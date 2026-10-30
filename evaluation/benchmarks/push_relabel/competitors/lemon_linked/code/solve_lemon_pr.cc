/* Reference solver for the push-relabel study: LEMON's preflow push.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .max file                                  (clocked, reported)
 *   2. build the LEMON digraph and capacity map             (clocked, reported)
 *   3. read the clock
 *   4. construct Preflow and call run()
 *   5. read the clock again
 *   6. check the flow and read its value                    (after the clock)
 *
 * Only step 4 sits between the two clock reads.  Steps 1 and 2 are outside it
 * because for an unverified library the structure build fuses with parsing --
 * a solver like this one would normally read the file straight into its own
 * graph.  That is not possible for verified exported code, which is handed
 * plain arrays and builds its own structures inside the entry point, so for
 * our export the build is inside the clock.  The asymmetry is inherent and
 * favours this reference solver.  Both are clocked and reported anyway, in
 * parse_ms and build_ms, so what sits outside the measurement is visible
 * rather than merely asserted.  dedup_ms is 0.000: SmartDigraph is a
 * multigraph and takes parallel arcs as they come, exactly as our export does.
 *
 * run(), NOT runMinCut().  LEMON's Preflow offers both.  run() is init()
 * followed by startFirstPhase() and startSecondPhase(), and it ends with a
 * maximum flow.  runMinCut() stops after the first phase, with a maximum
 * PREFLOW -- enough for the cut and for the value, but not a flow.  Our
 * export has no such shortcut: both its variants discharge until no vertex
 * carries excess, which is a flow already.  Handing this solver the cheaper
 * call would make the comparison worthless, so it gets the full one.
 *
 * The algorithm's OWN setup is inside the clock here, as it is for ours: a
 * fresh Preflow object is constructed for each repeat, and run() calls init(),
 * which allocates the flow map, the excess map, the level structure and the
 * bucket lists and sweeps them over every node and arc before any flow moves.
 * Hiding that would flatter this solver against exports that cannot hide it.
 *
 * THE VALUE IS READ AFTER THE CLOCK.  flowValue() is a cross-reference between
 * the thirteen solvers and nothing more; the measurement is the flow
 * computation alone, with no summing up inside it.  The value is also checked
 * against the arc flows the solver reports -- capacities respected and every
 * vertex but the two ends balanced -- which is what tells a maximum flow apart
 * from a maximum preflow.
 *
 * ONE PROBLEM PER PROCESS.  The source and the sink come from the file's own
 * `n' designator lines unless given on the command line, and there is
 * deliberately no way to hand this driver a second pair.
 */

#include <lemon/smart_graph.h>
#include <lemon/preflow.h>

#include <sys/resource.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>

using namespace lemon;

typedef SmartDigraph Graph;
typedef Graph::ArcMap<int64_t> CapMap;

static void die(const char *msg) {
  std::fprintf(stderr, "%s\n", msg);
  std::exit(1);
}

static const char *HEADER =
  "instance,nodes,arcs,variant,source,target,repeat,status,"
  "flow_value,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms,"
  "parse_ms,dedup_ms,build_ms,tag";

/* ---------- clock ----------
 * CPU time (user + system) is the measurement, as everywhere else in this
 * study.  Wall time is recorded as well but nothing is derived from it: the
 * campaign runs several solvers at once, so wall time carries whatever the
 * other runs were doing and CPU time does not. */

static void cpu_now(double *usr_ms, double *sys_ms) {
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  *usr_ms = ru.ru_utime.tv_sec * 1000.0 + ru.ru_utime.tv_usec / 1000.0;
  *sys_ms = ru.ru_stime.tv_sec * 1000.0 + ru.ru_stime.tv_usec / 1000.0;
}

static double wall_now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1000.0 + ts.tv_nsec / 1000000.0;
}

/* ---------- the DIMACS .max file ----------
 * Byte level, a whole 4 MiB at a time.  Node ids are kept exactly as the file
 * writes them, 1..n; nothing is renumbered. */

struct Edges {
  int64_t n = 0, m = 0, s = -1, t = -1;
  std::vector<int32_t> from, to;
  std::vector<int64_t> cap;
};

namespace {

struct Reader {
  int fd;
  std::vector<char> buf;
  size_t len = 0, pos = 0;
  bool eof = false;

  explicit Reader(const char *path) : buf(4u << 20) {
    fd = open(path, O_RDONLY);
    if (fd < 0) { std::perror(path); std::exit(1); }
  }
  ~Reader() { close(fd); }

  int get() {
    if (pos == len) {
      if (eof) return -1;
      ssize_t r = read(fd, buf.data(), buf.size());
      if (r <= 0) { eof = true; return -1; }
      len = (size_t)r; pos = 0;
    }
    return (unsigned char)buf[pos++];
  }
};

}  // namespace

static Edges parse_max(const char *path) {
  Reader in(path);
  Edges e;
  int c = in.get();
  int64_t arcs_seen = 0;

  while (c >= 0) {
    while (c == ' ' || c == '\t' || c == '\n' || c == '\r') c = in.get();
    if (c < 0) break;

    int kind = c;
    c = in.get();

    if (kind == 'c') {                      /* comment: drop the line */
      while (c >= 0 && c != '\n') c = in.get();
      continue;
    }

    if (kind == 'n') {                      /* `n <id> s' or `n <id> t' */
      while (c == ' ' || c == '\t') c = in.get();
      int64_t v = 0;
      while (c >= '0' && c <= '9') { v = v * 10 + (c - '0'); c = in.get(); }
      while (c == ' ' || c == '\t') c = in.get();
      if (c == 's') e.s = v;
      else if (c == 't') e.t = v;
      else die("node line is neither s nor t");
      while (c >= 0 && c != '\n') c = in.get();
      if (c == '\n') c = in.get();
      continue;
    }

    int64_t f[3] = {0, 0, 0};
    int nf = 0;
    bool want_tag = (kind == 'p');          /* `p max <nodes> <arcs>' */
    while (c >= 0 && c != '\n' && nf < 3) {
      while (c == ' ' || c == '\t') c = in.get();
      if (c < 0 || c == '\n' || c == '\r') break;
      if (want_tag && !(c >= '0' && c <= '9')) {
        while (c >= 0 && c != ' ' && c != '\t' && c != '\n') c = in.get();
        want_tag = false;
        continue;
      }
      if (!(c >= '0' && c <= '9')) break;
      int64_t v = 0;
      while (c >= '0' && c <= '9') { v = v * 10 + (c - '0'); c = in.get(); }
      f[nf++] = v;
    }
    while (c >= 0 && c != '\n') c = in.get();
    if (c == '\n') c = in.get();

    if (kind == 'p') {
      if (nf < 2) die("bad `p' line");
      e.n = f[0]; e.m = f[1];
      e.from.reserve((size_t)e.m);
      e.to.reserve((size_t)e.m);
      e.cap.reserve((size_t)e.m);
    } else if (kind == 'a') {
      if (nf < 3) die("bad `a' line");
      e.from.push_back((int32_t)f[0]);
      e.to.push_back((int32_t)f[1]);
      e.cap.push_back(f[2]);
      arcs_seen++;
    }
  }
  if (e.n == 0) die("no `p max' line in the instance");
  if (e.s < 1 || e.t < 1) die("no source or no sink line");
  e.m = arcs_seen;
  return e;
}

int main(int argc, char **argv) {
  const char *path = NULL, *tag = "";
  long long src = -1, dst = -1;
  int repeats = 1, csv = 1;

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (!std::strcmp(a, "--header")) { std::printf("%s\n", HEADER); return 0; }
    else if (!std::strcmp(a, "--csv")) csv = 1;
    else if (!std::strcmp(a, "--human")) csv = 0;
    else if (!std::strcmp(a, "--source") && i + 1 < argc) src = std::atoll(argv[++i]);
    else if (!std::strcmp(a, "--target") && i + 1 < argc) dst = std::atoll(argv[++i]);
    else if (!std::strcmp(a, "--tag") && i + 1 < argc) tag = argv[++i];
    else if (!std::strcmp(a, "--repeats") && i + 1 < argc) {
      repeats = std::atoi(argv[++i]);
      if (repeats < 1) die("--repeats must be at least 1");
    } else if (a[0] == '-' && a[1] == '-') {
      std::fprintf(stderr,
        "usage: solve_lemon_pr [options] <instance.max>\n"
        "  --source <v>       the source, a DIMACS node id (1-based).\n"
        "                     Defaults to the file's own `n <id> s' line.\n"
        "  --target <v>       the sink, likewise, from `n <id> t'\n"
        "  --repeats <k>      solve the SAME problem k times (default 1)\n"
        "  --header           print the CSV header line and exit\n"
        "  --csv              print one CSV row per repeat (default)\n"
        "  --human            print a human-readable block instead\n"
        "  --tag <s>          free-form label copied into the `tag' column\n");
      return 1;
    } else path = a;
  }
  if (!path) die("an instance is required");

  const char *base = std::strrchr(path, '/');
  base = base ? base + 1 : path;

  /* ---- 1. parse ---- */
  double u0, s0, u1, s1;
  cpu_now(&u0, &s0);
  Edges e = parse_max(path);
  cpu_now(&u1, &s1);
  double parse_ms = (u1 - u0) + (s1 - s0);

  if (src < 0) src = e.s;
  if (dst < 0) dst = e.t;
  if (src < 1 || src > e.n || dst < 1 || dst > e.n) die("source or sink out of range");
  if (src == dst) die("source and sink are the same vertex");

  /* ---- 2. build ---- */
  cpu_now(&u0, &s0);
  Graph g;
  std::vector<Graph::Node> node((size_t)e.n + 1);
  for (int64_t v = 1; v <= e.n; v++) node[(size_t)v] = g.addNode();
  CapMap cap(g);
  std::vector<Graph::Arc> arc((size_t)e.m);
  for (int64_t i = 0; i < e.m; i++) {
    Graph::Arc a = g.addArc(node[(size_t)e.from[(size_t)i]],
                            node[(size_t)e.to[(size_t)i]]);
    cap[a] = e.cap[(size_t)i];
    arc[(size_t)i] = a;
  }
  cpu_now(&u1, &s1);
  double build_ms = (u1 - u0) + (s1 - s0);

  Graph::Node S = node[(size_t)src], T = node[(size_t)dst];

  for (int rep = 1; rep <= repeats; rep++) {
    /* ---- 3. clock ---- */
    double w0 = wall_now_ms();
    cpu_now(&u0, &s0);

    /* ---- 4. the library, whole: init() and both phases ---- */
    Preflow<Graph, CapMap> pf(g, cap, S, T);
    pf.run();

    /* ---- 5. clock ---- */
    cpu_now(&u1, &s1);
    double w1 = wall_now_ms();

    double usr_ms = u1 - u0, sys_ms = s1 - s0;
    double cpu_ms = usr_ms + sys_ms, wall_ms = w1 - w0;

    /* ---- 6. the answer, after the clock ---- */
    int64_t value = pf.flowValue();
    std::vector<int64_t> net((size_t)e.n + 1, 0);
    const char *status = "OK";
    for (int64_t i = 0; i < e.m; i++) {
      int64_t f = pf.flow(arc[(size_t)i]);
      if (f < 0 || f > e.cap[(size_t)i]) { status = "OVER_CAPACITY"; break; }
      net[(size_t)e.from[(size_t)i]] -= f;
      net[(size_t)e.to[(size_t)i]] += f;
    }
    if (!std::strcmp(status, "OK")) {
      for (int64_t v = 1; v <= e.n; v++)
        if (v != src && v != dst && net[(size_t)v] != 0) { status = "NOT_A_FLOW"; break; }
    }
    if (!std::strcmp(status, "OK") && -net[(size_t)src] != value)
      status = "VALUE_MISMATCH";

    if (csv)
      std::printf("%s,%lld,%lld,lemon_preflow,%lld,%lld,%d,%s,%lld,"
                  "%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%s\n",
                  base, (long long)e.n, (long long)e.m,
                  (long long)src, (long long)dst, rep, status,
                  (long long)value, cpu_ms, usr_ms, sys_ms, cpu_ms, wall_ms,
                  parse_ms, 0.0, build_ms, tag);
    else
      std::printf("instance %s  %lld nodes, %lld arcs\n"
                  "variant  lemon_preflow   %lld -> %lld   rep %d\n"
                  "flow     %lld  (%s)\n"
                  "cpu      %.3f ms   wall %.3f ms   parse %.3f ms   build %.3f ms\n",
                  base, (long long)e.n, (long long)e.m,
                  (long long)src, (long long)dst, rep,
                  (long long)value, status, cpu_ms, wall_ms, parse_ms, build_ms);
  }
  return 0;
}
