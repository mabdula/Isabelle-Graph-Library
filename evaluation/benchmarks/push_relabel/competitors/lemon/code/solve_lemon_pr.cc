/* Reference solver for the push-relabel study: LEMON's preflow push.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .max file                                  (clocked, reported)
 *   2. repack the arcs into StaticDigraph's input pairs     (clocked, reported)
 *   3. read the clock
 *   4. sort the arcs by tail, build the CSR digraph and its capacity map,
 *      construct Preflow and call run()
 *   5. read the clock again
 *   6. check the flow and read its value                    (after the clock)
 *
 * STEPS 3 TO 5 ARE THE MEASUREMENT, AND THE GRAPH BUILD IS INSIDE IT.  The
 * lemon_linked column measures LEMON on SmartDigraph, a linked arc-list
 * structure built outside the clock; that compares our CSR export against a
 * different layout rather than against LEMON's implementation of the same
 * algorithm on the same layout, which is StaticDigraph, LEMON's own CSR.
 * StaticDigraph cannot be built while the file is read: build() takes a COMPLETE arc list, sorted by tail, and
 * walks it once -- a separate pass over every arc, exactly as our exported
 * code makes.  Nothing fuses with parsing, so nothing is left outside.  The
 * clock therefore opens on the filled arc list and covers the sort by tail (a
 * counting sort, linear in n + m, keeping the file's order within each node),
 * the CSR build, the algorithm's own setup and the solve.  (The JGraphT push-relabel
 * driver copies the graph into its own arrays inside the clock, so its build
 * is inside the clock by construction.)
 *
 * What stays outside is the file read (parse_ms) and repacking the parsed
 * arrays into the std::vector<std::pair<int,int>> that build() takes
 * (build_ms) -- marshalling into the library's input format, the same step the
 * other LEMON drivers in these studies take.  Both are reported so that what
 * sits outside the measurement is visible rather than merely asserted.
 * dedup_ms is 0.000: StaticDigraph takes parallel arcs as they come.
 *
 * EVERY REPEAT REBUILDS THE GRAPH.  It has to: the build is part of what is
 * measured, so a repeat that reused the graph would be timing something else.
 *
 * The capacity map is a second per-arc pass inside the clock: build() gives
 * the arcs new ids in sorted order, so the capacities are laid over those
 * ids through the permutation the sort recorded.  A SmartDigraph took the
 * capacity as each arc was added; a CSR graph cannot, and neither can ours.
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

#include <lemon/static_graph.h>
#include <lemon/preflow.h>

#include <sys/resource.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <utility>
#include <vector>

using namespace lemon;

typedef StaticDigraph Graph;
typedef Graph::ArcMap<int64_t> CapMap;

static void die(const char *msg) {
  std::fprintf(stderr, "%s\n", msg);
  std::exit(1);
}

static const char *HEADER =
  "instance,nodes,arcs,variant,source,target,repeat,status,"
  "flow_value,cpu_ms,cpu_usr_ms,cpu_sys_ms,thread_ms,wall_ms,"
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

/* ---------- the CSR build ----------
 * INSIDE THE CLOCK.  StaticDigraph::build(n, first, last) takes pairs of
 * 0-based node indices and requires them "in a non-decreasing order with
 * respect to their first values" (static_graph.h): it walks the range node by
 * node and asserts that it was consumed.  Our instance files are never in
 * that order -- an eighth of the arcs of the synthetic families and a third
 * to a half of the road networks' and dense graphs' are out of order -- so
 * the arcs are sorted by tail first.  A counting sort, because that is what a
 * CSR build is: one count per node, one prefix sum, one scatter, linear in
 * n + m and stable, so the arcs of a node keep the order the file gave them
 * and so does the walk.  `perm', if asked for, records which input arc landed
 * where, so a per-arc map (lengths, capacities) can be laid over the built
 * graph's arc ids, which build() assigns 0, 1, 2, ... in the order it reads
 * the pairs. */
static void build_csr(Graph &g, int n,
                      const std::vector<std::pair<int, int> > &arcs,
                      std::vector<int> *perm) {
  const size_t m = arcs.size();
  std::vector<int> start((size_t)n + 1, 0);
  for (size_t i = 0; i < m; i++) start[(size_t)arcs[i].first + 1]++;
  for (int v = 0; v < n; v++) start[(size_t)v + 1] += start[(size_t)v];
  std::vector<std::pair<int, int> > sorted(m);
  if (perm) perm->resize(m);
  for (size_t i = 0; i < m; i++) {
    int pos = start[(size_t)arcs[i].first]++;
    sorted[(size_t)pos] = arcs[i];
    if (perm) (*perm)[(size_t)pos] = (int)i;
  }
  g.build(n, sorted.begin(), sorted.end());
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

  /* ---- 2. repack the arcs into the pairs StaticDigraph::build takes ----
   * OUTSIDE THE CLOCK, reported in build_ms: this is marshalling into the
   * library's input format, not the building of its structure.  Node ids
   * 1..n become indices 0..n-1, in order, so that g.nodeFromId(id - 1) is the
   * node the file calls `id'.  File order is kept; the sort is in the clock. */
  cpu_now(&u0, &s0);
  std::vector<std::pair<int, int> > arcs((size_t)e.m);
  for (int64_t i = 0; i < e.m; i++)
    arcs[(size_t)i] = std::make_pair((int)e.from[(size_t)i] - 1,
                                     (int)e.to[(size_t)i] - 1);
  cpu_now(&u1, &s1);
  double build_ms = (u1 - u0) + (s1 - s0);

  for (int rep = 1; rep <= repeats; rep++) {
    /* ---- 3. clock ---- */
    double w0 = wall_now_ms();
    cpu_now(&u0, &s0);

    /* ---- 4. build the CSR digraph and its capacity map, then the library,
     * whole: init() and both phases.  A fresh graph, capacity map and
     * Preflow each time, so all three are allocated inside the clock on
     * every repeat.  Arc i of the built graph is input arc perm[i]. ---- */
    Graph g;
    std::vector<int> perm;
    build_csr(g, (int)e.n, arcs, &perm);
    CapMap cap(g);
    for (int64_t i = 0; i < e.m; i++)
      cap[g.arcFromId((int)i)] = e.cap[(size_t)perm[(size_t)i]];
    Graph::Node S = g.nodeFromId((int)src - 1), T = g.nodeFromId((int)dst - 1);
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
      /* arc i of the graph is input arc j: check it against j's capacity */
      size_t j = (size_t)perm[(size_t)i];
      int64_t f = pf.flow(g.arcFromId((int)i));
      if (f < 0 || f > e.cap[j]) { status = "OVER_CAPACITY"; break; }
      net[(size_t)e.from[j]] -= f;
      net[(size_t)e.to[j]] += f;
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
