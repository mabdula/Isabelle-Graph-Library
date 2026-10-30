/* Reference solver for the Dijkstra study: LEMON's Dijkstra, default heap.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .gr file                                   (clocked, reported)
 *   2. build the LEMON digraph and its length map           (clocked, reported)
 *   3. read the clock
 *   4. call Dijkstra::run(s, t)
 *   5. read the clock again
 *   6. report the difference, plus the answer for checking
 *
 * Only step 4 sits between the two clock reads.  Steps 1 and 2 are outside it
 * because for an unverified library the structure build fuses with parsing --
 * a solver like this one would normally read the file straight into its own
 * graph.  That is not possible for verified exported code, which is handed
 * plain arrays and builds its own structures inside the entry point, so for
 * our export the build is inside the clock.  The asymmetry is inherent and
 * favours this reference solver.  Both are clocked and reported anyway, in
 * parse_ms and build_ms, so what sits outside the measurement is visible
 * rather than merely asserted.  dedup_ms is 0.000: LEMON is a multigraph and
 * takes parallel arcs as they come, where SciPy and NetworkX cannot.
 *
 * ONE PROBLEM PER PROCESS.  The source and the target are given on the command
 * line and exactly one of them is accepted: a shortest-path problem is a graph
 * AND a pair, so two pairs are two problems and must not share a solver call,
 * a solver object, or a process.  There is deliberately no way to hand this
 * driver a list of pairs.
 *
 * The algorithm's OWN setup is inside the clock here, as it is for ours:
 * Dijkstra::run calls init(), which allocates the distance, predecessor,
 * processed and heap-cross-reference maps and clears them over every node.
 * A fresh Dijkstra object is constructed for each repeat so that this
 * allocation happens inside the clock every time rather than once.
 *
 * LEMON's default heap for Dijkstra is BinHeap (dijkstra.h, DijkstraDefault-
 * Traits::Heap), which is the same structure the verified export uses: a
 * binary heap with decrease-key.  Same algorithm, same heap, hand-written C++
 * against generated verified code.
 */

#include <lemon/smart_graph.h>
#include <lemon/dijkstra.h>

#include <sys/resource.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>

using namespace lemon;

typedef SmartDigraph Graph;
typedef Graph::ArcMap<int64_t> LenMap;

static void die(const char *msg) {
  std::fprintf(stderr, "%s\n", msg);
  std::exit(1);
}

static const char *HEADER =
  "instance,nodes,arcs,query,source,target,repeat,status,"
  "reached,hops,dist,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms,"
  "parse_ms,dedup_ms,build_ms,tag";

/* ---------- clock ----------
 * CPU time (user + system) is the measurement, as everywhere else in this
 * study.  Wall time is recorded as well but nothing is derived from it: the
 * campaign runs several solvers at once, so wall time carries whatever the
 * other runs were doing and CPU time does not.
 *
 * `proc_ms' is the whole process rather than the one thread.  Here the two are
 * the same number, because getrusage is read on a process that is doing
 * nothing else; the column exists so that the Scala driver, where they differ
 * by the cost of the JIT, can be read against these without a second shape of
 * row. */

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

/* ---------- the DIMACS .gr file ----------
 * Byte level, a whole 4 MiB at a time.  Node ids are kept exactly as the file
 * writes them, 1..n; nothing is renumbered. */

struct Edges {
  int64_t n = 0, m = 0;
  std::vector<int32_t> from, to;
  std::vector<int64_t> w;
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

static Edges parse_gr(const char *path) {
  Reader in(path);
  Edges e;
  int c = in.get();
  int64_t arcs_seen = 0;

  while (c >= 0) {
    /* skip blank space at the start of a line */
    while (c == ' ' || c == '\t' || c == '\n' || c == '\r') c = in.get();
    if (c < 0) break;

    int kind = c;
    c = in.get();

    if (kind == 'c') {                      /* comment: drop the line */
      while (c >= 0 && c != '\n') c = in.get();
      continue;
    }

    /* the next fields are unsigned decimals separated by blanks, except the
     * weight, which the format allows to be signed */
    int64_t f[3] = {0, 0, 0};
    int nf = 0;
    bool want_tag = (kind == 'p');          /* `p sp <nodes> <arcs>' */
    while (c >= 0 && c != '\n' && nf < 3) {
      while (c == ' ' || c == '\t') c = in.get();
      if (c < 0 || c == '\n' || c == '\r') break;
      if (want_tag && !(c >= '0' && c <= '9') && c != '-') {
        while (c >= 0 && c != ' ' && c != '\t' && c != '\n') c = in.get();
        want_tag = false;
        continue;
      }
      bool neg = false;
      if (c == '-') { neg = true; c = in.get(); }
      if (!(c >= '0' && c <= '9')) break;
      int64_t v = 0;
      while (c >= '0' && c <= '9') { v = v * 10 + (c - '0'); c = in.get(); }
      f[nf++] = neg ? -v : v;
    }
    while (c >= 0 && c != '\n') c = in.get();
    if (c == '\n') c = in.get();

    if (kind == 'p') {
      if (nf < 2) die("bad `p' line");
      e.n = f[0]; e.m = f[1];
      e.from.reserve((size_t)e.m);
      e.to.reserve((size_t)e.m);
      e.w.reserve((size_t)e.m);
    } else if (kind == 'a') {
      if (nf < 3) die("bad `a' line");
      e.from.push_back((int32_t)f[0]);
      e.to.push_back((int32_t)f[1]);
      e.w.push_back(f[2]);
      arcs_seen++;
    }
    /* anything else (`t', stray tags) is ignored */
  }
  if (e.n == 0) die("no `p sp' line in the instance");
  e.m = arcs_seen;
  return e;
}

int main(int argc, char **argv) {
  const char *path = NULL, *tag = "";
  long long src = -1, dst = -1, qid = 0;
  int repeats = 1, csv = 1;

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (!std::strcmp(a, "--header")) { std::printf("%s\n", HEADER); return 0; }
    else if (!std::strcmp(a, "--csv")) csv = 1;
    else if (!std::strcmp(a, "--human")) csv = 0;
    else if (!std::strcmp(a, "--source") && i + 1 < argc) src = std::atoll(argv[++i]);
    else if (!std::strcmp(a, "--target") && i + 1 < argc) dst = std::atoll(argv[++i]);
    else if (!std::strcmp(a, "--query") && i + 1 < argc) qid = std::atoll(argv[++i]);
    else if (!std::strcmp(a, "--tag") && i + 1 < argc) tag = argv[++i];
    else if (!std::strcmp(a, "--repeats") && i + 1 < argc) {
      repeats = std::atoi(argv[++i]);
      if (repeats < 1) die("--repeats must be at least 1");
    } else if (a[0] == '-' && a[1] == '-') {
      std::fprintf(stderr,
        "usage: solve_lemon [options] <instance.gr>\n"
        "  --source <v>       the source, a DIMACS node id (1-based)\n"
        "  --target <v>       the target, a DIMACS node id (1-based)\n"
        "  --query <id>       the id this pair carries in queries.csv\n"
        "  --repeats <k>      solve the SAME problem k times, one row each\n"
        "  --header           print the CSV header line and exit\n"
        "  --csv / --human    output shape (default --csv)\n"
        "  --tag <s>          label copied into the `tag' column\n");
      return 1;
    } else path = a;
  }
  if (!path) die("an instance is required");
  if (src < 0) die("a --source is required");
  if (dst < 0) die("a --target is required");

  /* ---- 1. parse ---- */
  double pu0, ps0, pu1, ps1;
  cpu_now(&pu0, &ps0);
  Edges e = parse_gr(path);
  cpu_now(&pu1, &ps1);
  double parse_ms = (pu1 - pu0) + (ps1 - ps0);

  const char *base = std::strrchr(path, '/');
  base = base ? base + 1 : path;

  /* ---- 2. build the digraph ----
   * Node ids 1..n map to node indices 0..n-1, in order, so that
   * g.nodeFromId(id - 1) is the node the file calls `id'. */
  double bu0, bs0, bu1, bs1;
  cpu_now(&bu0, &bs0);
  Graph g;
  g.reserveNode((int)e.n);
  g.reserveArc((int)e.m);
  for (int64_t i = 0; i < e.n; i++) g.addNode();
  LenMap len(g);
  for (int64_t i = 0; i < e.m; i++) {
    Graph::Arc a = g.addArc(g.nodeFromId((int)e.from[i] - 1),
                            g.nodeFromId((int)e.to[i] - 1));
    len[a] = e.w[i];
  }
  cpu_now(&bu1, &bs1);
  double build_ms = (bu1 - bu0) + (bs1 - bs0);

  {
    if (src < 1 || src > e.n || dst < 1 || dst > e.n) die("query out of range");
    Graph::Node s = g.nodeFromId((int)src - 1);
    Graph::Node t = g.nodeFromId((int)dst - 1);

    for (int rep = 1; rep <= repeats; rep++) {
      /* a fresh object each time, so its maps are allocated inside the clock */
      Dijkstra<Graph, LenMap> dij(g, len);

      /* ---- 3. clock ---- */
      double u0, s0, w0 = wall_now_ms();
      cpu_now(&u0, &s0);

      /* ---- 4. solve ---- */
      bool reached = dij.run(s, t);

      /* ---- 5. clock ---- */
      double u1, s1, w1 = wall_now_ms();
      cpu_now(&u1, &s1);

      double usr_ms = u1 - u0, sys_ms = s1 - s0;
      double cpu_ms = usr_ms + sys_ms, wall_ms = w1 - w0;

      /* ---- 6. the answer, after the clock ---- */
      const char *status = "UNREACHABLE";
      int64_t hops = 0, dist = -1;
      if (reached) {
        dist = dij.dist(t);
        status = "OPTIMAL";
        Graph::Node v = t;
        while (v != s) {
          Graph::Arc a = dij.predArc(v);
          if (a == INVALID) { status = "BAD_PATH"; hops = 0; break; }
          v = g.source(a);
          hops++;
        }
      }

      if (csv)
        std::printf("%s,%lld,%lld,%lld,%lld,%lld,%d,%s,%d,%lld,%lld,"
                    "%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%s\n",
                    base, (long long)e.n, (long long)e.m,
                    qid, src, dst, rep,
                    status, reached ? 1 : 0, (long long)hops, (long long)dist,
                    cpu_ms, usr_ms, sys_ms, cpu_ms, wall_ms,
                    parse_ms, 0.0, build_ms, tag);
      else
        std::printf("query %lld  %lld -> %lld  rep %d\n"
                    "  status   %s\n  hops     %lld\n  dist     %lld\n"
                    "  cpu      %.3f ms   (the measurement)\n"
                    "  wall     %.3f ms\n",
                    qid, src, dst, rep,
                    status, (long long)hops, (long long)dist, cpu_ms, wall_ms);
      std::fflush(stdout);
    }
  }
  return 0;
}
