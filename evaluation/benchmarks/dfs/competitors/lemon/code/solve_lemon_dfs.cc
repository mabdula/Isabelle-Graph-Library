/* Reference solver for the DFS study: LEMON's depth-first search.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .gr file                                   (clocked, reported)
 *   2. repack the arcs into StaticDigraph's input pairs     (clocked, reported)
 *   3. read the clock
 *   4. sort the arcs by tail, build the CSR digraph, call Dfs::run(s)
 *   5. read the clock again
 *   6. report the difference, plus the answer for checking
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
 * the CSR build, the algorithm's own setup and the search.  This is the same
 * rule the JGraphT driver follows with its sparse CSR graph.
 *
 * What stays outside is the file read (parse_ms) and repacking the parsed
 * arrays into the std::vector<std::pair<int,int>> that build() takes
 * (build_ms) -- marshalling into the library's input format, the counterpart
 * of the edge list the JGraphT driver fills.  Both are reported so that what
 * sits outside the measurement is visible rather than merely asserted.
 * dedup_ms is 0.000: StaticDigraph takes parallel arcs as they come.
 *
 * EVERY REPEAT REBUILDS THE GRAPH.  It has to: the build is part of what is
 * measured, so a repeat that reused the graph would be timing something else.
 *
 * IT SWEEPS EVERYTHING REACHABLE FROM THE SOURCE, AND NOTHING ELSE.  This
 * calls Dfs::run(s), the ONE-argument form, which runs the search until its
 * stack is empty.  Two other forms are deliberately NOT used:
 *
 *   run(s, t)  stops the moment t is reached.  Our exports are given a target
 *              the graph does not contain, so they never stop early, and a
 *              reference solver with a shortcut they do not have would make
 *              the comparison worthless.
 *   run()      with no argument sweeps EVERY component of the graph, picking
 *              a fresh unvisited root whenever the current one runs dry.
 *              That is strictly more work than our exports do, which would
 *              make this solver look worse than it is.
 *
 * run(s) is the one that matches: exactly the region reachable from the
 * source, exactly once.
 *
 * THE CROSS-CHECK IS THE NUMBER OF VERTICES VISITED.  The order the vertices
 * come out in is a property of the implementation -- LEMON's depth-first
 * order is not our export's -- but HOW MANY come out is a property of the
 * graph and the source alone.  So `visited' is the column the solvers are
 * checked against each other on, and here it is a count of Dfs::reached over
 * every node, taken AFTER the clock.
 *
 * WEIGHTS ARE PARSED AND THEN IGNORED.  The instances are the shortest-path
 * challenge's own, so that a DFS row, a BFS row and a Dijkstra row can be
 * read side by side on the same graph, but depth-first search has no use for
 * the third field of an arc line and no length map is ever built from it.
 *
 * ONE PROBLEM PER PROCESS.  The source is given on the command line and
 * exactly one is accepted: a search problem is a graph AND a source, so two
 * sources are two problems and must not share a solver call, a solver object,
 * or a process.  There is deliberately no way to hand this driver a list of
 * sources.
 *
 * THE TARGET MUST NOT BE A VERTEX.  It is carried on the command line only so
 * that every driver in the study takes the same arguments, and this one
 * refuses anything inside [1, n], exactly as the exports' drivers do.
 *
 * The algorithm's OWN setup is inside the clock here, as it is for ours:
 * Dfs::run calls init(), which allocates the predecessor, distance and
 * reached maps and clears them over every node.  A fresh Dfs object is
 * constructed for each repeat so that this allocation happens inside the
 * clock every time rather than once.  That matters: the search itself is a
 * single linear sweep, so clearing three maps over n nodes is a real share of
 * the work, and hiding it would flatter this solver against exports that
 * cannot hide theirs.
 */

#include <lemon/static_graph.h>
#include <lemon/dfs.h>

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
#include <utility>
#include <vector>

using namespace lemon;

typedef StaticDigraph Graph;

static void die(const char *msg) {
  std::fprintf(stderr, "%s\n", msg);
  std::exit(1);
}

static const char *HEADER =
  "instance,nodes,arcs,query,source,target,repeat,status,"
  "reached,visited,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms,"
  "parse_ms,dedup_ms,build_ms,clock_build_ms,clock_solve_ms,tag";

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
        "usage: solve_lemon_dfs [options] <instance.gr>\n"
        "  --source <v>       the source, a DIMACS node id (1-based)\n"
        "  --target <v>       must NOT be a node of the graph; the\n"
        "                     campaign passes 0\n"
        "  --query <id>       the id this source carries in queries.csv\n"
        "  --repeats <k>      search the SAME problem k times, one row each\n"
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

  /* ---- 2. repack the arcs into the pairs StaticDigraph::build takes ----
   * OUTSIDE THE CLOCK, reported in build_ms: this is marshalling into the
   * library's input format, not the building of its structure.  Node ids
   * 1..n become indices 0..n-1, in order, so that g.nodeFromId(id - 1) is the
   * node the file calls `id'.  File order is kept; the sort is in the clock. */
  double bu0, bs0, bu1, bs1;
  cpu_now(&bu0, &bs0);
  std::vector<std::pair<int, int> > arcs((size_t)e.m);
  for (int64_t i = 0; i < e.m; i++)
    arcs[(size_t)i] = std::make_pair((int)e.from[i] - 1, (int)e.to[i] - 1);
  cpu_now(&bu1, &bs1);
  double build_ms = (bu1 - bu0) + (bs1 - bs0);

  {
    if (src < 1 || src > e.n)
      die("the source is outside [1, n]");
    if (dst >= 1 && dst <= e.n)
      die("the target IS a node of this graph; this study searches the whole "
          "graph and needs a target outside [1, n]");

    for (int rep = 1; rep <= repeats; rep++) {
      /* ---- 3. clock ---- */
      double u0, s0, w0 = wall_now_ms();
      cpu_now(&u0, &s0);

      /* ---- 4. build the CSR digraph, then search it ----
       * A fresh graph and a fresh Dfs each time, so the build and the maps
       * are allocated inside the clock on every repeat.  run(s): the whole
       * region reachable from the source, no early exit and no restart in
       * another component.  See the note at the top. */
      Graph g;
      build_csr(g, (int)e.n, arcs, NULL);
      /* ---- the intermediate reading: the structure is built ---- */
      double um, sm;
      cpu_now(&um, &sm);
      Graph::Node s = g.nodeFromId((int)src - 1);
      Dfs<Graph> dfs(g);
      dfs.run(s);

      /* ---- 5. clock ---- */
      double u1, s1, w1 = wall_now_ms();
      cpu_now(&u1, &s1);

      double usr_ms = u1 - u0, sys_ms = s1 - s0;
      double cpu_ms = usr_ms + sys_ms, wall_ms = w1 - w0;
      /* the two parts of the clocked period; they add up to cpu_ms */
      double clock_build_ms = (um - u0) + (sm - s0);
      double clock_solve_ms = (u1 - um) + (s1 - sm);

      /* ---- 6. the answer, after the clock ----
       * How many vertices the sweep settled.  This is what the solvers are
       * cross-checked on; counting them is a pass over the node set and is
       * outside the measurement. */
      int64_t visited = 0;
      for (Graph::NodeIt v(g); v != INVALID; ++v)
        if (dfs.reached(v)) visited++;

      if (csv)
        std::printf("%s,%lld,%lld,%lld,%lld,%lld,%d,%s,%d,%lld,"
                    "%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%s\n",
                    base, (long long)e.n, (long long)e.m,
                    qid, src, dst, rep,
                    "OK", 0, (long long)visited,
                    cpu_ms, usr_ms, sys_ms, cpu_ms, wall_ms,
                    parse_ms, 0.0, build_ms,
                    clock_build_ms, clock_solve_ms, tag);
      else
        std::printf("query %lld  source %lld  rep %d\n"
                    "  status   OK\n  visited  %lld\n"
                    "  cpu      %.3f ms   (the measurement)\n"
                    "  wall     %.3f ms\n",
                    qid, src, rep, (long long)visited, cpu_ms, wall_ms);
      std::fflush(stdout);
    }
  }
  return 0;
}
