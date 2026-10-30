/* Reference solver for the Kruskal study: LEMON's kruskal().
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .gr file                                   (clocked, reported)
 *   2. collapse parallel edges to the cheapest              (clocked, reported)
 *   3. fill a SmartGraph and its cost map from the edges    (clocked, reported)
 *   4. read the clock
 *   5. kruskal(g, cost, tree)
 *   6. read the clock again
 *   7. report the difference, plus the tree for checking
 *
 * STEPS 4 TO 6 ARE THE MEASUREMENT.  The graph is built OUTSIDE it, and that
 * is the rule of these studies applied, not an exception to it: a structure
 * that can be filled while the file is read may be built outside the clock;
 * one that needs the complete arc list first is built after parsing and that
 * build is the first part of the measured period.  Kruskal's algorithm needs
 * no adjacency structure at all -- it reads the edges, sorts them by cost and
 * joins endpoints in a union-find forest -- so the most suitable LEMON graph
 * for it is the one that is cheapest to fill and cheapest to read edges off:
 * SmartGraph, an array of edges with their endpoints, grown one addEdge at a
 * time exactly as the file is read.  (StaticGraph, LEMON's CSR for undirected
 * graphs, would need a complete sorted edge list and an adjacency index that
 * kruskal() never touches.)  Here the graph is filled from the parsed arrays
 * rather than from the file directly, which is the same work in the same
 * place, and the time it takes is reported in build_ms.
 *
 * What IS inside the clock is everything kruskal() does: it walks the edges
 * into a vector of (edge, cost) pairs, sorts that vector by cost with
 * std::sort, initialises a UnionFind over the nodes, and runs the Kruskal
 * loop, setting the output map.  The output map is constructed inside the
 * clock too; it is the algorithm's own output structure, as the exports'
 * result lists are.  A fresh map on every repeat.
 *
 * EVERY ARC IS AN UNDIRECTED EDGE, AND PARALLEL EDGES ARE COLLAPSED:
 * the parser keeps the cheapest
 * edge of every unordered pair (collapse() below), so the solver is handed
 * a simple graph.  Parsing work, outside the clock, reported in dedup_ms;
 * the `edges' column is the count after it, `arcs' the file's.  Every
 * driver in the study does the same.
 *
 * THE ANSWER IS CHECKED AFTER THE CLOCK with the driver's own union-find: no
 * tree edge may close a cycle, and the count must be n minus the number of
 * connected components of the whole graph.  The tree's weight -- kruskal()'s
 * return value, re-summed here from the map -- is reported for the cross-check
 * between solvers.
 */

#include <lemon/smart_graph.h>
#include <lemon/kruskal.h>

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

typedef SmartGraph Graph;

static void die(const char *msg) {
  std::fprintf(stderr, "%s\n", msg);
  std::exit(1);
}

static const char *HEADER =
  "instance,nodes,arcs,edges,repeat,status,tree_edges,tree_weight,"
  "cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms,"
  "parse_ms,dedup_ms,build_ms,tag";

/* ---------- clock ----------
 * CPU time (user + system) is the measurement, as everywhere else in this
 * study.  Wall time is recorded as well but nothing is derived from it. */

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
    while (c == ' ' || c == '\t' || c == '\n' || c == '\r') c = in.get();
    if (c < 0) break;

    int kind = c;
    c = in.get();

    if (kind == 'c') {
      while (c >= 0 && c != '\n') c = in.get();
      continue;
    }

    int64_t f[3] = {0, 0, 0};
    int nf = 0;
    bool want_tag = (kind == 'p');
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
  }
  if (e.n == 0) die("no `p sp' line in the instance");
  e.m = arcs_seen;
  return e;
}

/* ---------- collapse parallel edges ----------
 * Keep the cheapest arc of every unordered pair {u, v}.  Two stable counting
 * sorts of the edge indices, by the larger endpoint and then by the smaller,
 * put equal pairs side by side in (lo, hi) order; one scan keeps the minimum
 * weight of each run.  Linear in n + m.  The result lists each edge once as
 * (lo, hi, w), sorted by (lo, hi); self-loops, if any, stay. */
static Edges collapse(const Edges &e) {
  const size_t m = (size_t)e.m, n = (size_t)e.n;
  std::vector<int32_t> lo(m), hi(m);
  for (size_t i = 0; i < m; i++) {
    int32_t u = e.from[i], v = e.to[i];
    if (u <= v) { lo[i] = u; hi[i] = v; } else { lo[i] = v; hi[i] = u; }
  }
  std::vector<int32_t> a(m), b(m), cnt(n + 2);
  for (size_t i = 0; i < m; i++) a[i] = (int32_t)i;
  /* by hi, then stably by lo */
  const std::vector<int32_t> *keys[2] = { &hi, &lo };
  std::vector<int32_t> *src = &a, *dst = &b;
  for (int pass = 0; pass < 2; pass++) {
    const std::vector<int32_t> &key = *keys[pass];
    std::fill(cnt.begin(), cnt.end(), 0);
    for (size_t i = 0; i < m; i++) cnt[(size_t)key[(size_t)(*src)[i]] + 1]++;
    for (size_t k = 1; k <= n + 1; k++) cnt[k] += cnt[k - 1];
    for (size_t i = 0; i < m; i++) {
      int32_t id = (*src)[i];
      (*dst)[(size_t)cnt[(size_t)key[(size_t)id]]++] = id;
    }
    std::swap(src, dst);
  }
  Edges r;
  r.n = e.n;
  r.from.reserve(m); r.to.reserve(m); r.w.reserve(m);
  for (size_t k = 0; k < m; k++) {
    int32_t i = (*src)[k];
    if (!r.from.empty() && r.from.back() == lo[(size_t)i] && r.to.back() == hi[(size_t)i]) {
      if (e.w[(size_t)i] < r.w.back()) r.w.back() = e.w[(size_t)i];
    } else {
      r.from.push_back(lo[(size_t)i]); r.to.push_back(hi[(size_t)i]); r.w.push_back(e.w[(size_t)i]);
    }
  }
  r.m = (int64_t)r.from.size();
  return r;
}

/* ---------- the check, after the clock: the driver's own union-find ---------- */

static int32_t uf_find(std::vector<int32_t> &p, int32_t i) {
  while (p[(size_t)i] != i) { p[(size_t)i] = p[(size_t)p[(size_t)i]]; i = p[(size_t)i]; }
  return i;
}

static int64_t components(const Edges &e) {
  std::vector<int32_t> p((size_t)e.n + 1);
  for (int64_t i = 0; i <= e.n; i++) p[(size_t)i] = (int32_t)i;
  int64_t c = e.n;
  for (int64_t i = 0; i < e.m; i++) {
    int32_t ru = uf_find(p, e.from[(size_t)i]), rv = uf_find(p, e.to[(size_t)i]);
    if (ru != rv) { p[(size_t)ru] = rv; c--; }
  }
  return c;
}

int main(int argc, char **argv) {
  const char *path = NULL, *tag = "";
  int repeats = 1, csv = 1;

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (!std::strcmp(a, "--header")) { std::printf("%s\n", HEADER); return 0; }
    else if (!std::strcmp(a, "--csv")) csv = 1;
    else if (!std::strcmp(a, "--human")) csv = 0;
    else if (!std::strcmp(a, "--tag") && i + 1 < argc) tag = argv[++i];
    else if (!std::strcmp(a, "--repeats") && i + 1 < argc) {
      repeats = std::atoi(argv[++i]);
      if (repeats < 1) die("--repeats must be at least 1");
    } else if (a[0] == '-' && a[1] == '-') {
      std::fprintf(stderr,
        "usage: solve_lemon_kruskal [options] <instance.gr>\n"
        "  --repeats <k>      solve the SAME instance k times, one row each\n"
        "  --header           print the CSV header line and exit\n"
        "  --csv / --human    output shape (default --csv)\n"
        "  --tag <s>          label copied into the `tag' column\n");
      return 1;
    } else path = a;
  }
  if (!path) die("an instance is required");

  /* ---- 1. parse ---- */
  double pu0, ps0, pu1, ps1;
  cpu_now(&pu0, &ps0);
  Edges raw = parse_gr(path);
  cpu_now(&pu1, &ps1);
  double parse_ms = (pu1 - pu0) + (ps1 - ps0);
  const int64_t raw_arcs = raw.m;

  /* ---- 2. collapse parallel edges: parsing work, outside, reported ---- */
  double du0, ds0, du1, ds1;
  cpu_now(&du0, &ds0);
  Edges e = collapse(raw);
  cpu_now(&du1, &ds1);
  double dedup_ms = (du1 - du0) + (ds1 - ds0);
  Edges().from.swap(raw.from); Edges().to.swap(raw.to); Edges().w.swap(raw.w);

  const char *base = std::strrchr(path, '/');
  base = base ? base + 1 : path;

  /* ---- 3. the library's graph, filled edge by edge ----
   * OUTSIDE THE CLOCK, reported in build_ms: see the note at the top.  Node
   * ids 1..n become indices 0..n-1, in order, so that g.nodeFromId(id - 1)
   * is the node the file calls `id'.  Edge ids are 0..m-1 in file order. */
  double bu0, bs0, bu1, bs1;
  cpu_now(&bu0, &bs0);
  Graph g;
  Graph::EdgeMap<int64_t> cost(g);
  g.reserveNode((int)e.n);
  g.reserveEdge((int)e.m);
  for (int64_t i = 0; i < e.n; i++) g.addNode();
  for (int64_t i = 0; i < e.m; i++) {
    Graph::Edge ed = g.addEdge(g.nodeFromId((int)e.from[(size_t)i] - 1),
                               g.nodeFromId((int)e.to[(size_t)i] - 1));
    cost[ed] = e.w[(size_t)i];
  }
  cpu_now(&bu1, &bs1);
  double build_ms = (bu1 - bu0) + (bs1 - bs0);

  int64_t comps = components(e);

  for (int rep = 1; rep <= repeats; rep++) {
    /* ---- 4. clock ---- */
    double u0, s0, w0 = wall_now_ms();
    cpu_now(&u0, &s0);

    /* ---- 5. Kruskal: collect, sort, union-find, into a fresh output map ---- */
    Graph::EdgeMap<bool> tree(g);
    int64_t total = kruskal(g, cost, tree);

    /* ---- 6. clock ---- */
    double u1, s1, w1 = wall_now_ms();
    cpu_now(&u1, &s1);

    double usr_ms = u1 - u0, sys_ms = s1 - s0;
    double cpu_ms = usr_ms + sys_ms, wall_ms = w1 - w0;

    /* ---- 7. the answer, after the clock ---- */
    std::vector<int32_t> p((size_t)e.n + 1);
    for (int64_t i = 0; i <= e.n; i++) p[(size_t)i] = (int32_t)i;
    int64_t cnt = 0, weight = 0;
    bool ok = true;
    for (Graph::EdgeIt it(g); it != INVALID; ++it) {
      if (!tree[it]) continue;
      cnt++;
      int32_t a = (int32_t)g.id(g.u(it)) + 1, b = (int32_t)g.id(g.v(it)) + 1;
      int32_t ra = uf_find(p, a), rb = uf_find(p, b);
      if (ra == rb) ok = false;
      else { p[(size_t)ra] = rb; weight += cost[it]; }
    }
    if (weight != total) ok = false;
    const char *status = (ok && cnt == e.n - comps) ? "SOLVED" : "BAD_TREE";

    if (csv)
      std::printf("%s,%lld,%lld,%lld,%d,%s,%lld,%lld,"
                  "%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%s\n",
                  base, (long long)e.n, (long long)raw_arcs, (long long)e.m, rep, status,
                  (long long)cnt, (long long)weight,
                  cpu_ms, usr_ms, sys_ms, cpu_ms, wall_ms,
                  parse_ms, dedup_ms, build_ms, tag);
    else
      std::printf("%s  rep %d\n  status      %s\n  tree edges  %lld  (n - components = %lld)\n"
                  "  tree weight %lld\n  edges       %lld  (%lld arcs in the file)\n"
                  "  cpu         %.3f ms   (the measurement)\n"
                  "  wall        %.3f ms\n  build       %.3f ms   (SmartGraph, outside)\n",
                  base, rep, status, (long long)cnt, (long long)(e.n - comps),
                  (long long)weight, (long long)e.m, (long long)raw_arcs,
                  cpu_ms, wall_ms, build_ms);
    std::fflush(stdout);
  }
  return 0;
}
