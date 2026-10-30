/*
  Reading a DIMACS assignment instance and writing the solution.

    p asn <nodes> <arcs>
    n <id>               a left node (one line per left node)
    a <l> <r> <cost>     an arc from a left node to a right node

  Nodes are 1..<nodes>; every node not declared by an n line is a right
  node. The parser is trusted: it establishes the input format the
  verified program assumes (Assignment_Solver.thy, locale asn_input):
  every id in range, the left nodes distinct, every arc from a left to
  a right node, no two arcs between the same pair of nodes. Anything
  else is rejected as malformed. The vertex count handed to the
  verified program is <nodes> + 1, so the vertices are the ids < it
  (0 is no node).
*/

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int64_t g_n, g_m, g_nl, g_nr;
static int64_t *g_fs, *g_ts, *g_ws, *g_ls, *g_rs;

static int fail(const char *msg, int64_t line) {
  if (line > 0) fprintf(stderr, "asn: line %lld: %s\n", (long long)line, msg);
  else fprintf(stderr, "asn: %s\n", msg);
  return 1;
}

static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : x > y;
}

/* 0 on success; otherwise a message is on stderr. */
int64_t asn_parse(const char *path) {
  FILE *f = fopen(path, "r");
  if (!f) return fail("cannot open input", 0);
  char line[256];
  int64_t lineno = 0, nodes = -1, arcs = -1, cnt_a = 0;
  char *is_left = NULL;
  while (fgets(line, sizeof line, f)) {
    lineno++;
    char *p = line;
    while (*p == ' ' || *p == '\t') p++;
    if (*p == 'c' || *p == '\n' || *p == '\r' || *p == 0) continue;
    if (*p == 'p') {
      long long a, b; char kind[8];
      if (nodes >= 0 || sscanf(p + 1, "%7s %lld %lld", kind, &a, &b) != 3 ||
          strcmp(kind, "asn") != 0 || a < 0 || b < 0)
        return fail("bad problem line", lineno);
      nodes = a; arcs = b;
      is_left = calloc((size_t)nodes + 2, 1);
      g_fs = malloc(((size_t)arcs + 1) * sizeof(int64_t));
      g_ts = malloc(((size_t)arcs + 1) * sizeof(int64_t));
      g_ws = malloc(((size_t)arcs + 1) * sizeof(int64_t));
      g_ls = malloc(((size_t)nodes + 1) * sizeof(int64_t));
      if (!is_left || !g_fs || !g_ts || !g_ws || !g_ls) return fail("out of memory", 0);
    } else if (*p == 'n') {
      long long v;
      if (nodes < 0) return fail("node line before problem line", lineno);
      if (cnt_a > 0) return fail("node line after arc lines", lineno);
      if (sscanf(p + 1, "%lld", &v) != 1 || v < 1 || v > nodes)
        return fail("bad node line", lineno);
      if (is_left[v]) return fail("left node declared twice", lineno);
      is_left[v] = 1; g_ls[g_nl++] = v;
    } else if (*p == 'a') {
      long long l, r, c;
      if (nodes < 0) return fail("arc line before problem line", lineno);
      if (sscanf(p + 1, "%lld %lld %lld", &l, &r, &c) != 3)
        return fail("bad arc line", lineno);
      if (l < 1 || l > nodes || r < 1 || r > nodes) return fail("node id out of range", lineno);
      if (!is_left[l] || is_left[r]) return fail("arc not from a left to a right node", lineno);
      if (cnt_a >= arcs) return fail("more arcs than declared", lineno);
      g_fs[cnt_a] = l; g_ts[cnt_a] = r; g_ws[cnt_a] = c; cnt_a++;
    } else return fail("unknown line type", lineno);
  }
  fclose(f);
  if (nodes < 0) return fail("no problem line", 0);
  if (cnt_a != arcs) return fail("fewer arcs than declared", 0);
  g_n = nodes + 1; g_m = arcs;

  /* no parallel arcs */
  uint64_t *key = malloc(((size_t)arcs + 1) * sizeof(uint64_t));
  if (!key) return fail("out of memory", 0);
  for (int64_t e = 0; e < arcs; e++)
    key[e] = (uint64_t)g_fs[e] * (uint64_t)(nodes + 1) + (uint64_t)g_ts[e];
  qsort(key, (size_t)arcs, sizeof(uint64_t), cmp_u64);
  for (int64_t e = 1; e < arcs; e++)
    if (key[e] == key[e - 1]) { free(key); return fail("parallel arcs", 0); }
  free(key);

  g_rs = malloc(((size_t)nodes + 1) * sizeof(int64_t));
  if (!g_rs) return fail("out of memory", 0);
  for (int64_t v = 1; v <= nodes; v++)
    if (!is_left[v]) g_rs[g_nr++] = v;
  free(is_left);
  return 0;
}

/* n (vertex bound), m, number of left and of right nodes */
void asn_sizes(int64_t *out) {
  out[0] = g_n; out[1] = g_m; out[2] = g_nl; out[3] = g_nr;
}

void asn_fill(int64_t *fs, int64_t *ts, int64_t *ws, int64_t *ls, int64_t *rs) {
  memcpy(fs, g_fs, (size_t)g_m * sizeof(int64_t));
  memcpy(ts, g_ts, (size_t)g_m * sizeof(int64_t));
  memcpy(ws, g_ws, (size_t)g_m * sizeof(int64_t));
  memcpy(ls, g_ls, (size_t)g_nl * sizeof(int64_t));
  memcpy(rs, g_rs, (size_t)g_nr * sizeof(int64_t));
  free(g_fs); free(g_ts); free(g_ws); free(g_ls); free(g_rs);
}

/*
  The solution: "s <cost>" and one "f <l> <r> 1" line per selected arc
  (the flow of the assignment as a min-cost flow), or "s infeasible".
  sel[e] != 0 marks arc e. 0 on success.
*/
int64_t asn_print(const char *path, const char *note, int64_t feasible, const char *cost,
                  int64_t m, const int64_t *fs, const int64_t *ts, const int64_t *sel) {
  FILE *f = fopen(path, "w");
  if (!f) return 1;
  static char buf[1 << 16];
  setvbuf(f, buf, _IOFBF, sizeof buf);
  fprintf(f, "c %s\n", note);
  if (!feasible) fprintf(f, "s infeasible\n");
  else {
    fprintf(f, "s %s\n", cost);
    for (int64_t e = 0; e < m; e++)
      if (sel[e]) fprintf(f, "f %lld %lld 1\n", (long long)fs[e], (long long)ts[e]);
  }
  return fclose(f) != 0;
}
