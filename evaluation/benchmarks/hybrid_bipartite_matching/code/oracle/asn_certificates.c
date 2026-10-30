/*
  The untrusted oracle of the certifying assignment solver: CSA computes
  the assignment, and the certificate generators below turn its result
  into a certificate in the format of the verified checker
  (Hungarian_Method/Refinements/Matching_Certificate_Arrays.thy):

    * an optimal perfect matching: the edge ids of the matching and an
      integer dual ys (one entry per vertex) with
        ys[l] + ys[r] <= w(e)  for every edge e = (l, r),
        ys[l] + ys[r]  = w(e)  for every matching edge;
    * no perfect matching: a set S of left vertices with |N(S)| < |S|
      (S = {} if the sides differ in size).

  Nothing here is trusted. Whatever is produced goes through the
  verified checker, and if the checker rejects it, the verified
  Hungarian method solves the instance from scratch.

  Vertices are the ids the caller uses (< n). Edge e runs from the left
  vertex fs[e] to the right vertex ts[e] and has weight ws[e].
*/

#include <stdint.h>
#include <stdlib.h>
#include <math.h>

#define ASN_UNKNOWN 0
#define ASN_OPT     1
#define ASN_INFEAS  2

/* The phase clock of the timing build (driver/asn_clock.c). */
#ifdef ASN_TIMING
extern void asn_stamp(int64_t k);
#define ASN_STAMP(k) asn_stamp(k)
#else
#define ASN_STAMP(k) ((void)0)
#endif

/* CSA as a library (oracle/csa, built with -DCSA_LIBRARY). */
extern int csa_solve_arrays(unsigned nl, unsigned nr, unsigned arcs,
                            const long *tl, const long *hd, const long *cs);
extern long csa_lhs_match(unsigned i);
extern double csa_rhs_price(unsigned j);
extern void csa_release(void);

/* The edges by left index, built once. */
typedef struct {
  int64_t nl, nr;
  int64_t *off;   /* nl + 1 */
  int64_t *head;  /* right index */
  int64_t *cost;
  int64_t *eid;
} adj_t;

static void adj_free(adj_t *g) {
  free(g->off); free(g->head); free(g->cost); free(g->eid);
}

static int adj_build(adj_t *g, int64_t m, const int64_t *li, const int64_t *ri,
                     const int64_t *ws) {
  g->off = calloc((size_t)g->nl + 1, sizeof(int64_t));
  g->head = malloc(((size_t)m + 1) * sizeof(int64_t));
  g->cost = malloc(((size_t)m + 1) * sizeof(int64_t));
  g->eid = malloc(((size_t)m + 1) * sizeof(int64_t));
  if (!g->off || !g->head || !g->cost || !g->eid) return 0;
  for (int64_t e = 0; e < m; e++) g->off[li[e] + 1]++;
  for (int64_t i = 0; i < g->nl; i++) g->off[i + 1] += g->off[i];
  int64_t *pos = malloc(((size_t)g->nl + 1) * sizeof(int64_t));
  if (!pos) return 0;
  for (int64_t i = 0; i <= g->nl; i++) pos[i] = g->off[i];
  for (int64_t e = 0; e < m; e++) {
    int64_t k = pos[li[e]]++;
    g->head[k] = ri[e]; g->cost[k] = ws[e]; g->eid[k] = e;
  }
  free(pos);
  return 1;
}

/*
  Optimality certificate generator. Given a perfect matching (mate_l,
  mate_r) and CSA's prices p of the right vertices, computes exact
  integer potentials.

  The dual of a right vertex r is d[r]; the dual of a left vertex l is
  w(l, M l) - d[M l], which makes every matching edge tight. Feasibility
  of the edge (l, r) then reads
      d[r] <= d[M l] + w(l, r) - w(l, M l),
  a shortest-path condition on the right vertices. CSA's prices satisfy
  it up to its final epsilon, so they are an almost feasible start: the
  label-correcting loop below starts from the rounded prices and only
  repairs the few violated conditions. It finds a feasible d iff the
  matching is optimal; a vertex queued more than nr times means a
  negative cycle, i.e. the matching is not optimal.

  (Dijkstra would need exactly feasible reduced costs to start from,
  which CSA's epsilon-optimal prices are not.)
*/
static int dual_gen(const adj_t *g, const int64_t *mate_l, const int64_t *mate_r,
                    const double *price, int64_t *mcost, int64_t *d) {
  int64_t nl = g->nl, nr = g->nr;
  for (int64_t l = 0; l < nl; l++) {
    mcost[l] = 0;
    for (int64_t k = g->off[l]; k < g->off[l + 1]; k++)
      if (g->head[k] == mate_l[l]) mcost[l] = g->cost[k];
  }
  int64_t *queue = malloc(((size_t)nr + 1) * sizeof(int64_t));
  int64_t *cnt = calloc((size_t)nr + 1, sizeof(int64_t));
  char *inq = calloc((size_t)nr + 1, 1);
  if (!queue || !cnt || !inq) { free(queue); free(cnt); free(inq); return 0; }
  int64_t qh = 0, qt = 0, qn = 0;
  for (int64_t r = 0; r < nr; r++) {
    d[r] = (int64_t)floor(price[r] + 0.5);
    queue[qt++] = r; inq[r] = 1; qn++;
  }
  if (qt == nr) qt = 0;
  int ok = 1;
  while (qn > 0 && ok) {
    int64_t u = queue[qh++]; if (qh == nr) qh = 0; qn--; inq[u] = 0;
    int64_t l = mate_r[u];
    for (int64_t k = g->off[l]; k < g->off[l + 1]; k++) {
      int64_t r = g->head[k];
      int64_t nd = d[u] + g->cost[k] - mcost[l];
      if (nd < d[r]) {
        d[r] = nd;
        if (!inq[r]) {
          if (++cnt[r] > nr) { ok = 0; break; }
          queue[qt++] = r; if (qt == nr) qt = 0; qn++; inq[r] = 1;
        }
      }
    }
  }
  free(queue); free(cnt); free(inq);
  return ok;
}

/*
  Infeasibility certificate generator. Starts from CSA's (partial)
  matching and searches alternating paths from the free left vertices
  (BFS), augmenting along each one it finds. When a search finds no
  augmenting path, the left vertices it reached form a Hall violator:
  all right vertices they reach are matched to reached left vertices,
  and the start vertex is free, so |N(S)| = |S| - 1.

  Returns the size of S (written to s_out as left indices), or -1 if
  the matching became perfect (then there is no violator, and no dual
  either, so the answer is unknown).
*/
static int64_t hall_gen(const adj_t *g, int64_t *mate_l, int64_t *mate_r,
                        int64_t *s_out) {
  int64_t nl = g->nl, nr = g->nr;
  int64_t *seen_l = malloc(((size_t)nl + 1) * sizeof(int64_t));
  int64_t *seen_r = malloc(((size_t)nr + 1) * sizeof(int64_t));
  int64_t *par_r = malloc(((size_t)nr + 1) * sizeof(int64_t));
  int64_t *queue = malloc(((size_t)nl + 1) * sizeof(int64_t));
  int64_t res = -2;
  if (!seen_l || !seen_r || !par_r || !queue) goto out;
  for (int64_t i = 0; i < nl; i++) seen_l[i] = -1;
  for (int64_t j = 0; j < nr; j++) seen_r[j] = -1;
  for (int64_t s = 0; s < nl; s++) {
    if (mate_l[s] >= 0) continue;
    int64_t qh = 0, qt = 0, free_r = -1;
    queue[qt++] = s; seen_l[s] = s;
    while (qh < qt && free_r < 0) {
      int64_t u = queue[qh++];
      for (int64_t k = g->off[u]; k < g->off[u + 1]; k++) {
        int64_t r = g->head[k];
        if (seen_r[r] == s) continue;
        seen_r[r] = s; par_r[r] = u;
        if (mate_r[r] < 0) { free_r = r; break; }
        int64_t v = mate_r[r];
        if (seen_l[v] != s) { seen_l[v] = s; queue[qt++] = v; }
      }
    }
    if (free_r < 0) {
      for (int64_t i = 0; i < qt; i++) s_out[i] = queue[i];
      res = qt;
      goto out;
    }
    for (int64_t r = free_r; r >= 0; ) {
      int64_t l = par_r[r], next = mate_l[l];
      mate_l[l] = r; mate_r[r] = l; r = next;
    }
  }
  res = -1;
out:
  free(seen_l); free(seen_r); free(par_r); free(queue);
  return res < -1 ? -1 : res;
}

/*
  The oracle. Inputs: n, the m edges (fs, ts, ws), the nl left vertices
  ls and the nr right vertices rs. Outputs, depending on the status:
    ASN_OPT:    ms_out[0..nl) the edge ids of the matching,
                ys_out[0..n) the dual;
    ASN_INFEAS: s_out[0..*len_out) the Hall violator (vertex ids);
    ASN_UNKNOWN: nothing.
  The output arrays must have room for nl, n and nl entries.
*/
static int64_t oracle_run(int64_t n, int64_t m, const int64_t *fs, const int64_t *ts,
                          const int64_t *ws, int64_t nl, const int64_t *ls, int64_t nr,
                          const int64_t *rs, int64_t *ms_out, int64_t *ys_out,
                          int64_t *s_out, int64_t *len_out) {
  *len_out = 0;
  if (nl != nr) return ASN_INFEAS;
  if (nl == 0) {
    for (int64_t v = 0; v < n; v++) ys_out[v] = 0;
    return ASN_OPT;
  }
  /* CSA computes with doubles; keep all sums exact. */
  int64_t maxc = 0;
  for (int64_t e = 0; e < m; e++) {
    int64_t c = ws[e] < 0 ? -ws[e] : ws[e];
    if (ws[e] == INT64_MIN || c > ((int64_t)1 << 31)) return ASN_UNKNOWN;
    if (c > maxc) maxc = c;
  }
  if ((double)(nl + 1) * 16.0 * ((double)maxc + 1.0) > 4503599627370496.0)
    return ASN_UNKNOWN;

  int64_t status = ASN_UNKNOWN;
  int64_t *idx = malloc(((size_t)n + 1) * sizeof(int64_t));
  int64_t *li = malloc(((size_t)m + 1) * sizeof(int64_t));
  int64_t *ri = malloc(((size_t)m + 1) * sizeof(int64_t));
  long *tl = malloc(((size_t)m + 1) * sizeof(long));
  long *hd = malloc(((size_t)m + 1) * sizeof(long));
  long *cs = malloc(((size_t)m + 1) * sizeof(long));
  int64_t *mate_l = malloc(((size_t)nl + 1) * sizeof(int64_t));
  int64_t *mate_r = malloc(((size_t)nr + 1) * sizeof(int64_t));
  double *price = malloc(((size_t)nr + 1) * sizeof(double));
  int64_t *mcost = malloc(((size_t)nl + 1) * sizeof(int64_t));
  int64_t *d = malloc(((size_t)nr + 1) * sizeof(int64_t));
  adj_t g = { nl, nr, NULL, NULL, NULL, NULL };
  if (!idx || !li || !ri || !tl || !hd || !cs || !mate_l || !mate_r || !price ||
      !mcost || !d)
    goto out;

  for (int64_t i = 0; i < nl; i++) idx[ls[i]] = i;
  for (int64_t j = 0; j < nr; j++) idx[rs[j]] = j;
  for (int64_t e = 0; e < m; e++) {
    li[e] = idx[fs[e]]; ri[e] = idx[ts[e]];
    tl[e] = (long)li[e]; hd[e] = (long)ri[e]; cs[e] = (long)ws[e];
  }
  if (!adj_build(&g, m, li, ri, ws)) goto out;

  /*
    CSA assumes that every node is on an arc. A left node l without arcs
    is the Hall violator {l}; with a right node without arcs (and
    |L| = |R|), all of L is one. (The verified program never asks the
    oracle in these cases; this only keeps the oracle total.)
  */
  for (int64_t i = 0; i < nl; i++)
    if (g.off[i] == g.off[i + 1]) {
      s_out[0] = ls[i]; *len_out = 1; status = ASN_INFEAS; goto out;
    }
  for (int64_t j = 0; j < nr; j++) mate_r[j] = 0;
  for (int64_t e = 0; e < m; e++) mate_r[ri[e]] = 1;
  for (int64_t j = 0; j < nr; j++)
    if (!mate_r[j]) {
      for (int64_t i = 0; i < nl; i++) s_out[i] = ls[i];
      *len_out = nl; status = ASN_INFEAS; goto out;
    }

  ASN_STAMP(2);
  int r = csa_solve_arrays((unsigned)nl, (unsigned)nr, (unsigned)m, tl, hd, cs);
  ASN_STAMP(3);
  if (r == 2) goto out;
  for (int64_t j = 0; j < nr; j++) { mate_r[j] = -1; price[j] = csa_rhs_price((unsigned)j); }
  int perfect = 1;
  for (int64_t i = 0; i < nl; i++) {
    mate_l[i] = csa_lhs_match((unsigned)i);
    if (mate_l[i] < 0) perfect = 0; else mate_r[mate_l[i]] = i;
  }
  csa_release();

  if (r == 0 && perfect) {
    if (!dual_gen(&g, mate_l, mate_r, price, mcost, d)) goto out;
    for (int64_t v = 0; v < n; v++) ys_out[v] = 0;
    for (int64_t j = 0; j < nr; j++) ys_out[rs[j]] = d[j];
    for (int64_t i = 0; i < nl; i++) {
      ys_out[ls[i]] = mcost[i] - d[mate_l[i]];
      for (int64_t k = g.off[i]; k < g.off[i + 1]; k++)
        if (g.head[k] == mate_l[i]) ms_out[i] = g.eid[k];
    }
#ifdef ASN_FAULT
    /*
      Fault injection (testing only): replace one matching edge and shift one
      dual value. The checker must reject; if it accepted, the solution
      printed would not be the (optimal perfect) matching, which the tests
      detect. So a correct answer from this build shows that the verified
      cleanup ran.
    */
    ms_out[0] = (ms_out[0] + 1) % m;
    ys_out[ls[0]] += 1;
#endif
    status = ASN_OPT;
  } else {
    int64_t k = hall_gen(&g, mate_l, mate_r, s_out);
    if (k >= 0) {
      for (int64_t i = 0; i < k; i++) s_out[i] = ls[s_out[i]];
      *len_out = k;
      status = ASN_INFEAS;
    }
  }
out:
  adj_free(&g);
  free(idx); free(li); free(ri); free(tl); free(hd); free(cs);
  free(mate_l); free(mate_r); free(price); free(mcost); free(d);
  return status;
}

int64_t asn_oracle(int64_t n, int64_t m, const int64_t *fs, const int64_t *ts,
                   const int64_t *ws, int64_t nl, const int64_t *ls, int64_t nr,
                   const int64_t *rs, int64_t *ms_out, int64_t *ys_out,
                   int64_t *s_out, int64_t *len_out) {
  int64_t status = oracle_run(n, m, fs, ts, ws, nl, ls, nr, rs, ms_out, ys_out,
                              s_out, len_out);
  ASN_STAMP(4);
  return status;
}
