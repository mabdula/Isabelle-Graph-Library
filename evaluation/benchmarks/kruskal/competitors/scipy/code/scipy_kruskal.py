#!/usr/bin/env python3
"""Minimum spanning tree with SciPy's Kruskal, timing the call.

Prints one CSV row, in exactly the column order the SML, Scala, Go, LEMON and
JGraphT drivers use, so every solver's rows sit in one table.

The entry point is

    scipy.sparse.csgraph.minimum_spanning_tree(csr_matrix)

which SciPy's documentation says is computed with Kruskal's algorithm: it
sorts the stored entries by weight and joins endpoints in a union-find
forest, in Cython.

THE CSR BUILD IS INSIDE THE CLOCK.  minimum_spanning_tree converts whatever
it is given to a CSR matrix before its Kruskal runs, and a CSR matrix cannot
be filled while the file is read: its row pointer array needs the COMPLETE
edge list.  That is the rule of these studies: a structure that needs the
complete arc list is built after parsing, and that build is the first part
of the measured period; the solve is the second.  The two parts are reported
as clock_build_ms and clock_solve_ms, from one intermediate reading, and
they add up to cpu_ms.  The matrix is rebuilt on every repeat.  (A structure
that could be filled while parsing stays outside the clock -- LEMON's,
JGraphT's and NetworkX's graphs in this study are such structures; SciPy's
is not.)

THE BUILD IS THE CHEAP ONE.  The parser's collapse delivers the edges sorted
by (lo, hi), which is CSR order already, so the matrix is built as
csr_matrix((data, indices, indptr)): indices are the hi endpoints as they
stand, indptr is a bincount of the lo endpoints and a cumulative sum.  Two
sequential passes, O(n + m), no sort.  coo_matrix(...).tocsr() would sort
the entries by row a second time.

TWO THINGS ARE DONE TO THE ARCS BEFORE THE CLOCK, and both are forced by
the matrix form and reported:

  * ARCS ON THE SAME ORDERED PAIR ARE COLLAPSED TO THE CHEAPEST (dedup_ms).
    tocsr() ADDS the entries that land on the same (row, column), so two
    arcs (u, v) of weights 3 and 5 would become one edge of weight 8, a
    wrong input rather than a slow one.  The grid families have no repeated
    arc and pass through untouched; the dense family has a few per cent.
    Reverse arcs (v, u) are a different matrix position and are NOT
    collapsed: minimum_spanning_tree reads graph[u, v] and graph[v, u] as one
    undirected edge of the cheaper weight, inside the clock, which is exactly
    the parallel-edge handling every other solver does for itself.
  * EVERY WEIGHT IS SHIFTED UP BY ONE (build_ms).  The instances carry
    weight-0 arcs, and SciPy uses a stored zero as an edge but then drops it
    from the tree it returns (eliminate_zeros), so the returned tree would
    be short by every zero-weight tree edge and could not be checked.
    Adding one to every weight changes nothing about which edges form a
    minimum spanning tree; the shift is taken off again after the clock.

The clock is CPU time (user + system) over the whole process, getrusage, the
same quantity the other drivers read.  Wall time is recorded but nothing is
derived from it.

THE ANSWER IS CHECKED AFTER THE CLOCK: the returned tree must be a forest
(as many components as n minus its edge count) with n minus the number of
components of the graph edges, both counted with connected_components.  The
tree weight is reported for the cross-check between solvers.
"""

import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import argparse
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gr_read import HEADER, collapse_min, cpu_ms, emit, limit_memory, parse_gr

import numpy as np
from scipy.sparse import coo_matrix, csr_matrix
from scipy.sparse.csgraph import connected_components, minimum_spanning_tree


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("instance", nargs="?")
    ap.add_argument("--repeats", type=int, default=1,
                    help="solve the SAME instance this many times, one row each")
    ap.add_argument("--header", action="store_true")
    ap.add_argument("--human", action="store_true")
    ap.add_argument("--mem-gb", type=float, default=0.0,
                    help="cap this run's address space, in GiB (0 = no cap)")
    ap.add_argument("--tag", default="")
    args = ap.parse_args()

    if args.header:
        print(HEADER)
        return
    if not args.instance:
        ap.error("an instance is required")
    limit_memory(args.mem_gb)

    base = os.path.basename(args.instance)

    # ---- outside the clock: parse, collapse parallel edges, shift ----
    a0, b0 = cpu_ms()
    n, m, frm, to, w = parse_gr(args.instance)
    a1, b1 = cpu_ms()
    frm, to, w = collapse_min(n, frm, to, w)
    edges = int(frm.size)
    a2, b2 = cpu_ms()
    # the library's input arrays: float64 weights, int32 column indices
    data = (w + 1).astype(np.float64)
    indices = to.astype(np.int32)
    a3, b3 = cpu_ms()
    setup = ["%.3f" % (a1 - a0 + b1 - b0), "%.3f" % (a2 - a1 + b2 - b1),
             "%.3f" % (a3 - a2 + b3 - b2)]

    # the number of components of the whole graph, for the check
    comps = connected_components(
        coo_matrix((np.ones(frm.size, dtype=np.int8), (frm, to)), shape=(n, n)),
        directed=False, return_labels=False)

    for rep in range(1, args.repeats + 1):
        u0, y0 = cpu_ms()
        w0 = time.perf_counter()
        um = ym = None
        try:
            # ---- the measurement: build the CSR matrix, then Kruskal ----
            indptr = np.zeros(n + 1, dtype=np.int64)
            np.cumsum(np.bincount(frm, minlength=n), out=indptr[1:])
            graph = csr_matrix((data, indices, indptr), shape=(n, n))
            # ---- the intermediate reading: the structure is built ----
            um, ym = cpu_ms()
            tree = minimum_spanning_tree(graph)
        except MemoryError:
            w1 = time.perf_counter()
            u1, y1 = cpu_ms()
            emit([base, n, m, edges, rep, "MEMORY", 0, -1,
                  "%.3f" % (u1 - u0 + y1 - y0), "%.3f" % (u1 - u0),
                  "%.3f" % (y1 - y0), "%.3f" % (u1 - u0 + y1 - y0),
                  "%.3f" % ((w1 - w0) * 1000.0)] + setup + ["", "", args.tag],
                 args.human)
            sys.exit(1)
        w1 = time.perf_counter()
        u1, y1 = cpu_ms()

        usr, sysr = u1 - u0, y1 - y0
        cpu = usr + sysr
        parts = ["%.3f" % (um - u0 + ym - y0), "%.3f" % (u1 - um + y1 - ym)]
        wall = (w1 - w0) * 1000.0

        # ---- after the clock: read the answer off and check it ----
        cnt = int(tree.nnz)
        weight = int(round(float(tree.sum()))) - cnt      # the shift taken off
        tree_comps = connected_components(tree, directed=False, return_labels=False)
        ok = (tree_comps == n - cnt) and (cnt == n - comps)
        status = "SOLVED" if ok else "BAD_TREE"

        emit([base, n, m, edges, rep, status, cnt, weight,
              "%.3f" % cpu, "%.3f" % usr, "%.3f" % sysr, "%.3f" % cpu,
              "%.3f" % wall] + setup + parts + [args.tag], args.human)


if __name__ == "__main__":
    main()
