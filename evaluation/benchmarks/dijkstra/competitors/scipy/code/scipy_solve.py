#!/usr/bin/env python3
"""Answer point-to-point shortest-path queries with SciPy, timing the call.

Prints one CSV row, in exactly the column order the SML,
Scala, Go and LEMON drivers use, so every solver's rows sit in one table.

The entry point is

    scipy.sparse.csgraph.dijkstra(graph, indices=source,
                                  return_predecessors=True)

Two things about it have to be said plainly, because they shape the number.

ONE: SciPy's Dijkstra has no target.  It settles the whole reachable graph
from the source; there is no way to ask it to stop when t comes off the heap.
Our export, LEMON and NetworkX all stop early.  On a road network where s and
t are close that is a large difference, and it is a property of the library,
not of this benchmark -- it is the number a user who calls SciPy gets.  The
`tag' column records `earlystop=no' on every row so the distinction survives
into the raw data.

TWO: predecessors are asked for.  The question this study asks is for a
shortest PATH, not for its length: our export returns the arcs of the path and
LEMON builds its predecessor map as a matter of course.  Asking SciPy for the
same thing is the like-for-like reading, and it costs it an extra array.

THE CSR BUILD IS INSIDE THE CLOCK, since the re-run of 2026-10-14.  The
first campaign left it outside, on the grounds that a library reads a file
straight into its own structure, so its build fuses with parsing.  That does
not hold for a CSR matrix: tocsr() takes the COMPLETE arc arrays, sorts them
by row and packs them -- a separate pass over every arc, exactly the pass our
exported code makes inside its entry point.  So the clock opens on the parsed
arrays and covers coo_matrix(...).tocsr() and the solve, and the matrix is
rebuilt on every repeat.  The same rule is applied to LEMON's StaticDigraph
and JGraphT's sparse graph in this study.  What stays outside is the file
read (parse_ms) and turning the parsed arrays into the arrays the constructor
takes (build_ms) -- marshalling into the library's input format, not the
building of its structure.  The first campaign's rows, with the build
outside, are labelled INVALID in their results directory.

The clock is CPU time (user + system) over the whole process, getrusage, the
same quantity the other drivers read.  Wall time is recorded but nothing is
derived from it.

ONE PROBLEM PER PROCESS.  The source and the target are given on the command
line and exactly one of them is accepted: a shortest-path problem is a graph
AND a pair, so two pairs are two problems and must not share a solver call, a
solver object, or a process.  There is deliberately no way to hand this driver
a list of pairs -- in particular SciPy's `indices' argument takes a list, and
passing one would solve several problems in a single call.

parse_ms, dedup_ms and build_ms report the work done OUTSIDE the clock, so
that what is outside it is visible rather than merely asserted.
"""

import os

# Set before numpy is imported.  Nothing here uses BLAS, but a stray threaded
# BLAS would put time on cores this run was not given, and CPU time counts
# every thread of the process.
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import argparse
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gr_read import (HEADER, cpu_ms, dedupe_min, emit, limit_memory,
                     parse_gr)

import numpy as np
import scipy
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import dijkstra


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("instance", nargs="?")
    ap.add_argument("--source", type=int, default=-1,
                    help="the source, a DIMACS node id (1-based)")
    ap.add_argument("--target", type=int, default=-1,
                    help="the target, a DIMACS node id (1-based)")
    ap.add_argument("--query", type=int, default=0,
                    help="the id this pair carries in queries.csv")
    ap.add_argument("--repeats", type=int, default=1,
                    help="solve the SAME problem this many times, one row each")
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
    if args.source < 0:
        ap.error("a --source is required")
    if args.target < 0:
        ap.error("a --target is required")
    limit_memory(args.mem_gb)

    base = os.path.basename(args.instance)

    # ---- outside the clock: parse, de-duplicate, make the input arrays ----
    # Each of the three is clocked on its own and reported in its own column,
    # so what sits outside the measurement is visible rather than asserted.
    a0, b0 = cpu_ms()
    n, m, frm, to, w = parse_gr(args.instance)
    a1, b1 = cpu_ms()
    # One arc per pair, the cheapest: a CSR build would otherwise ADD the
    # weights of parallel arcs.  See dedupe_min in gr_read.py.
    frm, to, w = dedupe_min(n, frm, to, w)
    a2, b2 = cpu_ms()
    # The CSR build itself is INSIDE the clock below; see the note at the top.
    wf = w.astype(np.float64)
    a3, b3 = cpu_ms()
    setup = ["%.3f" % (a1 - a0 + b1 - b0), "%.3f" % (a2 - a1 + b2 - b1),
             "%.3f" % (a3 - a2 + b3 - b2)]

    tag = args.tag + (";" if args.tag else "") + "earlystop=no"

    for qid, s, t in [(args.query, args.source, args.target)]:
        if not (1 <= s <= n and 1 <= t <= n):
            sys.exit("query %d: (%d, %d) outside [1, %d]" % (qid, s, t, n))
        si, ti = s - 1, t - 1
        for rep in range(1, args.repeats + 1):
            u0, y0 = cpu_ms()
            w0 = time.perf_counter()
            um = ym = None
            try:
                # ---- the measurement: build the CSR matrix, then solve ----
                graph = coo_matrix((wf, (frm, to)), shape=(n, n)).tocsr()
                # ---- the intermediate reading: the structure is built ----
                um, ym = cpu_ms()
                dist, pred = dijkstra(graph, directed=True, indices=si,
                                      return_predecessors=True)
            except MemoryError:
                w1 = time.perf_counter()
                u1, y1 = cpu_ms()
                emit([base, n, m, qid, s, t, rep, "MEMORY", 0, 0, -1,
                      "%.3f" % (u1 - u0 + y1 - y0), "%.3f" % (u1 - u0),
                      "%.3f" % (y1 - y0), "%.3f" % (u1 - u0 + y1 - y0),
                      "%.3f" % ((w1 - w0) * 1000.0)] + setup + ["", "", tag], args.human)
                sys.exit(1)
            w1 = time.perf_counter()
            u1, y1 = cpu_ms()

            usr, sysr = u1 - u0, y1 - y0
            cpu = usr + sysr
            # the two parts of the clocked period; they add up to cpu
            parts = ["%.3f" % (um - u0 + ym - y0), "%.3f" % (u1 - um + y1 - ym)]
            wall = (w1 - w0) * 1000.0

            # ---- after the clock: read the answer off ----
            d = dist[ti]
            if not np.isfinite(d):
                status, reached, hops, dval = "UNREACHABLE", 0, 0, -1
            else:
                hops = 0
                v = ti
                ok = True
                while v != si:
                    v = pred[v]
                    if v < 0:
                        ok = False
                        break
                    hops += 1
                status = "OPTIMAL" if ok else "BAD_PATH"
                reached, dval = 1, int(round(d))
                if not ok:
                    hops = 0

            emit([base, n, m, qid, s, t, rep, status, reached, hops, dval,
                  "%.3f" % cpu, "%.3f" % usr, "%.3f" % sysr, "%.3f" % cpu,
                  "%.3f" % wall] + setup + parts + [tag], args.human)


if __name__ == "__main__":
    main()
