#!/usr/bin/env python3
"""Search a whole graph with SciPy's depth-first order, timing the call.

Prints one CSV row, in exactly the column order the SML, Scala, Go, LEMON and
JGraphT drivers use, so every solver's rows sit in one table.

The entry point is

    scipy.sparse.csgraph.depth_first_order(graph, i_start=source,
                                           directed=True,
                                           return_predecessors=True)

which is a genuine depth-first search, and it is the counterpart of
breadth_first_order that the BFS study measured.

IT SWEEPS EVERYTHING REACHABLE FROM THE SOURCE, AND NOTHING ELSE.
depth_first_order has no target argument and no early exit, and it does not
continue into other components once the source's component runs dry: the node
array it returns is exactly the region reachable from the source.  That is the
same work the three verified exports do when they are given a target the graph
does not contain, which is how this study runs them, and it is what LEMON,
JGraphT and NetworkX are made to do here as well.  No solver in this study is
given a shortcut another one does not have, and none of them does extra work
the others do not.

THE CROSS-CHECK IS THE NUMBER OF VERTICES VISITED.  The order the vertices
come out in is a property of the implementation -- SciPy's depth-first order
is not our export's -- but HOW MANY come out is a property of the graph and
the source alone.  So `visited' is the column the solvers are checked against
each other on, and here it is simply the length of the returned node array.

THE MATRIX IS ONES, NOT WEIGHTS.  csgraph reads a stored zero as "no edge",
and the challenge's generators draw weights from [0, n], so a weighted matrix
would silently lose every zero-weight arc.  The graph is unweighted anyway,
so every arc is a 1.  Parallel arcs then sum to 2 or 3, which is still
non-zero and still exactly one edge; nothing needs collapsing, and dedup_ms
is an honest 0.000.

THE CSR BUILD IS INSIDE THE CLOCK.  A structure that can be filled while the
file is read may be built outside the clock; a CSR matrix cannot be: tocsr() takes the COMPLETE arc arrays, sorts them
by row and packs them -- a separate pass over every arc, exactly the pass our
exported code makes inside its entry point.  So the clock opens on the parsed
arrays and covers coo_matrix(...).tocsr() and the solve, and the matrix is
rebuilt on every repeat.  The same rule is applied to LEMON's StaticDigraph
and JGraphT's sparse graph in this study.  What stays outside is the file
read (parse_ms) and turning the parsed arrays into the arrays the constructor
takes (build_ms) -- marshalling into the library's input format, not the
building of its structure.  The scipy_prebuilt column measures the same call
with the matrix built before the clock.

The clock is CPU time (user + system) over the whole process, getrusage, the
same quantity the other drivers read.  Wall time is recorded but nothing is
derived from it.

ONE PROBLEM PER PROCESS.  The source is given on the command line and exactly
one is accepted: a search problem is a graph AND a source, so two sources are
two problems and must not share a solver call, a solver object, or a process.
There is deliberately no way to hand this driver a list of sources.

THE TARGET MUST NOT BE A VERTEX.  It is carried on the command line only so
that every driver in the study takes the same arguments, and this one refuses
anything inside [1, n], exactly as the exports' drivers do.

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
from gr_read import HEADER, cpu_ms, emit, limit_memory, parse_gr

import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import depth_first_order


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("instance", nargs="?")
    ap.add_argument("--source", type=int, default=-1,
                    help="the source, a DIMACS node id (1-based)")
    ap.add_argument("--target", type=int, default=-1,
                    help="must NOT be a node of the graph; the campaign "
                         "passes 0")
    ap.add_argument("--query", type=int, default=0,
                    help="the id this source carries in queries.csv")
    ap.add_argument("--repeats", type=int, default=1,
                    help="search the SAME problem this many times, one row each")
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

    # ---- outside the clock: parse, and make the constructor's arrays ----
    # The CSR build itself is INSIDE the clock below; see the note at the top.
    a0, b0 = cpu_ms()
    n, m, frm, to, _w = parse_gr(args.instance)
    a1, b1 = cpu_ms()
    ones = np.ones(frm.size, dtype=np.int8)
    a2, b2 = cpu_ms()
    setup = ["%.3f" % (a1 - a0 + b1 - b0), "0.000",
             "%.3f" % (a2 - a1 + b2 - b1)]

    tag = args.tag + (";" if args.tag else "") + "wholegraph=yes"

    qid, s, t = args.query, args.source, args.target
    if not 1 <= s <= n:
        sys.exit("query %d: source %d outside [1, %d]" % (qid, s, n))
    if 1 <= t <= n:
        sys.exit("query %d: target %d IS a node of this graph; this study "
                 "searches the whole graph and needs a target outside "
                 "[1, %d]" % (qid, t, n))
    si = s - 1
    for rep in range(1, args.repeats + 1):
        u0, y0 = cpu_ms()
        w0 = time.perf_counter()
        um = ym = None
        try:
            # ---- the measurement: build the CSR matrix, then search it ----
            graph = coo_matrix((ones, (frm, to)), shape=(n, n)).tocsr()
            # ---- the intermediate reading: the structure is built ----
            um, ym = cpu_ms()
            order, _pred = depth_first_order(
                graph, i_start=si, directed=True,
                return_predecessors=True)
        except MemoryError:
            w1 = time.perf_counter()
            u1, y1 = cpu_ms()
            emit([base, n, m, qid, s, t, rep, "MEMORY", 0, -1,
                  "%.3f" % (u1 - u0 + y1 - y0), "%.3f" % (u1 - u0),
                  "%.3f" % (y1 - y0), "%.3f" % (u1 - u0 + y1 - y0),
                  "%.3f" % ((w1 - w0) * 1000.0)] + setup + ["", "", tag],
                 args.human)
            sys.exit(1)
        w1 = time.perf_counter()
        u1, y1 = cpu_ms()

        usr, sysr = u1 - u0, y1 - y0
        cpu = usr + sysr
        # the two parts of the clocked period; they add up to cpu
        parts = ["%.3f" % (um - u0 + ym - y0), "%.3f" % (u1 - um + y1 - ym)]
        wall = (w1 - w0) * 1000.0

        # ---- after the clock: read the answer off ----
        # The node array holds exactly the region reachable from the source,
        # each vertex once.  The target is not a vertex, so `reached' is 0.
        visited = int(order.size)
        emit([base, n, m, qid, s, t, rep, "OK", 0, visited,
              "%.3f" % cpu, "%.3f" % usr, "%.3f" % sysr, "%.3f" % cpu,
              "%.3f" % wall] + setup + parts + [tag], args.human)


if __name__ == "__main__":
    main()
