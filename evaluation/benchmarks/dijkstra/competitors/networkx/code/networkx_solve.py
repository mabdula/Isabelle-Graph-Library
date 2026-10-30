#!/usr/bin/env python3
"""Answer point-to-point shortest-path queries with NetworkX, timing the call.

Prints one CSV row, in exactly the column order the SML,
Scala, Go, LEMON and SciPy drivers use, so every solver's rows sit in one
table.

The entry point is

    networkx.single_source_dijkstra(G, source, target=t, weight="weight")

which is NetworkX's own binary-heap Dijkstra in pure Python, and which does
stop as soon as the target is settled -- unlike SciPy's, which has no target
argument at all.  It returns the distance and the path, so the hop count is
read straight off the answer rather than walked back through a predecessor
array.

Building the DiGraph sits outside the clock.  That is allowed here and not for
our export: a library like this one would normally read the file straight into
its own structure, so the build fuses with parsing, which verified exported
code handed plain arrays cannot do.  The asymmetry is inherent and it favours
NetworkX -- which it needs, since building the graph is by far the slowest
thing this driver does.

Parallel arcs are collapsed to their cheapest member before the graph is
built: a DiGraph cannot hold two arcs between the same pair and add_edge
silently overwrites, keeping whichever came last.  See dedupe_min in
gr_read.py.

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

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import argparse
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gr_read import (HEADER, cpu_ms, dedupe_min, emit, limit_memory,
                     parse_gr)

import networkx as nx


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

    # ---- outside the clock: parse, de-duplicate, build the DiGraph ----
    # Each of the three is clocked on its own and reported in its own column,
    # so what sits outside the measurement is visible rather than asserted.
    a0, b0 = cpu_ms()
    n, m, frm, to, w = parse_gr(args.instance)
    a1, b1 = cpu_ms()
    frm, to, w = dedupe_min(n, frm, to, w)
    a2, b2 = cpu_ms()
    try:
        g = nx.DiGraph()
        g.add_nodes_from(range(n))
        g.add_weighted_edges_from(zip(frm.tolist(), to.tolist(), w.tolist()),
                                  weight="weight")
    except MemoryError:
        sys.exit("out of memory building the graph")
    a3, b3 = cpu_ms()
    setup = ["%.3f" % (a1 - a0 + b1 - b0), "%.3f" % (a2 - a1 + b2 - b1),
             "%.3f" % (a3 - a2 + b3 - b2)]

    # Force the lazy import of the dijkstra implementation before the clock
    # starts: loading a module is admin, not solving.
    nx.single_source_dijkstra(g, 0, target=0, weight="weight")

    for qid, s, t in [(args.query, args.source, args.target)]:
        if not (1 <= s <= n and 1 <= t <= n):
            sys.exit("query %d: (%d, %d) outside [1, %d]" % (qid, s, t, n))
        si, ti = s - 1, t - 1
        for rep in range(1, args.repeats + 1):
            u0, y0 = cpu_ms()
            w0 = time.perf_counter()
            try:
                try:
                    dist, path = nx.single_source_dijkstra(
                        g, si, target=ti, weight="weight")
                    found = True
                except nx.NetworkXNoPath:
                    found = False
            except MemoryError:
                w1 = time.perf_counter()
                u1, y1 = cpu_ms()
                emit([base, n, m, qid, s, t, rep, "MEMORY", 0, 0, -1,
                      "%.3f" % (u1 - u0 + y1 - y0), "%.3f" % (u1 - u0),
                      "%.3f" % (y1 - y0), "%.3f" % (u1 - u0 + y1 - y0),
                      "%.3f" % ((w1 - w0) * 1000.0)] + setup + [args.tag], args.human)
                sys.exit(1)
            w1 = time.perf_counter()
            u1, y1 = cpu_ms()

            usr, sysr = u1 - u0, y1 - y0
            cpu = usr + sysr
            wall = (w1 - w0) * 1000.0

            # ---- after the clock: read the answer off ----
            if not found:
                status, reached, hops, dval = "UNREACHABLE", 0, 0, -1
            else:
                ok = path[0] == si and path[-1] == ti
                status = "OPTIMAL" if ok else "BAD_PATH"
                reached = 1
                hops = len(path) - 1 if ok else 0
                dval = int(dist)

            emit([base, n, m, qid, s, t, rep, status, reached, hops, dval,
                  "%.3f" % cpu, "%.3f" % usr, "%.3f" % sysr, "%.3f" % cpu,
                  "%.3f" % wall] + setup + [args.tag], args.human)


if __name__ == "__main__":
    main()
