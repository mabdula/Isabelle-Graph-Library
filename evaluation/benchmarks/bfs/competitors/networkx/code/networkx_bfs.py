#!/usr/bin/env python3
"""Answer point-to-point reachability queries with NetworkX's BFS, timing the call.

Prints one CSV row, in exactly the column order the SML, Scala, Go, LEMON,
JGraphT and SciPy drivers use, so every solver's rows sit in one table.

The entry point is

    dict(networkx.bfs_predecessors(G, source))

NetworkX's own breadth-first search, in pure Python.  It yields (node, parent)
as it goes, so the dict() is what actually drives the search; draining the
generator is the measurement, and the parent map it produces is the same
answer the imperative export returns.

NO EARLY EXIT, AND THAT IS THE POINT.  bfs_predecessors has no target: it
walks everything reachable from the source.  Neither verified BFS export takes
a target either -- the imperative one fills a distance array and a parent
array over the whole graph, the functional one runs rounds until the frontier
empties and then asks whether the target is in the visited set -- so every
solver in this study settles the whole reachable region.  Nothing here is
given a shortcut the exports do not have.  The `tag' column records
`earlystop=no' on every row so that this survives into the raw data.

WEIGHTS ARE NOT LOADED AT ALL.  This is BFS; the DiGraph is built from bare
pairs.  That also means parallel arcs need no collapsing -- a DiGraph holds
the pair once and the second copy is simply absorbed -- so dedup_ms is an
honest 0.000 rather than work hidden outside the clock.  The Dijkstra study
had to collapse them, because add_edge overwrites weights.

Building the DiGraph sits outside the clock.  That is allowed here and not for
our exports: a library like this one would normally read the file straight
into its own structure, so the build fuses with parsing, which verified
exported code handed plain arrays cannot do.  The asymmetry is inherent and it
favours NetworkX -- which it needs, since building the graph is by far the
slowest thing this driver does.

The clock is CPU time (user + system) over the whole process, getrusage, the
same quantity the other drivers read.  Wall time is recorded but nothing is
derived from it.

ONE PROBLEM PER PROCESS.  The source and the target are given on the command
line and exactly one of them is accepted: a search problem is a graph AND a
pair, so two pairs are two problems and must not share a solver call, a solver
object, or a process.  There is deliberately no way to hand this driver a list
of pairs.

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
from gr_read import HEADER, cpu_ms, emit, limit_memory, parse_gr

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

    # ---- outside the clock: parse and build the DiGraph ----
    # Each phase is clocked on its own and reported in its own column, so
    # what sits outside the measurement is visible rather than asserted.
    # There is no de-duplication phase: see the note at the top.
    a0, b0 = cpu_ms()
    n, m, frm, to, _w = parse_gr(args.instance)
    a1, b1 = cpu_ms()
    try:
        g = nx.DiGraph()
        g.add_nodes_from(range(n))
        g.add_edges_from(zip(frm.tolist(), to.tolist()))
    except MemoryError:
        sys.exit("out of memory building the graph")
    a2, b2 = cpu_ms()
    setup = ["%.3f" % (a1 - a0 + b1 - b0), "0.000",
             "%.3f" % (a2 - a1 + b2 - b1)]

    # Force the lazy import of the breadth-first implementation before the
    # clock starts: loading a module is admin, not searching.
    dict(nx.bfs_predecessors(g, 0))

    tag = args.tag + (";" if args.tag else "") + "earlystop=no"

    for qid, s, t in [(args.query, args.source, args.target)]:
        if not (1 <= s <= n and 1 <= t <= n):
            sys.exit("query %d: (%d, %d) outside [1, %d]" % (qid, s, t, n))
        si, ti = s - 1, t - 1
        for rep in range(1, args.repeats + 1):
            u0, y0 = cpu_ms()
            w0 = time.perf_counter()
            try:
                # ---- the measurement ----
                pred = dict(nx.bfs_predecessors(g, si))
            except MemoryError:
                w1 = time.perf_counter()
                u1, y1 = cpu_ms()
                emit([base, n, m, qid, s, t, rep, "MEMORY", 0, 0, -1,
                      "%.3f" % (u1 - u0 + y1 - y0), "%.3f" % (u1 - u0),
                      "%.3f" % (y1 - y0), "%.3f" % (u1 - u0 + y1 - y0),
                      "%.3f" % ((w1 - w0) * 1000.0)] + setup + [tag],
                     args.human)
                sys.exit(1)
            w1 = time.perf_counter()
            u1, y1 = cpu_ms()

            usr, sysr = u1 - u0, y1 - y0
            cpu = usr + sysr
            wall = (w1 - w0) * 1000.0

            # ---- after the clock: read the answer off ----
            # bfs_predecessors omits the source, so a target that IS the
            # source is reached at zero hops and appears in no dict.
            if ti == si:
                status, reached, hops = "REACHED", 1, 0
            elif ti in pred:
                hops = 0
                v = ti
                ok = True
                while v != si:
                    v = pred.get(v, -1)
                    if v < 0:
                        ok = False
                        break
                    hops += 1
                    if hops > n:
                        ok = False
                        break
                status = "REACHED" if ok else "BAD_PATH"
                reached = 1
                if not ok:
                    hops = 0
            else:
                status, reached, hops = "UNREACHABLE", 0, 0

            # `dist' repeats the hop count: in an unweighted graph the two
            # are the same number, and keeping the column lets a BFS row and
            # a Dijkstra row sit in the same table without reshaping either.
            dval = hops if reached else -1

            emit([base, n, m, qid, s, t, rep, status, reached, hops, dval,
                  "%.3f" % cpu, "%.3f" % usr, "%.3f" % sysr, "%.3f" % cpu,
                  "%.3f" % wall] + setup + [tag], args.human)


if __name__ == "__main__":
    main()
