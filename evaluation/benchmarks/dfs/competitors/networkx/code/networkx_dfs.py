#!/usr/bin/env python3
"""Search a whole graph with NetworkX's depth-first search, timing the call.

Prints one CSV row, in exactly the column order the SML, Scala, Go, LEMON,
JGraphT and SciPy drivers use, so every solver's rows sit in one table.

The entry point is

    dict(networkx.dfs_predecessors(G, source))

NetworkX's own depth-first search, in pure Python.  It yields (node, parent)
as it goes, so the dict() is what actually drives the search; draining the
generator is the measurement.

IT SWEEPS EVERYTHING REACHABLE FROM THE SOURCE, AND NOTHING ELSE.
dfs_predecessors has no target and no early exit, and given a source it walks
that source's component only -- it does not restart in another component the
way the no-source form would.  That is the same work the three verified
exports do when they are given a target the graph does not contain, which is
how this study runs them, and it is what LEMON, JGraphT and SciPy are made to
do here as well.  The `tag' column records `wholegraph=yes' on every row so
that this survives into the raw data.

THE CROSS-CHECK IS THE NUMBER OF VERTICES VISITED.  The order the vertices
come out in is a property of the implementation; HOW MANY come out is a
property of the graph and the source alone.  dfs_predecessors omits the
source itself, which has no parent, so `visited' is the size of the map plus
one.

WEIGHTS ARE NOT LOADED AT ALL.  This is DFS; the DiGraph is built from bare
pairs.  That also means parallel arcs need no collapsing -- a DiGraph holds
the pair once and the second copy is simply absorbed -- so dedup_ms is an
honest 0.000.

Building the DiGraph sits outside the clock.  That is allowed here and not for
our exports: a library like this one would normally read the file straight
into its own structure, so the build fuses with parsing, which verified
exported code handed plain arrays cannot do.  The asymmetry is inherent and it
favours NetworkX -- which it needs, since building the graph is by far the
slowest thing this driver does.

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

    # ---- outside the clock: parse and build the DiGraph ----
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

    # Force the lazy import of the depth-first implementation before the
    # clock starts: loading a module is admin, not searching.
    dict(nx.dfs_predecessors(g, 0))

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
        try:
            # ---- the measurement ----
            pred = dict(nx.dfs_predecessors(g, si))
        except MemoryError:
            w1 = time.perf_counter()
            u1, y1 = cpu_ms()
            emit([base, n, m, qid, s, t, rep, "MEMORY", 0, -1,
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
        # The map holds every vertex the search settled except the source,
        # which has no parent.  The target is not a vertex, so `reached' is 0.
        visited = len(pred) + 1
        emit([base, n, m, qid, s, t, rep, "OK", 0, visited,
              "%.3f" % cpu, "%.3f" % usr, "%.3f" % sysr, "%.3f" % cpu,
              "%.3f" % wall] + setup + [tag], args.human)


if __name__ == "__main__":
    main()
