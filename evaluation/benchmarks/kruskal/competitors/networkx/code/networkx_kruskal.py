#!/usr/bin/env python3
"""Minimum spanning tree with NetworkX's Kruskal, timing the call.

Prints one CSV row, in exactly the column order the SML, Scala, Go, LEMON,
JGraphT and SciPy drivers use, so every solver's rows sit in one table.

The entry point is

    list(networkx.minimum_spanning_edges(G, algorithm="kruskal",
                                         weight="weight", data=True))

NetworkX's own Kruskal, in pure Python: it sorts the edges by weight and
joins endpoints in its UnionFind.  It yields the tree edges as it goes, so
the list() is what actually drives the algorithm; draining the generator is
the measurement.

THE GRAPH IS BUILT OUTSIDE THE CLOCK, and that is the rule of these studies
applied: a structure that can be filled while the file is read may be built
outside the clock.  Kruskal's algorithm needs no adjacency structure; what
it needs from the graph is its edges with their weights, and with parallel
edges already collapsed by the parser the most suitable NetworkX graph is
its plain Graph (a dict of dicts of edge-attribute dicts), filled one edge
at a time.  Here the Graph is filled from the parsed arrays rather than
from the file directly, the same work in the same place; that time is
build_ms.

PARALLEL EDGES ARE COLLAPSED BY THE PARSER, as in every driver of the study
(collapse_min in gr_read.py, dedup_ms): every unordered pair keeps its
cheapest arc, so the Graph
gets each edge once.

The clock is CPU time (user + system) over the whole process, getrusage, the
same quantity the other drivers read.  Wall time is recorded but nothing is
derived from it.

THE ANSWER IS CHECKED AFTER THE CLOCK with the driver's own union-find: no
returned edge may close a cycle, and the count must be n minus the number of
connected components of the graph (counted with SciPy's connected_components
over the arc arrays, so that the check on the largest instances does not run
into the cap).  The tree weight is reported for the cross-check between
solvers.
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
import networkx as nx
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components


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

    # ---- outside the clock: parse, collapse parallel edges, fill the Graph ----
    a0, b0 = cpu_ms()
    n, m, frm, to, w = parse_gr(args.instance)
    a1, b1 = cpu_ms()
    frm, to, w = collapse_min(n, frm, to, w)
    edges = int(frm.size)
    ad, bd = cpu_ms()
    try:
        G = nx.Graph()
        G.add_nodes_from(range(n))
        G.add_weighted_edges_from(zip(frm.tolist(), to.tolist(), w.tolist()))
    except MemoryError:
        sys.exit("MemoryError while building the Graph")
    a2, b2 = cpu_ms()
    setup = ["%.3f" % (a1 - a0 + b1 - b0), "%.3f" % (ad - a1 + bd - b1),
             "%.3f" % (a2 - ad + b2 - bd)]

    # the number of components of the whole graph, for the check
    comps = connected_components(
        coo_matrix((np.ones(frm.size, dtype=np.int8), (frm, to)), shape=(n, n)),
        directed=False, return_labels=False)

    for rep in range(1, args.repeats + 1):
        u0, y0 = cpu_ms()
        w0 = time.perf_counter()
        try:
            # ---- the measurement: Kruskal, drained ----
            tree = list(nx.minimum_spanning_edges(G, algorithm="kruskal",
                                                  weight="weight", data=True))
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
        wall = (w1 - w0) * 1000.0

        # ---- after the clock: check the tree ----
        parent = list(range(n))

        def find(i):
            while parent[i] != i:
                parent[i] = parent[parent[i]]
                i = parent[i]
            return i

        cnt, weight, ok = 0, 0, True
        for u, v, d in tree:
            cnt += 1
            ru, rv = find(u), find(v)
            if ru == rv:
                ok = False
            else:
                parent[ru] = rv
                weight += int(d["weight"])
        status = "SOLVED" if ok and cnt == n - comps else "BAD_TREE"

        emit([base, n, m, edges, rep, status, cnt, weight,
              "%.3f" % cpu, "%.3f" % usr, "%.3f" % sysr, "%.3f" % cpu,
              "%.3f" % wall] + setup + ["", "", args.tag], args.human)


if __name__ == "__main__":
    main()
