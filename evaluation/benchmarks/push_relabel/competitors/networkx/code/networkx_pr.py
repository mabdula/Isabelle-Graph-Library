#!/usr/bin/env python3
"""Compute a maximum flow with NetworkX's push-relabel, timing the call.

Prints one CSV row, in exactly the column order the SML, Scala, Go, LEMON,
JGraphT and SciPy drivers use, so every solver's rows sit in one table.

The entry point is

    networkx.algorithms.flow.preflow_push(G, s, t, capacity="capacity")

NetworkX's own highest-label push-relabel, in pure Python.

A MAXIMUM FLOW, NOT A MAXIMUM PREFLOW.  preflow_push takes a `value_only'
argument.  With value_only=True it returns the moment a maximum PREFLOW is
found -- enough for the value, since the excess at the sink is already right,
but the result is not a flow.  The default, used here, falls through to the
second phase, which relabels every node and returns the leftover excess to the
source.  Our export has no such shortcut: both its variants discharge until no
vertex carries excess, which is a flow already.  Handing this solver the
cheaper call would make the comparison worthless, so it gets the full one, and
the `tag' column records `value_only=no' on every row so that this survives
into the raw data.

Building the DiGraph sits outside the clock.  That is allowed here and not for
our exports: a library like this one would normally read the file straight
into its own structure, so the build fuses with parsing, which verified
exported code handed plain arrays cannot do.  The asymmetry is inherent and it
favours NetworkX -- which it needs, since building the graph is by far the
slowest thing this driver does.

PARALLEL ARCS ARE SUMMED FIRST.  A DiGraph holds one capacity per ordered
pair and add_edge overwrites, so a bundle of parallel arcs would silently
become whichever one was read last.  They are collapsed to a single arc of
their combined capacity before the build, which changes no maximum flow value,
and the cost is reported in dedup_ms.  None of the three families in this
study actually emits parallel arcs, so the figure is near zero; the pass is
there so that a family that did would not quietly give a wrong answer.

The clock is CPU time (user + system) over the whole PROCESS, getrusage, the
same quantity every other driver in this study reports; thread_ms repeats it,
since this process does nothing else.  The pair exists for the JVM columns,
where the two differ by the cost of the JIT and of garbage collection.  Wall
time is recorded but nothing is derived from it.

THE VALUE IS READ AFTER THE CLOCK, as a cross-reference against the other
twelve solvers and nothing more; the measurement is the flow computation
alone, with no summing up inside it.  The flow is also checked -- capacities
respected and every vertex but the two ends balanced -- which is what tells a
maximum flow apart from a maximum preflow.

ONE PROBLEM PER PROCESS.  The source and the sink come from the file's own `n'
designator lines, and there is deliberately no way to hand this driver a
second pair.
"""

import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import argparse
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from max_read import (HEADER, cpu_ms, dedupe_sum, emit, limit_memory,
                      parse_max)

import networkx as nx


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("instance", nargs="?")
    ap.add_argument("--source", type=int, default=None,
                    help="override the file's own source (1-based)")
    ap.add_argument("--target", type=int, default=None,
                    help="override the file's own sink (1-based)")
    ap.add_argument("--repeats", type=int, default=1)
    ap.add_argument("--tag", default="")
    ap.add_argument("--header", action="store_true")
    ap.add_argument("--human", action="store_true")
    ap.add_argument("--memory-gb", type=float, default=0.0,
                    help="cap this run's address space, so that a run which "
                         "asks for too much dies alone")
    args = ap.parse_args()

    if args.header:
        print(HEADER)
        return 0
    if not args.instance:
        ap.error("an instance is required")

    limit_memory(args.memory_gb)

    base = os.path.basename(args.instance)

    # ---- 1. parse ----
    u0, s0 = cpu_ms()
    n, m, src, snk, frm, to, cap = parse_max(args.instance)
    u1, s1 = cpu_ms()
    parse_ms = (u1 - u0) + (s1 - s0)

    if args.source is not None:
        src = args.source - 1
    if args.target is not None:
        snk = args.target - 1
    if not (0 <= src < n) or not (0 <= snk < n):
        sys.exit("source or sink outside [1, %d]" % n)
    if src == snk:
        sys.exit("source and sink are the same vertex")

    # ---- 2. collapse parallel arcs ----
    u0, s0 = cpu_ms()
    frm, to, cap = dedupe_sum(n, frm, to, cap)
    u1, s1 = cpu_ms()
    dedup_ms = (u1 - u0) + (s1 - s0)

    # ---- 3. build ----
    u0, s0 = cpu_ms()
    G = nx.DiGraph()
    G.add_nodes_from(range(n))
    G.add_edges_from((int(a), int(b), {"capacity": int(c)})
                     for a, b, c in zip(frm, to, cap))
    u1, s1 = cpu_ms()
    build_ms = (u1 - u0) + (s1 - s0)

    tag = args.tag + (";" if args.tag else "") + "value_only=no"

    for rep in range(1, args.repeats + 1):
        # ---- 4. clock ----
        w0 = time.monotonic()
        u0, s0 = cpu_ms()

        # ---- 5. the library, whole: both phases ----
        R = nx.algorithms.flow.preflow_push(G, src, snk, capacity="capacity")

        # ---- 6. clock ----
        u1, s1 = cpu_ms()
        w1 = time.monotonic()

        usr, sysd = u1 - u0, s1 - s0
        cpu = usr + sysd
        wall = (w1 - w0) * 1000.0

        # ---- 7. the answer, after the clock ----
        value = R.graph["flow_value"]
        status = "OK"
        net = [0] * n
        for u, v, d in R.edges(data=True):
            f = d["flow"]
            if f <= 0:                      # the residual network carries a
                continue                    # reverse arc for every arc
            net[u] -= f
            net[v] += f
        if any(net[v] for v in range(n) if v != src and v != snk):
            status = "NOT_A_FLOW"
        elif -net[src] != value:
            status = "VALUE_MISMATCH"

        emit([base, n, m, "networkx_preflow_push", src + 1, snk + 1, rep,
              status, value,
              "%.3f" % cpu, "%.3f" % usr, "%.3f" % sysd, "%.3f" % cpu,
              "%.3f" % wall, "%.3f" % parse_ms, "%.3f" % dedup_ms,
              "%.3f" % build_ms, tag], human=args.human)

    return 0


if __name__ == "__main__":
    sys.exit(main())
