#!/usr/bin/env python3
"""Compute a maximum flow with SciPy's Dinic, timing the call.

Prints one CSV row, in exactly the column order the SML, Scala, Go, LEMON,
JGraphT and NetworkX drivers use, so every solver's rows sit in one table.

The entry point is

    scipy.sparse.csgraph.maximum_flow(csr, source, sink, method="dinic")

DINIC, NOT PUSH-RELABEL, AND DELIBERATELY SO.  SciPy ships no push-relabel at
all: scipy.sparse.csgraph.maximum_flow offers `edmonds_karp' and `dinic' and
nothing else.  Dinic is the faster of the two and is what this column reports,
so SciPy's column is a cross-ALGORITHM comparison where the other twelve are
cross-implementation.  That is worth having rather than leaving the cell
blank, and the AK family is where it is most interesting: Cherkassky and
Goldberg built that family so that push-relabel AND Dinic both grow roughly
quadratically on it, so the two algorithms meet there on equal terms.  The
`tag' column records `algorithm=dinic' on every row so that no reader of the
raw data mistakes this for a push-relabel figure.

Dinic is augmenting-path based, so unlike the preflow-push columns it has no
preflow stage to convert: what it ends with is a flow by construction.

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

PARALLEL ARCS NEED NO COLLAPSING HERE, and dedup_ms is an honest 0.000.
Building a CSR matrix from coordinates ADDS duplicate entries, and for a flow
problem a bundle of parallel arcs IS one arc of their combined capacity, so
SciPy's own build does the right thing at no extra cost.  NetworkX cannot and
has to be helped; this one does not.

CAPACITIES MUST BE int32.  maximum_flow refuses anything else outright
("graph capacities must be integers").  All three generators in this study
emit capacities well inside int32 -- genrmf and washington cap at 10,000 and
ak at 1,000,000 -- so nothing is rescaled or clipped, and the driver checks
rather than assumes.

The clock is CPU time (user + system) over the whole PROCESS, getrusage, the
same quantity every other driver in this study reports; thread_ms repeats it,
since this process does nothing else.  The pair exists for the JVM columns,
where the two differ by the cost of the JIT and of garbage collection.  Wall
time is recorded but nothing is derived from it.

THE VALUE IS READ AFTER THE CLOCK, as a cross-reference and nothing more; the
measurement is the flow computation alone, with no summing up inside it.

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
from max_read import HEADER, cpu_ms, emit, limit_memory, parse_max

import numpy as np
import scipy.sparse as sp
from scipy.sparse.csgraph import maximum_flow


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
    ap.add_argument("--memory-gb", type=float, default=0.0)
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
    if cap.max() > np.iinfo(np.int32).max:
        sys.exit("a capacity does not fit in int32; SciPy would refuse it")

    # ---- 2. the constructor's arrays; the CSR build is in the clock ----
    u0, s0 = cpu_ms()
    cap32 = cap.astype(np.int32)
    u1, s1 = cpu_ms()
    build_ms = (u1 - u0) + (s1 - s0)

    tag = args.tag + (";" if args.tag else "") + "algorithm=dinic"

    for rep in range(1, args.repeats + 1):
        # ---- 3. clock ----
        w0 = time.monotonic()
        u0, s0 = cpu_ms()

        # ---- 4. build the CSR matrix, then the library ----
        csr = sp.coo_matrix((cap32, (frm, to)), shape=(n, n)).tocsr()
        res = maximum_flow(csr, src, snk, method="dinic")

        # ---- 5. clock ----
        u1, s1 = cpu_ms()
        w1 = time.monotonic()

        usr, sysd = u1 - u0, s1 - s0
        cpu = usr + sysd
        wall = (w1 - w0) * 1000.0

        # ---- 6. the answer, after the clock ----
        value = int(res.flow_value)
        f = res.flow.tocoo()
        pos = f.data > 0
        net = np.zeros(n, dtype=np.int64)
        np.add.at(net, f.row[pos], -f.data[pos].astype(np.int64))
        np.add.at(net, f.col[pos], f.data[pos].astype(np.int64))
        status = "OK"
        inner = np.ones(n, dtype=bool)
        inner[src] = inner[snk] = False
        if net[inner].any():
            status = "NOT_A_FLOW"
        elif -net[src] != value:
            status = "VALUE_MISMATCH"

        emit([base, n, m, "scipy_dinic", src + 1, snk + 1, rep, status, value,
              "%.3f" % cpu, "%.3f" % usr, "%.3f" % sysd, "%.3f" % cpu,
              "%.3f" % wall, "%.3f" % parse_ms, "0.000",
              "%.3f" % build_ms, tag], human=args.human)

    return 0


if __name__ == "__main__":
    sys.exit(main())
