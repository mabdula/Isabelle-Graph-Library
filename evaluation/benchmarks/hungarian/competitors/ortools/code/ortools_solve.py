#!/usr/bin/env python3
"""Solve a DIMACS .asn instance with Google OR-Tools, timing only the solver call.

OR-Tools is the second solver the challenge names on its "Assignment Problem
Reference Solvers" page, where it is described as an implementation of the same
CSA algorithm as the Goldberg-Kennedy reference code.  Its assignment entry
point takes an arc list, so it is handed exactly the arcs that exist -- the
like-for-like reading, as with scipy's sparse solver and unlike scipy's dense
one, which has to be handed a completed graph.

Prints one CSV row in the same column order as scipy_solve.py and
JGraphTSolve.java, so all the reference solvers land in one table.

Like the other reference drivers this makes a warm-up call before the measured
one, so that library loading and any first-call setup sit outside the clock.

Arcs are added one at a time rather than through the bulk add_arcs_with_cost
entry point.  Both build the same problem and the solve itself is identical,
and arc marshalling is outside the clock for every solver in this study -- but
the bulk path spawns a three-thread pool at add time, and those threads spin
before they park, so their spin-down lands inside the first measured window and
reads as 5x the CPU of the solve (22.7 ms against a 4.1 ms solve, measured).
The per-arc path never starts a thread, so the process stays single-threaded
and the measurement is of the solver and nothing else.  Measured both ways on
low-cost n=2048: same cost, same solve time to within noise.
"""

import argparse
import os
import resource
import sys
import time

import ortools
from ortools.graph.python import linear_sum_assignment


def parse_asn(path):
    """Read a DIMACS assignment instance.  Outside the clock."""
    n_nodes = n_arcs = 0
    left_flag = set()
    src, dst, cost = [], [], []
    with open(path, "rb") as fh:
        for line in fh:
            k = line[0:1]
            if k == b"a":
                f = line.split()
                src.append(int(f[1])); dst.append(int(f[2])); cost.append(int(f[3]))
            elif k == b"n":
                left_flag.add(int(line.split()[1]))
            elif k == b"p":
                f = line.split()
                n_nodes = int(f[2]); n_arcs = int(f[3])
    left = sorted(left_flag) if left_flag else sorted(set(src))
    right = sorted(set(dst))
    return n_nodes, n_arcs, src, dst, cost, left, right


def warm_up():
    """Solve a small instance so library setup is not on the clock."""
    s = linear_sum_assignment.SimpleLinearSumAssignment()
    n = 8
    for i in range(n):
        for j in range(n):
            s.add_arc_with_cost(i, j, (i * 7 + j * 13) % 11 + 1)
    s.solve()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--tag", default="")
    ap.add_argument("--csv", action="store_true")
    args = ap.parse_args()

    n_nodes, n_arcs, src, dst, cost, left, right = parse_asn(args.path)
    n_left, n_right = len(left), len(right)

    # ---- input marshalling: before the clock ----
    row_of = {v: i for i, v in enumerate(left)}
    col_of = {v: i for i, v in enumerate(right)}
    rows = [row_of[v] for v in src]
    cols = [col_of[v] for v in dst]

    solver = linear_sum_assignment.SimpleLinearSumAssignment()
    for r, c, w in zip(rows, cols, cost):
        solver.add_arc_with_cost(r, c, w)

    warm_up()

    # ---- clock ----
    ru0 = resource.getrusage(resource.RUSAGE_SELF)
    t0 = time.perf_counter()

    rc = solver.solve()

    t1 = time.perf_counter()
    ru1 = resource.getrusage(resource.RUSAGE_SELF)
    # ---- clock ----

    wall_ms = (t1 - t0) * 1000.0
    usr_ms = (ru1.ru_utime - ru0.ru_utime) * 1000.0
    sys_ms = (ru1.ru_stime - ru0.ru_stime) * 1000.0
    cpu_ms = usr_ms + sys_ms

    if rc == solver.OPTIMAL:
        status = "OPTIMAL"
        matched = solver.num_nodes()
        cost_str = str(solver.optimal_cost())
    elif rc == solver.INFEASIBLE:
        status, matched, cost_str = "NO_PERFECT_MATCHING", 0, "NA"
    else:
        status, matched, cost_str = "ERROR_%d" % rc, 0, "NA"

    base = os.path.basename(args.path)
    if args.csv:
        print(",".join([
            base, str(n_nodes), str(n_arcs), str(n_left), str(n_right),
            "0", "0.000", status, str(matched), cost_str,
            "%.3f" % cpu_ms, "%.3f" % usr_ms, "%.3f" % sys_ms,
            "%.3f" % wall_ms, args.tag]))
    else:
        print("instance   %s" % base)
        print("solver     ortools %s / linear_sum_assignment" % ortools.__version__)
        print("nodes      %d (|X| = %d, |Y| = %d)" % (n_nodes, n_left, n_right))
        print("arcs       %d" % n_arcs)
        print("status     %s" % status)
        print("matched    %d" % matched)
        print("cost       %s" % cost_str)
        print("cpu        %.3f ms   (the measurement)" % cpu_ms)
        print("wall       %.3f ms" % wall_ms)


if __name__ == "__main__":
    main()
