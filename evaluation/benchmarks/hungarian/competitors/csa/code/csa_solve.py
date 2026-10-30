#!/usr/bin/env python3
"""Run the DIMACS reference solver CSA on a .asn instance and print one CSV row.

CSA is the Goldberg-Kennedy cost-scaling push-relabel assignment code, the
reference solver the 13th DIMACS Implementation Challenge (Network Flows 2.0)
names on its "Assignment Problem Reference Solvers" page.  It is a standalone C
program that reads the instance from standard input, so the timing cannot be
taken from out here -- the clock lives inside the program, added by
build_csa.sh.  It starts inside parse(),
immediately before CSA packs the arc list it has read into its own per-node
arc arrays (a counting sort over the complete list: a structure built after
parsing, whose build is the first part of the clocked period in this study),
and stops immediately after the scaling loop; reading the arc lines and
computing the objective are outside.  This wrapper only feeds the program the
instance and reformats what it prints.

The row has the same columns, in the same order, as scipy_solve.py,
ortools_solve.py and JGraphTSolve.java.
"""

import argparse
import os
import re
import subprocess
import sys
import time


def header(path):
    """Problem size, from the 'p' line and the count of 'n' lines.

    Outside the clock, and outside the solver process entirely.
    """
    n_nodes = n_arcs = n_left = 0
    with open(path, "rb") as fh:
        for line in fh:
            k = line[0:1]
            if k == b"n":
                n_left += 1
            elif k == b"p":
                f = line.split()
                n_nodes, n_arcs = int(f[2]), int(f[3])
    if n_left == 0:
        n_left = n_nodes // 2
    return n_nodes, n_arcs, n_left, n_nodes - n_left


COST_RE = re.compile(rb"\|>\s+cost\s+(-?\d+)")
MEAS_RE = re.compile(rb"MEASURE cpu_ms=([\d.]+) usr_ms=([\d.]+) sys_ms=([\d.]+)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--binary", default=None,
                    help="CSA variant to run (default reference/csa/build/csa_s)")
    ap.add_argument("--timeout", type=float, default=None)
    ap.add_argument("--tag", default="")
    ap.add_argument("--csv", action="store_true")
    args = ap.parse_args()

    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    binary = args.binary or os.path.join(root, "reference", "csa", "build", "csa_s")
    if not os.path.exists(binary):
        sys.exit("missing CSA binary: %s (run build_csa.sh)" % binary)

    n_nodes, n_arcs, n_left, n_right = header(args.path)

    status = "OPTIMAL"
    cost_str = "NA"
    cpu_ms = usr_ms = sys_ms = 0.0
    matched = 0

    w0 = time.perf_counter()
    try:
        with open(args.path, "rb") as fh:
            p = subprocess.run([binary], stdin=fh, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, timeout=args.timeout)
        out = p.stdout
    except subprocess.TimeoutExpired:
        out = b""
        status = "TIMEOUT"
    w1 = time.perf_counter()
    wall_ms = (w1 - w0) * 1000.0   # whole process, for reference only

    if status == "OPTIMAL":
        mc = COST_RE.search(out)
        mm = MEAS_RE.search(out)
        if mc is None or mm is None:
            status = "ERROR"
            sys.stderr.write(out.decode("utf-8", "replace"))
        else:
            cost_str = mc.group(1).decode()
            cpu_ms = float(mm.group(1))
            usr_ms = float(mm.group(2))
            sys_ms = float(mm.group(3))
            matched = n_left

    base = os.path.basename(args.path)
    variant = os.path.basename(binary)
    if args.csv:
        print(",".join([
            base, str(n_nodes), str(n_arcs), str(n_left), str(n_right),
            "0", "0.000", status, str(matched), cost_str,
            "%.3f" % cpu_ms, "%.3f" % usr_ms, "%.3f" % sys_ms,
            "%.3f" % wall_ms, args.tag]))
    else:
        print("instance   %s" % base)
        print("solver     csa / %s" % variant)
        print("nodes      %d (|X| = %d, |Y| = %d)" % (n_nodes, n_left, n_right))
        print("arcs       %d" % n_arcs)
        print("status     %s" % status)
        print("matched    %d" % matched)
        print("cost       %s" % cost_str)
        print("cpu        %.3f ms   (the measurement)" % cpu_ms)
        print("cpu user   %.3f ms" % usr_ms)
        print("cpu sys    %.3f ms" % sys_ms)
        print("wall       %.3f ms   (whole process, reference only)" % wall_ms)


if __name__ == "__main__":
    main()
