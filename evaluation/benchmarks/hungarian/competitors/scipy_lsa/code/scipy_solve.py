#!/usr/bin/env python3
"""Solve a DIMACS .asn instance with SciPy, timing the solver call -- and, for
the sparse solver, the CSR build in front of it.

Prints one CSV row in exactly the column order the SML driver uses, so the
two solvers' results can sit in the same table and be read by the same
table builder.

Two SciPy entry points are offered:

  --solver dense    scipy.optimize.linear_sum_assignment  (the default)
                    The assignment solver, on a full cost matrix.  Natural
                    for the geometric family, which is complete anyway.  On
                    a sparse instance the absent arcs must be entered as a
                    cost high enough that no cheapest perfect matching would
                    ever pick one, so SciPy is handed a complete graph where
                    the SML solver is handed only the arcs that exist.  That
                    is recorded in the tag, not hidden.

  --solver sparse   scipy.sparse.csgraph.min_weight_full_bipartite_matching
                    The same problem on the same sparse input the SML solver
                    gets, so it is the like-for-like reading on the two
                    sparse families.  Refuses the instance outright if no
                    perfect matching exists.

Both are shortest-augmenting-path methods with dual potentials, the family
the Hungarian method belongs to.

WHAT IS CLOCKED.  The rule of this study: a
solver gets its faster structure; a structure that can be filled arc by arc
while the file is read may be built outside the clock; one that needs the
complete arc list first is built after parsing, and that build is the first
part of the clocked period.  The dense matrix is of the first kind -- n is on
the p line, and a cell can be set as each arc line is read -- so its fill
stays outside.  The CSR matrix is of the second kind: csr_matrix((w, (rows,
cols))) is a sort-and-pack pass over the complete arrays, so for --solver
sparse the clock opens on the parsed arrays and covers the CSR build and the
solver call, nothing else.  The scipy_mwfbm_prebuilt column of the published
results built the CSR before the clock.
"""

import os

# Set before numpy is imported.  Nothing here uses BLAS, but a stray threaded
# BLAS would put time on cores this run was not given, and CPU time counts
# every thread of the process.
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import argparse
import resource
import sys
import time

import numpy as np
import scipy
from scipy.optimize import linear_sum_assignment
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import min_weight_full_bipartite_matching


def parse_asn(path):
    """Read a DIMACS assignment instance.  Outside the clock."""
    n_nodes = n_arcs = 0
    left_flag = None
    src = []
    dst = []
    cost = []
    with open(path, "rb") as fh:
        for line in fh:
            if not line:
                continue
            k = line[0:1]
            if k == b"a":
                f = line.split()
                src.append(int(f[1]))
                dst.append(int(f[2]))
                cost.append(int(f[3]))
            elif k == b"n":
                left_flag[int(line.split()[1])] = True
            elif k == b"p":
                f = line.split()
                n_nodes = int(f[2])
                n_arcs = int(f[3])
                left_flag = np.zeros(n_nodes + 2, dtype=bool)
            elif k in (b"c", b"\n", b"\r"):
                continue
    src = np.asarray(src, dtype=np.int64)
    dst = np.asarray(dst, dtype=np.int64)
    cost = np.asarray(cost, dtype=np.int64)

    # Some generators mark the left side with 'n' lines, some leave it
    # implicit in the arc tails.  Either way the tails are the left side.
    if left_flag is None or not left_flag.any():
        left = np.unique(src)
    else:
        left = np.flatnonzero(left_flag)
    right = np.unique(dst)
    return n_nodes, n_arcs, src, dst, cost, left, right


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--solver", choices=("dense", "sparse"), default="dense")
    ap.add_argument("--tag", default="")
    ap.add_argument("--csv", action="store_true")
    args = ap.parse_args()

    n_nodes, n_arcs, src, dst, cost, left, right = parse_asn(args.path)
    n_left = left.size
    n_right = right.size

    # ---- input marshalling: before the clock ----
    # Compact the vertex ids down to 0..n_left-1 and 0..n_right-1.
    row_of = np.full(int(max(src.max(), left.max())) + 1, -1, dtype=np.int64)
    row_of[left] = np.arange(n_left)
    col_of = np.full(int(max(dst.max(), right.max())) + 1, -1, dtype=np.int64)
    col_of[right] = np.arange(n_right)
    rows = row_of[src]
    cols = col_of[dst]

    # A stored zero is indistinguishable from an absent arc in a sparse
    # matrix, so if any arc costs nothing, lift every cost by one.  Every
    # perfect matching uses exactly n_left arcs, so a uniform lift moves all
    # objective values by the same constant and cannot change which matching
    # is cheapest.  The constant is taken back off the reported cost.
    shift = 1 if cost.size and cost.min() <= 0 else 0
    w = (cost + shift).astype(np.float64)

    if args.solver == "sparse":
        # THE CSR BUILD IS INSIDE THE CLOCK: the matrix is made between the
        # clock reads below, from the arrays that are ready here.  See the
        # module docstring.
        payload = None
    else:
        # A dense matrix could be filled arc by arc while the file is read,
        # so its fill sits outside the clock.
        # One arc more expensive than any whole perfect matching built from
        # real arcs, so a cheapest assignment picks a fake arc only when no
        # perfect matching exists at all.  Kept small enough that every sum
        # stays an exact float64 integer.
        big = float(n_left) * float(w.max()) + 1.0
        m = np.full((n_left, n_right), big, dtype=np.float64)
        m[rows, cols] = w
        payload = m

    # ---- clock ----
    ru0 = resource.getrusage(resource.RUSAGE_SELF)
    t0 = time.perf_counter()

    status = "OPTIMAL"
    try:
        if args.solver == "sparse":
            payload = csr_matrix((w, (rows, cols)), shape=(n_left, n_right))
            ri, ci = min_weight_full_bipartite_matching(payload)
        else:
            ri, ci = linear_sum_assignment(payload)
    except ValueError:
        status = "NO_PERFECT_MATCHING"
        ri = ci = np.empty(0, dtype=np.int64)

    t1 = time.perf_counter()
    ru1 = resource.getrusage(resource.RUSAGE_SELF)
    # ---- clock ----

    if args.solver == "sparse" and payload is not None and payload.nnz != n_arcs:
        # Parallel arcs got summed, or a zero was pruned.  Either would
        # silently change the instance, so stop rather than report a
        # number for a problem that is not the one on disk.
        sys.stderr.write(
            "refusing to run: matrix holds %d entries for %d arcs\n"
            % (payload.nnz, n_arcs))
        sys.exit(3)

    wall_ms = (t1 - t0) * 1000.0
    usr_ms = (ru1.ru_utime - ru0.ru_utime) * 1000.0
    sys_ms = (ru1.ru_stime - ru0.ru_stime) * 1000.0
    cpu_ms = usr_ms + sys_ms

    matched = int(ri.size)
    if status == "OPTIMAL" and (matched != n_left or n_left != n_right):
        status = "NO_PERFECT_MATCHING"
    if status == "OPTIMAL":
        sel = payload[ri, ci]
        if hasattr(sel, "toarray"):
            sel = sel.toarray()
        chosen = np.asarray(sel).ravel()
        if args.solver == "dense" and chosen.max() >= big:
            # A fake arc was used, so the real graph has no perfect matching.
            status = "NO_PERFECT_MATCHING"
            cost_str = "NA"
        else:
            cost_str = str(int(round(chosen.sum())) - shift * matched)
    else:
        cost_str = "NA"

    base = os.path.basename(args.path)
    if args.csv:
        print(",".join([
            base, str(n_nodes), str(n_arcs), str(n_left), str(n_right),
            "0", "0.000", status, str(matched), cost_str,
            "%.3f" % cpu_ms, "%.3f" % usr_ms, "%.3f" % sys_ms,
            "%.3f" % wall_ms, args.tag]))
    else:
        print("instance   %s" % base)
        print("solver     scipy %s / %s" % (scipy.__version__, args.solver))
        print("nodes      %d (|X| = %d, |Y| = %d)" % (n_nodes, n_left, n_right))
        print("arcs       %d" % n_arcs)
        print("status     %s" % status)
        print("matched    %d" % matched)
        print("cost       %s" % cost_str)
        print("cpu        %.3f ms   (the measurement)" % cpu_ms)
        print("cpu user   %.3f ms" % usr_ms)
        print("cpu sys    %.3f ms" % sys_ms)
        print("wall       %.3f ms" % wall_ms)


if __name__ == "__main__":
    main()
