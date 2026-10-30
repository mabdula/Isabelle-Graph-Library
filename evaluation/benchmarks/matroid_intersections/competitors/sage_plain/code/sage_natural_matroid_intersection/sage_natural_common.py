"""Shared solver code of the plain Sage matroid intersection scripts for bipartite (b-)matching.

This is the baseline a Sage user would write without any knowledge of our verified code: the
two matroids are built with Sage's own constructors, and every query of the intersection
routines (closure, circuit, independence) is answered by Sage's generic implementations on
top of the rank function of the matroid.

Instances are read by the study's own reader, bench/asn_reader.py, which also documents the
format; nothing here parses.

The ground set is the set of edges, numbered in input order. The instance is the intersection
of two partition matroids: the blocks of the left matroid are the edges at a left vertex,
those of the right matroid the edges at a right vertex.

- Matching: Sage's built-in PartitionMatroid (sage.matroids.union_matroid), at most one
  element per block.
- b-matching: Sage has no partition matroid with capacities, so the matroid is given by its
  rank function, r(X) = sum over blocks B of min(cap(B), |X & B|), through
  Matroid(groundset=..., rank_function=...), which yields a RankMatroid.

The unweighted problems use Sage's intersection_unweighted (maximum cardinality), the weighted
ones Sage's intersection (maximum weight, not necessarily of maximum cardinality). Arc values
are weights to be maximised.

The measured time is the process CPU time (time.process_time) from just before the call to
Sage's intersection routine until just after it returns; reading the instance, building the
matroids and checking the result are not included.
"""

from collections import Counter, defaultdict

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))  # package: asn_reader.py beside run_sage.py (the study had it in bench/)
from asn_reader import InstanceError, read_instance  # the study's reader; never on the clock

try:  # initialise Sage before importing submodules: full Sage, or modular passagemath-modules
    import sage.all  # noqa: F401
except ImportError:
    import sage.all__sagemath_modules  # noqa: F401
from sage.matroids.constructor import Matroid
from sage.matroids.union_matroid import PartitionMatroid


def blocks(ends):
    """The blocks of one side: for every vertex, the list of the edges at it."""
    B = defaultdict(list)
    for e, x in enumerate(ends):
        B[x].append(e)
    return list(B.values())


def capacity_rank(ends, cap):
    """The rank function of the partition matroid with capacities of one side."""
    def rank(X):
        return sum(min(k, cap(x)) for x, k in Counter(ends[e] for e in X).items())
    return rank


def build_matroids(edges, caps, capacities):
    """The left and the right partition matroid on range(len(edges))."""
    left, right = [u for u, _ in edges], [v for _, v in edges]
    if not capacities:
        return PartitionMatroid(blocks(left)), PartitionMatroid(blocks(right))
    E = range(len(edges))
    cap = lambda x: caps.get(x, 1)
    return (Matroid(groundset=E, rank_function=capacity_rank(left, cap)),
            Matroid(groundset=E, rank_function=capacity_rank(right, cap)))


def solve(path, weighted, capacities):
    """Solve the instance in `path` and return (size, weight, cpu_seconds). Without
    `capacities`, every capacity must be 1. Exits on malformed input or if Sage's result is not
    a common independent set."""
    try:
        nodes, edges, weights, caps = read_instance(path)
    except (InstanceError, OSError) as e:
        sys.exit(f"error: {e}")
    if not capacities and any(c != 1 for c in caps.values()):
        sys.exit("error: capacities other than 1 in a matching instance")
    M1, M2 = build_matroids(edges, caps, capacities)
    wt = dict(enumerate(weights))

    if weighted:
        start = time.process_time()
        sol = M1.intersection(M2, wt)
        end = time.process_time()
    else:
        start = time.process_time()
        sol = M1.intersection_unweighted(M2)
        end = time.process_time()

    if not (M1.is_independent(sol) and M2.is_independent(sol)):
        sys.exit("error: Sage returned a set that is not a common independent set")
    return len(sol), sum(weights[e] for e in sol), end - start


def main(weighted, capacities):
    """Command line entry of the four problem scripts: print the measured CPU seconds."""
    if len(sys.argv) != 2:
        sys.exit(f"usage: {sys.argv[0]} INSTANCE")
    print(f"{solve(sys.argv[1], weighted, capacities)[2]:.6f}")
