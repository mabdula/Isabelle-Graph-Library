"""Shared solver code of the Sage matroid intersection scripts for bipartite (b-)matching.

Instances are read by the study's own reader, bench/asn_reader.py, which also documents the
format; nothing here parses.

The instance is the intersection of two partition matroids on the edges: the blocks of the
left matroid are the edges at a left vertex, those of the right matroid the edges at a right
vertex, and a block may contain at most as many elements as the capacity of its vertex.
Each matroid answers Sage's queries with a Python transcription of the verified oracle of
our Isabelle instance: the unit partition oracle (Partition_Oracle_Imp) for matching, the
partition oracle with capacities (Capacity_Partition_Oracle_Imp) for b-matching; see
OracleMatroid for how Sage's set queries are built from the oracle's tests.

The unweighted problems use Sage's intersection_unweighted (Cunningham's blocking-flow
algorithm, maximum cardinality). The weighted problems use Sage's intersection, which computes
a maximum-weight common independent set, i.e. a maximum-weight (b-)matching that need not have
maximum cardinality. Arc values are weights to be maximised.

The measured time is the process CPU time (time.process_time) from just before the call to
Sage's intersection routine until just after it returns; reading the instance, building the
matroids and checking the result are not included.
"""

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))  # package: asn_reader.py beside run_sage.py (the study had it in bench/)
from asn_reader import InstanceError, read_instance  # the study's reader; never on the clock

try:  # initialise Sage before importing submodules: full Sage, or modular passagemath-modules
    import sage.all  # noqa: F401
except ImportError:
    import sage.all__sagemath_modules  # noqa: F401
from sage.matroids.matroid import Matroid


def part_handle(n, nb, Bl):
    """part_handle_imp: for every element, the ascending list of the elements of its block
    (the lists of one block are shared), built in time O(n + nb)."""
    Kb = [[] for _ in range(nb)]
    for i in range(n):
        Kb[Bl[i]].append(i)
    return [Kb[Bl[i]] for i in range(n)]


class UnitPartitionOracle:
    """The verified unit partition oracle of one side (Partition_Oracle_Imp). Bl is the array of
    blocks, C the array counting the solution elements per block, Kx the partner lists."""

    def __init__(self, n, nb, Bl):
        self.Bl = Bl
        self.C = [0] * nb
        self.Kx = part_handle(n, nb, Bl)

    def cnt_ins(self, i):
        """part_cnt_ins"""
        b = self.Bl[i]
        self.C[b] += 1

    def cnt_del(self, i):
        """part_cnt_del"""
        b = self.Bl[i]
        self.C[b] -= 1

    def ins(self, y):
        """part_ins_imp: may y (outside the solution) be inserted?"""
        return self.C[self.Bl[y]] == 0

    def exch(self, x, y):
        """part_exch_imp: may y (outside the solution, not insertable) replace x (inside)?"""
        return self.Bl[x] == self.Bl[y]

    def pts(self, x):
        """The exchange partners of x: the elements of its block."""
        return self.Kx[x]


class CapPartitionOracle(UnitPartitionOracle):
    """The verified partition oracle with capacities (Capacity_Partition_Oracle_Imp): counters,
    blocks, exchange queries and partners of the unit case, and the capacity array Ka."""

    def __init__(self, n, nb, Bl, Ka):
        super().__init__(n, nb, Bl)
        self.Ka = Ka

    def ins(self, y):
        """part_cap_ins_imp"""
        b = self.Bl[y]
        return self.C[b] < self.Ka[b]


class OracleMatroid(Matroid):
    """A Sage matroid on range(n) answering Sage's queries with one of the verified oracles.

    It holds a solution S like the solution handle of the verified code: the Boolean array Xi
    (bm_memb) and the counters of the oracle, changed only by sol_ins and sol_del (bm_ins and
    bm_del). S is always independent: elements are inserted only after a positive insertion
    test. Sage's queries are answered by the tests of the verified code on S:

    - independence of S + a - r (at most one element added, at most one removed): an insertion
      test on a, and if it fails, an exchange test between r and a;
    - closure of S: S and every other element failing the insertion test, one pass over all
      elements, like the scan for sources and targets in the verified code; it is kept until S
      changes;
    - closure of S - y: the closure of S without y and without the exchange partners x of y
      passing the filter nb1_imp (x outside S, not insertable, exchangeable with y);
    - circuit of S + u (u not insertable): u and the exchange partners y of u passing the filter
      nb2_imp (y in S, u exchangeable with y).

    Any other set X becomes the solution first: the elements of S - X are deleted, and those of
    X - S inserted if they pass the insertion test, as in an augmentation; S is then a maximal
    independent subset of X, which gives the rank, independence, closure and a circuit of X.
    Sage hands over and expects whole sets, so building and comparing them is Sage's share."""

    def __init__(self, n, orcl):
        self._n = n
        self._groundset = frozenset(range(n))
        self._o = orcl
        self._Xi = [False] * n
        self._S = set()
        self._cl = None

    def groundset(self):
        return self._groundset

    def _sol_ins(self, x):
        """bm_ins"""
        if not self._Xi[x]:
            self._Xi[x] = True
            self._S.add(x)
            self._o.cnt_ins(x)
            self._cl = None

    def _sol_del(self, x):
        """bm_del"""
        if self._Xi[x]:
            self._Xi[x] = False
            self._S.discard(x)
            self._o.cnt_del(x)
            self._cl = None

    def _near(self, X):
        """(X - S, S - X) if both have at most one element, else None."""
        S = self._S
        if abs(len(X) - len(S)) <= 1:
            add = X - S
            if len(add) <= 1:
                rem = S - X
                if len(rem) <= 1:
                    return add, rem
        return None

    def _move_to(self, X):
        """Make a maximal independent subset of X containing S & X the solution."""
        for x in self._S - X:
            self._sol_del(x)
        for x in X - self._S:
            if self._o.ins(x):
                self._sol_ins(x)

    def _closure_S(self):
        if self._cl is None:
            Xi, o = self._Xi, self._o
            self._cl = frozenset(e for e in range(self._n) if Xi[e] or not o.ins(e))
        return self._cl

    def _rank(self, X):
        self._move_to(X)
        return len(self._S)

    def _is_independent(self, X):
        d = self._near(X)
        if d is None:
            self._move_to(X)
            return len(self._S) == len(X)
        add, rem = d
        if not add:
            return True
        a = next(iter(add))
        if self._o.ins(a):
            return True
        return bool(rem) and self._o.exch(next(iter(rem)), a)

    def _closure(self, X):
        d = self._near(X)
        if d is not None and not d[0] and d[1]:
            y = next(iter(d[1]))
            Xi, o = self._Xi, self._o
            drop = [x for x in o.pts(y) if not Xi[x] and not o.ins(x) and o.exch(y, x)]
            return self._closure_S().difference(drop, (y,))
        if d is None or d[0]:
            self._move_to(X)
        return self._closure_S()

    def _circuit(self, X):
        d = self._near(X)
        if d is not None and d[0] and not d[1]:
            u = next(iter(d[0]))
            if self._o.ins(u):
                raise ValueError("no circuit in independent set.")
        else:
            self._move_to(X)
            u = next(iter(X - self._S), None)
            if u is None:
                raise ValueError("no circuit in independent set.")
        Xi, o = self._Xi, self._o
        return frozenset([u] + [y for y in o.pts(u) if Xi[y] and o.exch(y, u)])


def solve(path, weighted, capacities):
    """Solve the instance in `path` and return (size, weight, cpu_seconds). Without
    `capacities`, every capacity must be 1 and the unit partition oracle is used; with them, the
    partition oracle with capacities. Exits on malformed input or if Sage's result is not a
    common independent set."""
    try:
        nodes, edges, weights, caps = read_instance(path)
    except (InstanceError, OSError) as e:
        sys.exit(f"error: {e}")
    if not capacities and any(c != 1 for c in caps.values()):
        sys.exit("error: capacities other than 1 in a matching instance")
    m, nb = len(edges), nodes + 1
    Fa, Ta = [u for u, _ in edges], [v for _, v in edges]
    if capacities:
        Ka = [caps.get(x, 1) for x in range(nb)]  # shared by both sides, as in the verified code
        M1 = OracleMatroid(m, CapPartitionOracle(m, nb, Fa, Ka))
        M2 = OracleMatroid(m, CapPartitionOracle(m, nb, Ta, Ka))
    else:
        M1 = OracleMatroid(m, UnitPartitionOracle(m, nb, Fa))
        M2 = OracleMatroid(m, UnitPartitionOracle(m, nb, Ta))
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
