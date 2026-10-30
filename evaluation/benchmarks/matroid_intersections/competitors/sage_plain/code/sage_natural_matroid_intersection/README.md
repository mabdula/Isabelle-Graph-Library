# Plain Sage matroid intersection baseline

Solves bipartite matching problems with SageMath's matroid intersection the way a Sage user
would, without our verified oracles: the two partition matroids are built with Sage's own
constructors, and all queries of the intersection routines are answered by Sage's generic
code on top of the rank function. Instances are read by the study's reader,
`../asn_reader.py`, which also documents the format.

| Problem | Matroids | Rank oracle runs as |
|---|---|---|
| matching | `PartitionMatroid` (`sage.matroids.union_matroid`) | Cython on Python sets/dicts |
| b-matching | `Matroid(groundset=E, rank_function=r)`, a `RankMatroid` with r(X) = sum over blocks B of min(cap(B), \|X & B\|) | interpreted Python |

Sage has no partition matroid with capacities, hence the rank function for b-matching. In both
cases closures and circuits come from the generic `Matroid._closure` and `Matroid._circuit`,
which ask the rank oracle about once per ground set element.

## Requirements

A Python with `sage.matroids`: either full Sage (run with `sage -python`) or just

    pip install passagemath-modules

## Scripts

Each takes the instance file as its only argument and prints a single number: the CPU seconds
(`time.process_time`) of the Sage intersection call alone; parsing and matroid construction
are excluded.

| Script | Problem | Sage routine |
|---|---|---|
| `sage_natural_matching.py` | maximum-cardinality matching | `intersection_unweighted` |
| `sage_natural_b_matching.py` | maximum-cardinality b-matching | `intersection_unweighted` |
| `sage_natural_weighted_matching.py` | maximum-weight matching | `intersection` |
| `sage_natural_weighted_b_matching.py` | maximum-weight b-matching | `intersection` |

The matching scripts reject instances with capacities other than 1.

## Shared code

`sage_natural_common.py` (must stay next to the scripts) holds the construction of the two
matroids and the timed solve.
