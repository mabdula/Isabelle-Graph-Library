# Sage matroid intersection baseline

Solves bipartite matching problems with SageMath's matroid intersection. The two partition
matroids answer Sage's queries with Python transcriptions of the verified oracles of our
Isabelle instances. Instances are read by the study's reader, `../asn_reader.py`, which also
documents the format.

## Requirements

A Python with `sage.matroids`: either full Sage (run with `sage -python`) or just

    pip install passagemath-modules

## Scripts

Each takes the instance file as its only argument and prints a single number: the CPU seconds
(`time.process_time`) of the Sage intersection call alone; parsing and matroid construction
are excluded.

| Script | Problem | Sage routine |
|---|---|---|
| `sage_matching.py` | maximum-cardinality matching | `intersection_unweighted` |
| `sage_b_matching.py` | maximum-cardinality b-matching | `intersection_unweighted` |
| `sage_weighted_matching.py` | maximum-weight matching | `intersection` |
| `sage_weighted_b_matching.py` | maximum-weight b-matching | `intersection` |

The matching scripts reject instances with capacities other than 1.

## Shared code

`sage_bipartite_common.py` (must stay next to the scripts) holds the oracle
transcriptions `UnitPartitionOracle` (matching) and `CapPartitionOracle` (b-matching), the
adapter `OracleMatroid` that answers Sage's queries with them, and the timed solve.
