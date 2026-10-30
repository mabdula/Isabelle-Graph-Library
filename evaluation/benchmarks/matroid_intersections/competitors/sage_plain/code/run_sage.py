#!/usr/bin/env python3
"""Run the sage_plain baseline on one instance and print the measurement contract line.

Usage:  run_sage.py sage_plain PROBLEM INSTANCE
        PROBLEM is matching, b_matching, weighted_matching or weighted_b_matching

This is harness code, not solver code, cut down to the one solver that lives in
this directory.  It imports solve() from
the baseline (unchanged, in sage_natural_matroid_intersection/) and prints one line:

    cpu_ms=<int> card=<int> weight=<int>

cpu_ms is the CPU time of the intersection call alone, as the baseline itself
measures it with time.process_time.  card and weight are the objective of the
returned set, computed after the clock has stopped.  user_ms and sys_ms are not
reported for Sage: process_time gives the sum and not the split.
"""

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

# problem -> (weighted, capacities); the capacitated pair reads the stamped file
PROBLEMS = {
    'matching':            (False, False),
    'weighted_matching':   (True,  False),
    'b_matching':          (False, True),
    'weighted_b_matching': (True,  True),
}


def main():
    if len(sys.argv) != 4 or sys.argv[1] != 'sage_plain':
        sys.exit(f"usage: {sys.argv[0]} sage_plain PROBLEM INSTANCE")
    problem, instance = sys.argv[2:]
    if problem not in PROBLEMS:
        sys.exit(f"unknown problem {problem!r}; one of {sorted(PROBLEMS)}")
    sys.path.insert(0, str(HERE))                 # asn_reader.py
    sys.path.insert(0, str(HERE / "sage_natural_matroid_intersection"))
    solve = __import__("sage_natural_common").solve
    weighted, capacities = PROBLEMS[problem]
    card, weight, cpu = solve(instance, weighted, capacities)
    print(f"cpu_ms={round(cpu * 1000)} card={card} weight={weight}")


if __name__ == "__main__":
    main()
