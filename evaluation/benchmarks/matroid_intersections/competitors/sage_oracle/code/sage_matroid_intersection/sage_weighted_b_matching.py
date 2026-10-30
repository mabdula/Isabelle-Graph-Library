#!/usr/bin/env python3
"""Maximum-weight bipartite b-matching (vertex capacities) with Sage's matroid intersection.

Usage:  python3 sage_weighted_b_matching.py INSTANCE
Prints the CPU seconds of the intersection call alone; see sage_bipartite_common.py.
"""

from sage_bipartite_common import main

if __name__ == "__main__":
    main(weighted=True, capacities=True)
