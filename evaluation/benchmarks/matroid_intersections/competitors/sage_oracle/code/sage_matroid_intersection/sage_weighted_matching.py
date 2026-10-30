#!/usr/bin/env python3
"""Maximum-weight bipartite matching with Sage's matroid intersection.

Usage:  python3 sage_weighted_matching.py INSTANCE
Prints the CPU seconds of the intersection call alone; see sage_bipartite_common.py.
"""

from sage_bipartite_common import main

if __name__ == "__main__":
    main(weighted=True, capacities=False)
