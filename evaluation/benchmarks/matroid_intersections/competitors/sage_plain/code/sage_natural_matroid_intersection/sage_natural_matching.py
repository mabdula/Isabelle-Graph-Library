#!/usr/bin/env python3
"""Maximum-cardinality bipartite matching with Sage's matroid intersection.
Plain Sage version: the matroids are built with Sage's own constructors.

Usage:  python3 sage_natural_matching.py INSTANCE
Prints the CPU seconds of the intersection call alone; see sage_natural_common.py.
"""

from sage_natural_common import main

if __name__ == "__main__":
    main(weighted=False, capacities=False)
