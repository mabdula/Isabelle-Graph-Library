#!/usr/bin/env python3
"""Turn a DIMACS assignment instance into a b-matching instance by stamping
vertex capacities onto it.

The graph is not touched. Comments, the arc lines and their order are passed
through unchanged, so the b-matching instance sits on exactly the graph the
DIMACS generator produced and its result is comparable with the matching result
on the same file. The only edits are the "n" lines, which are replaced by one
"n <id> <cap>" line per vertex that carries an arc, and the problem line.

Capacity rule:

    cap(v) = min(U, deg(v)),  U drawn uniformly from 1..20, once per vertex

The cap at the degree matters: a capacity above the degree is unreachable, so
without it the high draws would all collapse to the same instance. Drawing per
vertex rather than per side is what makes the two sides disagree on total
capacity, so the answer is not forced to be a perfect matching.

Vertices are drawn for in ascending id order, so a given (file, seed) always
yields the same instance. The rule and the seed are recorded in a "c" line.

usage: stamp_capacities.py IN OUT [--seed S] [--max M] [--keep-problem-line]
"""

import argparse
import random
import sys
from collections import Counter


def stamp(lines, seed, maxcap, keep_problem_line):
    """Return the stamped lines. `lines` is the input file, as a list."""
    deg = Counter()
    left, right = set(), set()
    for line in lines:
        tok = line.split()
        if tok and tok[0] == 'a':
            try:
                u, v = int(tok[1]), int(tok[2])
            except (IndexError, ValueError):
                sys.exit(f"error: malformed arc line {line.strip()!r}")
            deg[u] += 1
            deg[v] += 1
            left.add(u)
            right.add(v)
    if not deg:
        sys.exit("error: no arcs")

    rng = random.Random(seed)
    cap = {v: min(rng.randint(1, maxcap), deg[v]) for v in sorted(deg)}

    note = (f"c capacities: cap(v) = min(U[1,{maxcap}], deg(v)), "
            f"drawn per vertex, seed {seed}\n")
    nlines = [f"n {v} {cap[v]}\n" for v in sorted(cap)]

    out = []
    placed = False
    for line in lines:
        tok = line.split()
        head = tok[0] if tok else None
        if head == 'p':
            if keep_problem_line:
                out.append(line)
            else:  # the file is a b-matching instance now; both are accepted
                out.append(' '.join(['p', 'bmatch'] + tok[2:]) + '\n')
            out.append(note)
        elif head == 'n':
            if not placed:          # the whole "n" block, in place of the first
                out.extend(nlines)
                placed = True
        elif head == 'a':
            if not placed:          # no "n" block in the input: before the arcs
                out.extend(nlines)
                placed = True
            out.append(line)
        else:
            out.append(line)
    if not placed:
        sys.exit("error: nowhere to place the capacities")
    return out, cap, deg, left, right


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('src')
    ap.add_argument('dst')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--max', type=int, default=20, dest='maxcap')
    ap.add_argument('--keep-problem-line', action='store_true',
                    help='leave "p asn" alone instead of writing "p bmatch"')
    ap.add_argument('--quiet', action='store_true')
    a = ap.parse_args()
    if a.maxcap < 1:
        sys.exit("error: --max must be at least 1")

    with open(a.src) as f:
        lines = f.readlines()
    out, cap, deg, left, right = stamp(lines, a.seed, a.maxcap, a.keep_problem_line)
    with open(a.dst, 'w') as f:
        f.writelines(out)

    if not a.quiet:
        cl = sum(cap[v] for v in left)
        cr = sum(cap[v] for v in right)
        print(f"{a.dst}: {len(left)}+{len(right)} vertices stamped, "
              f"capacity {cl} left / {cr} right, "
              f"mean {(cl + cr) / len(cap):.2f}, size at most {min(cl, cr)}")


if __name__ == '__main__':
    main()
