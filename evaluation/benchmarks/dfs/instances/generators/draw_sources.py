#!/usr/bin/env python3
"""Draw the random source for every instance in the study.

Every solver reads this file, so all thirteen of them search exactly the same
graph from exactly the same vertex, and the source is recorded next to the
timing it produced.

THE SOURCES ARE DRAWN AT RANDOM, AND THEY ARE THIS STUDY'S OWN.  The master
seed below is not the Dijkstra study's, so these sources are a fresh draw and
not the ones the BFS study searched from.  A DFS row and a BFS row therefore
share a graph but not a source, and only the per-instance totals should be
read across the two studies, not individual rows.

The draw is reproducible without being positional: the seed for an instance is
derived from its own name and the master seed, so adding or removing an
instance never shifts the sources drawn for the others.

THE TARGET COLUMN IS 0 ON EVERY ROW, AND 0 IS NOT A VERTEX.  DIMACS ids run
1..n.  All three verified exports are reachability searches that stop the
moment the top of the stack equals the target, and this study measures a FULL
graph search, so they are given a target the graph cannot contain and run
until their stacks are empty.  The reference solvers are run through entry
points that take no target at all and sweep the whole region reachable from
the source.  Every driver REFUSES a target inside [1, n], so a real target
cannot reach a solver by accident.  The column is kept -- rather than dropped
-- so that a DFS row and a BFS row have the same shape.

The synthetic families have ten graphs per size and get one source each.  The
road networks are a single graph per region, so they get ten sources each, to
give the same spread of searches per table cell.
"""
import csv, gzip, hashlib, os, random, sys

# ROOT is the instances/ directory: the script runs from instances/generators
# after the families have been generated into instances/<family>/.
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
INST = ROOT
OUT = os.path.join(INST, "queries.csv")
MASTER = 20261013          # this study's own; see the note above

SYNTH = ["Square-n", "Long-n", "Dense-n"]
ROAD_QUERIES = 10

# No vertex of a DIMACS .gr file carries this id.
ABSENT_TARGET = 0


def header_of(path):
    """Node and arc count from the DIMACS 'p sp N M' line."""
    op = gzip.open if path.endswith(".gz") else open
    with op(path, "rt") as fh:
        for line in fh:
            if line.startswith("p "):
                f = line.split()
                return int(f[2]), int(f[3])
            if not line.startswith("c"):
                break
    raise SystemExit("no problem line in " + path)


def rng_for(name):
    h = hashlib.blake2b(("%d:%s" % (MASTER, name)).encode(), digest_size=8)
    return random.Random(int.from_bytes(h.digest(), "big"))


def main():
    rows = []
    for fam in SYNTH:
        d = os.path.join(INST, fam)
        for f in sorted(os.listdir(d)):
            if not f.endswith(".gr"):
                continue
            n, m = header_of(os.path.join(d, f))
            s = rng_for(f).randrange(1, n + 1)
            rows.append([fam, f, n, m, 0, s, ABSENT_TARGET])
    d = os.path.join(INST, "USA-road-t")
    for f in sorted(os.listdir(d)):
        if not f.endswith(".gr"):
            continue
        n, m = header_of(os.path.join(d, f))
        rng = rng_for(f)
        for q in range(ROAD_QUERIES):
            rows.append(["USA-road-t", f, n, m, q,
                         rng.randrange(1, n + 1), ABSENT_TARGET])

    with open(OUT, "w", newline="") as fh:
        w = csv.writer(fh, lineterminator="\n")
        w.writerow(["family", "instance", "nodes", "arcs", "query",
                    "source", "target"])
        w.writerows(rows)
    print("wrote %s  %d searches  master seed %d" % (OUT, len(rows), MASTER))


if __name__ == "__main__":
    main()
