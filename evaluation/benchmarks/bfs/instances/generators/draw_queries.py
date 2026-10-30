#!/usr/bin/env python3
"""Draw one random (source, target) pair for every instance in the study.

Every solver reads this file, so all of them answer exactly the same question
on exactly the same graph, and the pair is recorded next to the timing it
produced.

The draw is reproducible without being positional: the seed for an instance is
derived from its own name and the master seed, so adding or removing an
instance never shifts the pairs drawn for the others.  THAT IS WHY THIS STUDY
AND THE DIJKSTRA STUDY ASK THE SAME QUESTIONS.  The master seed below is the
one the Dijkstra study used, and Square-n, Long-n and USA-road-t are the same
files, reached through symbolic links; so adding the Dense-n family here
leaves every one of their 360 pairs bit-identical to the pairs that study
drew.  A BFS row and a Dijkstra row for the same instance and query are two
answers to two questions about one graph and one pair.

The synthetic families have ten graphs per size and get one pair each.  The
road networks are a single graph per region, so they get ten pairs each, to
give the same spread of queries per table cell.
"""
import csv, gzip, hashlib, os, random, sys

# AS RUN: ROOT was the study directory and INST its instances/ directory; for
# this package the families are read from the directory of this script
# (where the generator scripts write them) and the output lands beside it.
ROOT = os.path.dirname(os.path.abspath(__file__))
INST = ROOT
OUT = os.path.join(INST, "queries.csv")
MASTER = 20261011          # recorded in the header line of the output

# Dense-n is this study's own: the 9th DIMACS Challenge on shortest paths
# shipped no dense family -- all six of its synthetic families sit at four
# arcs per node -- so it was built here with the challenge's own sprand
# generator at m = n^2/16.  See bench/gen/genDense-n.gr.pl.
SYNTH = ["Square-n", "Long-n", "Dense-n"]
ROAD_QUERIES = 10


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


def draw(rng, n):
    """A source and a target, distinct, over the DIMACS ids 1..n."""
    s = rng.randrange(1, n + 1)
    t = rng.randrange(1, n + 1)
    while t == s:
        t = rng.randrange(1, n + 1)
    return s, t


def main():
    rows = []
    for fam in SYNTH:
        d = os.path.join(INST, fam)
        for f in sorted(os.listdir(d)):
            if not f.endswith(".gr"):
                continue
            n, m = header_of(os.path.join(d, f))
            s, t = draw(rng_for(f), n)
            rows.append([fam, f, n, m, 0, s, t])
    d = os.path.join(INST, "USA-road-t")
    for f in sorted(os.listdir(d)):
        if not f.endswith(".gr"):
            continue
        n, m = header_of(os.path.join(d, f))
        rng = rng_for(f)
        for q in range(ROAD_QUERIES):
            s, t = draw(rng, n)
            rows.append(["USA-road-t", f, n, m, q, s, t])

    with open(OUT, "w", newline="") as fh:
        w = csv.writer(fh, lineterminator="\n")
        w.writerow(["family", "instance", "nodes", "arcs", "query",
                    "source", "target"])
        w.writerows(rows)
    print("wrote %s  %d queries  master seed %d" % (OUT, len(rows), MASTER))


if __name__ == "__main__":
    main()
