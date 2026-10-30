#!/usr/bin/env python3
"""Draw one random (source, target) pair for every instance in the study.

Every solver reads this file, so all ten of them answer exactly the same
question on exactly the same graph, and the pair is recorded next to the
timing it produced.

The draw is reproducible without being positional: the seed for an instance is
derived from its own name and the master seed, so adding or removing an
instance never shifts the pairs drawn for the others.

The synthetic families have ten graphs per size and get one pair each.  The
road networks are a single graph per region, so they get ten pairs each, to
give the same spread of queries per table cell.
"""
import csv, gzip, hashlib, os, random, sys

ROOT = ".."   # the instances/ directory
INST = os.path.join(ROOT, "instances")
OUT = os.path.join(INST, "queries.csv")
MASTER = 20261011          # recorded in the header line of the output

SYNTH = ["Square-n", "Long-n"]
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
