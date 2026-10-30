INSTANCES OF THE BFS STUDY -- where every graph and every query came from
=========================================================================

Four families (Tables 9 to 12 of the paper).  Nothing is distributed here
but checksums; every file can be regenerated or re-downloaded byte for byte
and checked against MD5SUM_instances.txt.

HOW TO OBTAIN
  Generators  ../setup_instances.sh fetches the 9th DIMACS Challenge code suite
              ch9-1.1.tar.gz (md5 96c9761eec9dcd27dfb3711203ee4aa6; the download
              sources are listed in the script) into generators/, extracts the
              challenge's scripts genSquare-n.gr.pl and genLong-n.gr.pl from
              it and applies generators/*.pl.patch, which hold exactly the
              study's edits; `make' in generators/ then builds spgrid.exe and
              sprand.exe.  genDense-n.gr.pl is the study's own script and is
              in generators/.
  Instances   not distributed: regenerate them with the scripts (cd generators
              && perl genSquare-n.gr.pl, ...) or any single one with its exact
              command line in seeds/<family>.txt, and compare with
              MD5SUM_instances.txt.  USA-road-t: download the 12 archives from
              the URL pattern and with the checksums in seeds/USA-road-t.txt.

1. Square-n   square grids, n = 2^10 .. 2^21 (actual n = height*width with
              height = floor(sqrt(2^p)), so odd p give 2025, 8190, ...),
              m ~ 4n.  10 instances per size.
2. Long-n     long grids of height 16, n = 2^10 .. 2^21, m ~ 4n.  10 per size.
   Both are the Dijkstra study's files, produced by the 9th DIMACS
   Challenge's spgrid generator (generators/ch9-1.1.tar.gz,
   gens/grid/spgrid.c; `make' in generators/ builds it) driven by the
   challenge's own scripts genSquare-n.gr.pl and genLong-n.gr.pl, kept in
   generators/ as run except for two paths made relative (marked in
   the scripts; the challenge's copies in scripts/ of the tarball differ
   further only in $TRIALS = 10 instead of 1).  Weights (ignored by BFS) are
   uniform in [0, n].
3. Dense-n    this study's own family: n = 2^10 .. 2^15, m = n^2/16, built by
              generators/genDense-n.gr.pl (ours, after the shape of the
              challenge's genRandom4-n.gr.pl) around the challenge's own
              sprand generator (gens/rand/sprand.c): a Hamiltonian cycle on a
              random permutation of the nodes, then m-n random arcs, no
              self-loops, weights in [0, n].  10 instances per size.
   All three scripts seed perl's rand() with 971 and draw one 31-bit seed per
   instance in order p = 10.., trial 0..9 (perl 5.34 on Linux, drand48).
   seeds/<family>.txt lists, for every instance, the seed and the exact
   generator command line, e.g.
       spgrid.exe 32 0 1024 32 0 1024 1545908516   > Square-n.10.0.gr
       sprand.exe 1024 65536 0 1024 1545908516      > Dense-n.10.0.gr
   (spgrid: width, min weight, max weight, height, min, max, seed;
    sprand: n, m, min weight, max weight, seed).  The first comment line of
   each .gr repeats the seed.  To regenerate: `make' in generators/, then
   `perl genSquare-n.gr.pl' etc. there (writes ./Square-n etc.).
4. USA-road-t downloaded; see seeds/USA-road-t.txt.

QUERIES   queries.csv: family, instance, nodes, arcs, query, source, target.
          Drawn by generators/draw_queries.py (as run except for the paths,
          marked; master seed 20261011, per-instance RNG seeded from
          blake2b("20261011:<instance file>"), s and t uniform over 1..n with
          t != s).  Same master seed as the Dijkstra study, so the pairs of
          the shared families are identical to that study's.

CHECKING  MD5SUM_instances.txt: md5, size and path of every .gr (and .gr.gz)
          file the campaigns read: 240 Square-n/Long-n, 60 Dense-n, 24 road
          files.
