INSTANCES OF THE PUSH-RELABEL STUDY -- where every network came from
====================================================================

Three families (Tables 19, 20, 21 of the paper), all produced on the fly by
DIMACS generators and deleted after use; no instance file is distributed and
none was checksummed.  ../setup_instances.sh fetches the three generators' sources
(the script says from where) and `make' in generators/ builds them exactly as
the study did; seeds/<family>.txt lists, for every instance that
was measured, the generator command line that produces it.

HOW TO OBTAIN
  Generators  ../setup_instances.sh fetches genrmf (the Flow Challenge 2.0's genrmfDimacs.zip),
              washington.c (the challenge's copy) and ak.c (PRF 1.8, the Wayback
              Machine's copy of Goldberg's site), each checked by md5 (sources in the
              script); `make' in generators/ builds bin/genrmf, bin/washington, bin/ak.
  Instances   not distributed (the study produced each one on the fly): run the
              command line given for it in seeds/<family>.txt, e.g.
                bin/genrmf -a 16 -b 256 -c1 1 -c2 10000 -seed 1 > rmf-long-16-256_s1.max
              The generators are deterministic; no checksum was recorded.

1. rmf-long       genrmf -a A -b B -c1 1 -c2 10000 -seed S
                  n = A^2 B, m = 4AB(A-1) + (B-1)A^2.  15 rungs from (8,64)
                  to (91,8104); the top six rungs are the Flow Challenge 2.0
                  prescription, the nine below follow its rule downward
                  (halve n, A = n^(1/4), B = n^(1/2)).  Seeds 1, 2, 3 per
                  rung = three instances.  Source and sink from the file.
2. wash-rlg-long  washington 2 128 D2 10000 S  (function 2: random level
                  graph, long; dim1 = 128; capacity range 10000; seed S).
                  n = 128 D2 + 2.  15 rungs D2 = 32 .. 524288; the top six are
                  the prescription.  Seeds 1, 2, 3 per rung.
3. ak             ak K, n = 4K + 6, m = 6K + 7, no seed.  9 rungs K = 1024 ..
                  262144 (n = 4102 .. 1048582); the top three extend the
                  1994 paper's sizes.  One instance per rung, three repeats.

The ladders are the seed lists in seeds/.
