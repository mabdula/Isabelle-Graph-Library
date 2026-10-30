BENCHMARK -- matroid intersection (paper Tables 25, 26, 27, 28)
===============================================================

Bipartite matching, b-matching, weighted matching and weighted b-matching
solved as the intersection of two partition matroids, by the verified
Bipartite_Matching export (SML) and by SageMath's matroid
intersection with two kinds of oracle.

Layout
  Makefile              builds the single-run programs: make column-<name> (the names below), make generators FAMILIES="..."
  columns.txt           column name -> single-run program and its fixed arguments (read by run/run_experiments.py)
  code/sml/             parser and the SML single-run programs; OUTPUT*.txt: the row each prints and what its clock covers
  competitors/<name>/   one directory per library column: Makefile, code/, OUTPUT.txt; `make' there builds bench_<name>
  instances/            generators, seeds, queries, checksums (instances/README.txt says how an instance is made)
  paper_results/    the tables and raw rows of the paper appendix, for comparison
  PROTOCOL.txt          how one measured run was launched and aggregated into a cell of the paper
  ENVIRONMENT.txt       the machine and the versions behind the numbers of the paper appendix
  setup_libraries.sh, setup_instances.sh   fetch the third-party code and generators (setup/thirdparty.sh runs them
                        with the columns and families of the mode); the code exports are read from
                        ../../work/exports/current/matroid_intersections/ (setup/exports.sh)

Run one problem (same two arguments for every program)
  ./bench_sml matching instances/.../low-cost_n64_s1.asn
  ./bench_sml b_matching instances/.../low-cost_n64_s1.bmatch
  PROBLEM is matching | b_matching | weighted_matching | weighted_b_matching;
  the (weighted) b-matching problems read the .bmatch file (same graph,
  capacities stamped on), the others the .asn file.  Each program prints one
  line of key=value pairs; OUTPUT.txt beside each program says what every
  field is and what the clock covers.

Columns of the paper, their names in columns.txt and the program behind each
  SML                  sml                            bench_sml
  Sage (our oracle)    sage_oracle                    competitors/sage_oracle/bench_sage_oracle
  Sage (plain)         sage_plain                     competitors/sage_plain/bench_sage_plain
