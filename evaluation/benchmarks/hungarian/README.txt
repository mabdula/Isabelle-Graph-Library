BENCHMARK -- Hungarian method (paper Tables 22, 23, 24)
=======================================================

Layout
  Makefile              builds the single-run programs: make column-<name> (the names below), make generators FAMILIES="..."
  columns.txt           column name -> single-run program and its fixed arguments (read by run/run_experiments.py)
  code/sml/             parser and the SML single-run programs; OUTPUT*.txt: the row each prints and what its clock covers
  competitors/<name>/   one directory per library column: Makefile, code/, OUTPUT.txt; `make' there builds bench_<name>
  instances/            generators, seeds, queries, checksums (instances/README.txt says how an instance is made)
  published_results/    the published tables and raw rows, for comparison
  PROTOCOL.txt          how one measured run was launched and aggregated into a cell of the paper
  ENVIRONMENT.txt       the machine and the versions behind the published numbers
  setup_libraries.sh, setup_instances.sh   fetch the third-party code and generators (setup/thirdparty.sh runs them
                        with the columns and families of the mode); the code exports are read from
                        ../../work/exports/current/hungarian/ (setup/exports.sh)

Run one instance
  ./bench_sml --theta-frac 1.0 --cap 2 --tag low-cost <file.asn>
  competitors/csa/bench_csa --csv --tag low-cost <file.asn>
  Each prints one CSV row; OUTPUT.txt beside each program says what every
  column is and what the clock covers.  The JVM launchers read JAVA_HOME from
  the environment at run time (work/env.sh sets it).

Columns of the paper, their names in columns.txt and the program behind each
  SML                  sml                            bench_sml
  CSA CSR              csa_q_csr                      competitors/csa/bench_csa
  OR-Tools             ortools                        competitors/ortools/bench_ortools
  SciPy LSA            scipy_lsa                      competitors/scipy_lsa/bench_scipy_lsa
  SciPy MWFBM CSR      scipy_mwfbm_csr                competitors/scipy_mwfbm/bench_scipy_mwfbm
  JGraphT KM with GC   jgrapht_kuhnmunkres_threadgc   competitors/jgrapht_kuhnmunkres/bench_jgrapht_kuhnmunkres
  JGraphT MWBM CSR     jgrapht_mwbm_csr               competitors/jgrapht_mwbm/bench_jgrapht_mwbm
  JGraphT MWBM hash    jgrapht_mwbm_hashgraph         competitors/jgrapht_mwbm_hashgraph/bench_jgrapht_mwbm_hashgraph

PROTOCOL.txt says which campaign each column was read from and how the
cells (mean over ten instances of the median of three repeats) were formed.
