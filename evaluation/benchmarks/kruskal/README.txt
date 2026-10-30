BENCHMARK -- Kruskal's algorithm (paper Tables 16, 17, 18)
==========================================================

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
                        ../../work/exports/current/kruskal/ (setup/exports.sh)

Run one problem (any program; same options everywhere)
  ./bench_sml --tag Square-n instances/Square-n/Square-n.10.0.gr
  prints one CSV row; --header prints the column names.  OUTPUT.txt beside
  each program says what every column is and what the clock covers.
  bench_jgrapht reads JAVA_HOME from the environment (work/env.sh sets it).

Columns of the paper, their names in columns.txt and the program behind each
  SML                  sml                            bench_sml
  LEMON                lemon                          competitors/lemon/bench_lemon
  JGraphT              jgrapht                        competitors/jgrapht/bench_jgrapht
  SciPy                scipy                          competitors/scipy/bench_scipy
  NetworkX             networkx                       competitors/networkx/bench_networkx

Portability: nothing in the package refers to the benchmark machine; tools
come from PATH or from the variables documented in the Makefiles.
