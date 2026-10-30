BENCHMARK -- Dijkstra's algorithm (paper Tables 13, 14, 15)
===========================================================

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
                        ../../work/exports/current/dijkstra/ (setup/exports.sh)

Run one problem (any program; same options everywhere)
  ./bench_sml --source 14 --target 787 --tag Square-n instances/.../Square-n.10.0.gr
  prints one CSV row; --header prints the column names.  OUTPUT.txt beside
  each program says what every column is and what the clock covers.

Columns of the paper, their names in columns.txt and the program behind each
  SML                  sml                            bench_sml
  LEMON CSR            lemon_csr                      competitors/lemon/bench_lemon
  LEMON linked         lemon_linked                   competitors/lemon_linked/bench_lemon_linked
  JGraphT CSR          jgrapht_csr                    competitors/jgrapht/bench_jgrapht
  JGraphT hash         jgrapht_hashgraph              competitors/jgrapht_hashgraph/bench_jgrapht_hashgraph
  SciPy CSR            scipy_csr                      competitors/scipy/bench_scipy
  SciPy prebuilt       scipy_prebuilt                 competitors/scipy_prebuilt/bench_scipy_prebuilt
  NetworkX             networkx                       competitors/networkx/bench_networkx

competitors/lemon_linked, competitors/jgrapht_hashgraph and
competitors/scipy_prebuilt measure the libraries on a structure built outside
the clock (a linked arc list, an object-per-arc graph, a prebuilt CSR matrix);
competitors/lemon, competitors/jgrapht and competitors/scipy measure them on
CSR built inside the clock.  PROTOCOL.txt says which results directory each
column was read from.
