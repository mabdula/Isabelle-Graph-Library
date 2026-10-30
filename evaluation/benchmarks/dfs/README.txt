BENCHMARK -- depth-first search (paper Tables 5, 6, 7, 8)
=========================================================

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
                        ../../work/exports/current/dfs/ (setup/exports.sh)

Run one problem (any program; same options everywhere)
  ./bench_sml_csr --source 359 --target 0 --tag Square-n instances/Square-n/Square-n.10.0.gr
  prints one CSV row; --header prints the column names.  OUTPUT.txt beside
  each program says what every column is and what the clock covers.  The
  target must be 0 (not a vertex): the search is a full sweep.

Columns of the paper, their names in columns.txt and the program behind each
  SML CSR              sml_csr                        bench_sml_csr
  SML lists            sml_lists                      bench_sml_lists
  SML RBT              sml_rbt                        bench_sml_rbt
  LEMON CSR            lemon_csr                      competitors/lemon/bench_lemon
  LEMON linked         lemon_linked                   competitors/lemon_linked/bench_lemon_linked
  JGraphT CSR          jgrapht_csr                    competitors/jgrapht/bench_jgrapht
  JGraphT hash         jgrapht_hashgraph              competitors/jgrapht_hashgraph/bench_jgrapht_hashgraph
  SciPy CSR            scipy_csr                      competitors/scipy/bench_scipy
  SciPy prebuilt       scipy_prebuilt                 competitors/scipy_prebuilt/bench_scipy_prebuilt
  NetworkX             networkx                       competitors/networkx/bench_networkx

The *_linked, *_hashgraph and *_prebuilt programs are the drivers of the first
campaign (2026-10-13), kept as they ran, in competitors/lemon_linked,
competitors/jgrapht_hashgraph and competitors/scipy_prebuilt; the others are
the drivers of the campaign of 2026-10-14.
PROTOCOL.txt says which campaign each column was read from.
