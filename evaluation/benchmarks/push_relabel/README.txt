BENCHMARK -- push-relabel maximum flow (paper Tables 19, 20, 21)
================================================================

Layout
  Makefile              builds the single-run programs: make column-<name> (the names below), make generators FAMILIES="..."
  columns.txt           column name -> single-run program and its fixed arguments (read by run/run_experiments.py)
  code/sml_pr/, code/sml_afp/   parser and the two SML single-run programs; OUTPUT.txt: the row each prints and what its clock covers
  competitors/<name>/   one directory per library column: Makefile, code/, OUTPUT.txt; `make' there builds bench_<name>
  instances/            generators, seeds, queries, checksums (instances/README.txt says how an instance is made)
  paper_results/    the tables and raw rows of the paper appendix, for comparison
  PROTOCOL.txt          how one measured run was launched and aggregated into a cell of the paper
  ENVIRONMENT.txt       the machine and the versions behind the numbers of the paper appendix
  setup_libraries.sh, setup_instances.sh   fetch the third-party code and generators (setup/thirdparty.sh runs them
                        with the columns and families of the mode); the code exports are read from
                        ../../work/exports/current/push_relabel/ (setup/exports.sh)

Run one problem
  instances/generators/bin/genrmf -a 8 -b 64 -c1 1 -c2 10000 -seed 1 > rmf-long-8-64.max
  ./bench_sml_pr --variant hl --tag "seed=1" rmf-long-8-64.max
  prints one CSV row; --header prints the column names.  OUTPUT.txt beside
  each program says what every column is and what the clock covers.

Columns of the paper, their names in columns.txt and the program behind each
  SML HL               sml_hl                         bench_sml_pr --variant hl
  SML FIFO             sml_fifo                       bench_sml_pr --variant fifo
  SML AFP              sml_afp                        bench_sml_afp
  LEMON CSR            lemon_csr                      competitors/lemon/bench_lemon
  LEMON linked         lemon_linked                   competitors/lemon_linked/bench_lemon_linked
  GC (hi_pr)           hipr                           competitors/hipr/bench_hipr
  JGraphT              jgrapht                        competitors/jgrapht/bench_jgrapht
  SciPy CSR            scipy_csr                      competitors/scipy/bench_scipy
  SciPy prebuilt       scipy_prebuilt                 competitors/scipy_prebuilt/bench_scipy_prebuilt
  NetworkX             networkx                       competitors/networkx/bench_networkx

The "LEMON linked" and "SciPy Dinic prebuilt" columns measure LEMON on
SmartDigraph built outside the clock and SciPy with the matrix built before
the clock; they are competitors/lemon_linked and competitors/scipy_prebuilt.
PROTOCOL.txt says which results directory each column was read from.
