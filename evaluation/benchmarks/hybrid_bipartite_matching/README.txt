BENCHMARK -- hybrid bipartite matching solver with CSA as oracle (paper Tables 35, 36, 37)
==========================================================================================

Layout
  Makefile              builds the single-run programs: make column-<name> (the names below), make generators FAMILIES="..."
  columns.txt           column name -> single-run program and its fixed arguments (read by run/run_experiments.py)
  code/driver/          the SML main and FFI glue, parser/printer, the phase clock, the CSV wrapper asn_solve.py
  code/oracle/          the certificate generators and (after the setup) CSA, as used by the oracle
  code/README_solver.md the solver's own README (what is proved, what is trusted); code/OUTPUT.txt the row
  instances/            generators, seeds, queries, checksums (instances/README.txt says how an instance is made)
  published_results/    the published tables and raw rows, for comparison
  PROTOCOL.txt          how one measured run was launched and aggregated into a cell of the paper
  ENVIRONMENT.txt       the machine and the versions behind the published numbers
  setup_libraries.sh, setup_instances.sh   fetch the third-party code and generators (setup/thirdparty.sh runs them
                        with the columns and families of the mode); the code exports are read from
                        ../../work/exports/current/hybrid_bipartite_matching/ (setup/exports.sh)

There is no competitors directory: the paper's columns Oracle, Cert., Check,
Glue and Total are phases of the one hybrid run (code/OUTPUT.txt).

Run one instance
  ./bench_hybrid --tag low-cost instances/files/low-cost/low-cost_n2048_s1.asn
  prints one CSV row (header in code/OUTPUT.txt).


THE ORACLE'S C CODE
  CSA is not redistributed with the evaluation.  ./setup_libraries.sh fetches the challenge's
  tarball, extracts the unmodified files into code/oracle/pristine_csa/ and makes
  code/oracle/csa/, the oracle (library form, every change marked CSA_LIBRARY),
  by applying code/oracle/ORACLE_MODIFICATIONS.diff, the complete difference
  between the two.  code/oracle/asn_certificates.c is the oracle
  entry and the certificate generators (our own code).
