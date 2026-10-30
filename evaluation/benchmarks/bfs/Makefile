# Makefile -- the single-run programs of the breadth-first search (Tables 9, 11 and 12) benchmark.
#   make column-<name>                    builds the program of one column (the names of README.txt)
#   make COLUMNS="<name> <name>"          builds those columns; plain `make' builds every column
#   make generators FAMILIES="<family>"   builds the instance generators those families need
#   make clean
# The SML programs are compiled from the code exports in $(GEN) (work/exports/current/bfs, filled by
# setup/exports.sh) with MLton 20241230 and the campaign's flags; a library program is built by `make' in its
# competitors/<name> directory.  Tools come from PATH (source work/env.sh); MLTON overrides the compiler.
MLTON    ?= mlton
GEN      ?= $(abspath ../../work/exports/current/bfs)
COLUMNS  ?= sml_csr sml_rbt lemon_csr lemon_linked jgrapht_csr jgrapht_hashgraph scipy_csr scipy_prebuilt networkx
FAMILIES ?= Square-n Long-n Dense-n
.PHONY: all clean generators $(addprefix column-,$(COLUMNS))
all: $(addprefix column-,$(COLUMNS))
column-sml_csr: bench_sml_csr
column-sml_rbt: bench_sml_rbt
column-lemon_csr: ; $(MAKE) -C competitors/lemon
column-lemon_linked: ; $(MAKE) -C competitors/lemon_linked
column-jgrapht_csr: ; $(MAKE) -C competitors/jgrapht
column-jgrapht_hashgraph: ; $(MAKE) -C competitors/jgrapht_hashgraph
column-scipy_csr: ; $(MAKE) -C competitors/scipy
column-scipy_prebuilt: ; $(MAKE) -C competitors/scipy_prebuilt
column-networkx: ; $(MAKE) -C competitors/networkx
bench_sml_csr: code/sml/bench_sml_csr.mlb code/sml/main_csr.sml code/sml/gr_parser.sml $(GEN)/BFS_CSR_SML/BFS_CSR.sml $(GEN)/bfs_api.sml
	cd code/sml && $(MLTON) -inline 10000 -mlb-path-var 'GEN $(GEN)' -output $(CURDIR)/$@ bench_sml_csr.mlb
bench_sml_rbt: code/sml/bench_sml_rbt.mlb code/sml/main_rbt.sml code/sml/gr_parser.sml $(GEN)/BFS_RBT_SML/BFS_RBT.sml
	cd code/sml && $(MLTON) -inline 10000 -mlb-path-var 'GEN $(GEN)' -output $(CURDIR)/$@ bench_sml_rbt.mlb
GENS := $(if $(filter Square-n Long-n,$(FAMILIES)),spgrid.exe) $(if $(filter Dense-n,$(FAMILIES)),sprand.exe)
generators:
	$(if $(strip $(GENS)),$(MAKE) -C instances/generators $(GENS),@echo "no generator needed for $(FAMILIES)")
clean:
	rm -f bench_sml_csr bench_sml_rbt
	for d in competitors/*/ instances/generators/; do [ -f $$d/Makefile ] && $(MAKE) -C $$d clean; done; true
