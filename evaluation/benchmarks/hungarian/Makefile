# Makefile -- the single-run programs of the Hungarian method (Tables 22, 23 and 24) benchmark.
#   make column-<name>                    builds the program of one column (the names of README.txt)
#   make COLUMNS="<name> <name>"          builds those columns; plain `make' builds every column
#   make generators FAMILIES="<family>"   builds the instance generators those families need
#   make clean
# The SML programs are compiled from the code exports in $(GEN) (work/exports/current/hungarian, filled by
# setup/exports.sh) with MLton 20241230 and the campaign's flags; a library program is built by `make' in its
# competitors/<name> directory.  Tools come from PATH (source work/env.sh); MLTON overrides the compiler.
MLTON    ?= mlton
GEN      ?= $(abspath ../../work/exports/current/hungarian)
COLUMNS  ?= sml csa_q_csr ortools scipy_lsa scipy_mwfbm_csr jgrapht_kuhnmunkres_threadgc jgrapht_mwbm_csr jgrapht_mwbm_hashgraph
FAMILIES ?= low-cost two-cost geometric
.PHONY: all clean generators $(addprefix column-,$(COLUMNS))
all: $(addprefix column-,$(COLUMNS))
column-sml: bench_sml
column-csa_q_csr: ; $(MAKE) -C competitors/csa
column-ortools: ; $(MAKE) -C competitors/ortools
column-scipy_lsa: ; $(MAKE) -C competitors/scipy_lsa
column-scipy_mwfbm_csr: ; $(MAKE) -C competitors/scipy_mwfbm
column-jgrapht_kuhnmunkres_threadgc: ; $(MAKE) -C competitors/jgrapht_kuhnmunkres
column-jgrapht_mwbm_csr: ; $(MAKE) -C competitors/jgrapht_mwbm
column-jgrapht_mwbm_hashgraph: ; $(MAKE) -C competitors/jgrapht_mwbm_hashgraph
# 64-bit Int.int is required: the geometric costs overflow MLton's default 32-bit Int
bench_sml: code/sml/bench_sml.mlb code/sml/main.sml code/sml/asn_parser.sml $(GEN)/SML/Hungarian.sml
	cd code/sml && $(MLTON) -default-type int64 -inline 10000 -mlb-path-var 'GEN $(GEN)' -output $(CURDIR)/$@ bench_sml.mlb
GENS := $(if $(filter low-cost two-cost,$(FAMILIES)),build/assign) $(if $(filter geometric,$(FAMILIES)),build/dcube)
generators:
	$(if $(strip $(GENS)),$(MAKE) -C instances/generators $(GENS),@echo "no generator needed for $(FAMILIES)")
clean:
	rm -f bench_sml
	for d in competitors/*/ instances/generators/; do [ -f $$d/Makefile ] && $(MAKE) -C $$d clean; done; true
