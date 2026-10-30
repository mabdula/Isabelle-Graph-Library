# Makefile -- the single-run programs of the hybrid bipartite matching solver (CSA as oracle, Tables 35, 36 and 37; smoke test only) benchmark.
#   make column-<name>                    builds the program of one column (the names of README.txt)
#   make COLUMNS="<name> <name>"          builds those columns; plain `make' builds every column
#   make generators FAMILIES="<family>"   builds the instance generators those families need
#   make clean
# The SML programs are compiled from the code exports in $(GEN) (work/exports/current/hybrid_bipartite_matching, filled by
# setup/exports.sh) with MLton 20241230 and the campaign's flags; a library program is built by `make' in its
# competitors/<name> directory.  Tools come from PATH (source work/env.sh); MLTON overrides the compiler.
MLTON    ?= mlton
GEN      ?= $(abspath ../../work/exports/current/hybrid_bipartite_matching)
COLUMNS  ?= hybrid
FAMILIES ?= low-cost two-cost geometric
.PHONY: all clean generators $(addprefix column-,$(COLUMNS))
all: $(addprefix column-,$(COLUMNS))
CC     ?= gcc
PYTHON ?= python3
D      := code/driver
O      := code/oracle
CSA    := $(O)/csa
OBJ    := $(D)/obj
CFLAGS    := -O2
CSA_FLAGS := -O3 -std=gnu89 -w -DCSA_LIBRARY -DMIN_COST -DQUEUE_ORDER -Dn=csa_glob_n -Dm=csa_glob_m
CSA_SRC   := main refine update_epsilon parse stack queue timer debug
CSA_OBJ   := $(CSA_SRC:%=$(OBJ)/csa_%.o)
TIMING    := -DASN_TIMING
MLTON_FLAGS := -default-ann 'allowFFI true' -default-type int64 -inline 10000 -link-opt -lm
column-hybrid: bench_hybrid
$(OBJ):
	mkdir -p $(OBJ)
$(OBJ)/csa_%.o: $(CSA)/%.c $(CSA)/csa_types.h $(CSA)/csa_defs.h | $(OBJ)
	$(CC) $(CFLAGS) $(CSA_FLAGS) -c $< -o $@
$(OBJ)/asn_certificates_bench.o: $(O)/asn_certificates.c | $(OBJ)
	$(CC) $(CFLAGS) $(TIMING) -c $< -o $@
$(OBJ)/asn_io.o: $(D)/asn_io.c | $(OBJ)
	$(CC) $(CFLAGS) -c $< -o $@
$(OBJ)/asn_clock_bench.o: $(D)/asn_clock.c | $(OBJ)
	$(CC) $(CFLAGS) $(TIMING) -c $< -o $@
$(D)/asn_solver_bench.mlb: Makefile
	printf '$$(SML_LIB)/basis/basis.mlb\n$$(GEN)/Assignment_Solver.sml\nasn_bench_on.sml\nasn_main.sml\n' > $@
$(D)/asn_solver_bench: $(D)/asn_solver_bench.mlb $(D)/asn_main.sml $(D)/asn_bench_on.sml $(GEN)/Assignment_Solver.sml $(CSA_OBJ) $(OBJ)/asn_certificates_bench.o $(OBJ)/asn_io.o $(OBJ)/asn_clock_bench.o
	cd $(D) && $(MLTON) $(MLTON_FLAGS) -mlb-path-var 'GEN $(GEN)' -output asn_solver_bench asn_solver_bench.mlb \
	  $(CSA_OBJ:$(D)/%=%) obj/asn_certificates_bench.o obj/asn_io.o obj/asn_clock_bench.o
# the launcher: the campaign's CSV wrapper around the timing build
bench_hybrid: $(D)/asn_solver_bench $(D)/asn_solve.py
	printf '%s\n' '#!/bin/bash' \
	  '# One run of the hybrid solver, one CSV row: asn_solve.py around asn_solver_bench.' \
	  '# Options: [--no-oracle] [--tag T] [--timeout S] <instance.asn>' \
	  'here="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' \
	  'exec $(PYTHON) "$$here/code/driver/asn_solve.py" --binary "$$here/code/driver/asn_solver_bench" --csv "$$@"' > $@
	chmod +x $@
GENS := $(if $(filter low-cost two-cost,$(FAMILIES)),build/assign) $(if $(filter geometric,$(FAMILIES)),build/dcube)
generators:
	$(if $(strip $(GENS)),$(MAKE) -C instances/generators $(GENS),@echo "no generator needed for $(FAMILIES)")
clean:
	rm -rf $(OBJ) $(D)/asn_solver_bench $(D)/asn_solver_bench.mlb bench_hybrid
	[ -f instances/generators/Makefile ] && $(MAKE) -C instances/generators clean; true
