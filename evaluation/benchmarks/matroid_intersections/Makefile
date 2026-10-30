# Makefile -- the single-run programs of the matroid intersection (Tables 26, 27 and 28) benchmark.
#   make column-<name>                    builds the program of one column (the names of README.txt)
#   make COLUMNS="<name> <name>"          builds those columns; plain `make' builds every column
#   make generators FAMILIES="<family>"   builds the instance generators those families need
#   make clean
# The SML programs are compiled from the code exports in $(GEN) (work/exports/current/matroid_intersections, filled by
# setup/exports.sh) with MLton 20241230 and the campaign's flags; a library program is built by `make' in its
# competitors/<name> directory.  Tools come from PATH (source work/env.sh); MLTON overrides the compiler.
MLTON    ?= mlton
GEN      ?= $(abspath ../../work/exports/current/matroid_intersections)
COLUMNS  ?= sml sage_oracle sage_plain
FAMILIES ?= low-cost two-cost geometric
.PHONY: all clean generators $(addprefix column-,$(COLUMNS))
all: $(addprefix column-,$(COLUMNS))
column-sml: bench_sml
column-sage_oracle: ; $(MAKE) -C competitors/sage_oracle
column-sage_plain: ; $(MAKE) -C competitors/sage_plain
bench_sml: code/sml/bench_sml.mlb code/sml/main.sml code/sml/instance.sml $(GEN)/SML/Bipartite_Matching.sml
	cd code/sml && $(MLTON) -default-type int64 -inline 10000 -mlb-path-var 'GEN $(GEN)' -output $(CURDIR)/$@ bench_sml.mlb
GENS := $(if $(filter low-cost two-cost,$(FAMILIES)),assign) $(if $(filter geometric,$(FAMILIES)),dcube)
generators:
	$(if $(strip $(GENS)),$(MAKE) -C instances/generators $(GENS),@echo "no generator needed for $(FAMILIES)")
clean:
	rm -f bench_sml
	for d in competitors/*/ instances/generators/; do [ -f $$d/Makefile ] && $(MAKE) -C $$d clean; done; true
