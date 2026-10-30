# Makefile -- the single-run programs of the Kruskal (Tables 16, 17 and 18) benchmark.
#   make column-<name>                    builds the program of one column (the names of README.txt)
#   make COLUMNS="<name> <name>"          builds those columns; plain `make' builds every column
#   make generators FAMILIES="<family>"   builds the instance generators those families need
#   make clean
# The SML programs are compiled from the code exports in $(GEN) (work/exports/current/kruskal, filled by
# setup/exports.sh) with MLton 20241230 and the campaign's flags; a library program is built by `make' in its
# competitors/<name> directory.  Tools come from PATH (source work/env.sh); MLTON overrides the compiler.
MLTON    ?= mlton
GEN      ?= $(abspath ../../work/exports/current/kruskal)
COLUMNS  ?= sml lemon jgrapht scipy networkx
FAMILIES ?= Square-n Long-n Dense-n
.PHONY: all clean generators $(addprefix column-,$(COLUMNS))
all: $(addprefix column-,$(COLUMNS))
column-sml: bench_sml
column-lemon: ; $(MAKE) -C competitors/lemon
column-jgrapht: ; $(MAKE) -C competitors/jgrapht
column-scipy: ; $(MAKE) -C competitors/scipy
column-networkx: ; $(MAKE) -C competitors/networkx
bench_sml: code/sml/bench_sml.mlb code/sml/main.sml code/sml/gr_parser.sml $(GEN)/Kruskal_SML/Kruskal_Imperative_Min.sml
	cd code/sml && $(MLTON) -inline 10000 -mlb-path-var 'GEN $(GEN)' -output $(CURDIR)/$@ bench_sml.mlb
GENS := $(if $(filter Square-n Long-n,$(FAMILIES)),spgrid.exe) $(if $(filter Dense-n,$(FAMILIES)),sprand.exe)
generators:
	$(if $(strip $(GENS)),$(MAKE) -C instances/generators $(GENS),@echo "no generator needed for $(FAMILIES)")
clean:
	rm -f bench_sml
	for d in competitors/*/ instances/generators/; do [ -f $$d/Makefile ] && $(MAKE) -C $$d clean; done; true
