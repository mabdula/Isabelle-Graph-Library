# Makefile -- the single-run programs of the push-relabel (Tables 19, 20 and 21) benchmark.
#   make column-<name>                    builds the program of one column (the names of README.txt)
#   make COLUMNS="<name> <name>"          builds those columns; plain `make' builds every column
#   make generators FAMILIES="<family>"   builds the instance generators those families need
#   make clean
# The SML programs are compiled from the code exports in $(GEN) (work/exports/current/push_relabel, filled by
# setup/exports.sh) with MLton 20241230 and the campaign's flags; a library program is built by `make' in its
# competitors/<name> directory.  Tools come from PATH (source work/env.sh); MLTON overrides the compiler.
MLTON    ?= mlton
GEN      ?= $(abspath ../../work/exports/current/push_relabel)
COLUMNS  ?= sml_hl sml_fifo sml_afp lemon_csr lemon_linked hipr jgrapht scipy_csr scipy_prebuilt networkx
FAMILIES ?= rmf-long wash-rlg-long ak
.PHONY: all clean generators $(addprefix column-,$(COLUMNS))
all: $(addprefix column-,$(COLUMNS))
column-sml_hl: bench_sml_pr
column-sml_fifo: bench_sml_pr
column-sml_afp: bench_sml_afp
column-lemon_csr: ; $(MAKE) -C competitors/lemon
column-lemon_linked: ; $(MAKE) -C competitors/lemon_linked
column-hipr: ; $(MAKE) -C competitors/hipr
column-jgrapht: ; $(MAKE) -C competitors/jgrapht
column-scipy_csr: ; $(MAKE) -C competitors/scipy
column-scipy_prebuilt: ; $(MAKE) -C competitors/scipy_prebuilt
column-networkx: ; $(MAKE) -C competitors/networkx
# bench_sml_pr: the library's export, highest label and FIFO in one program (--variant hl|fifo)
bench_sml_pr: code/sml_pr/bench_sml_pr.mlb code/sml_pr/main.sml code/sml_pr/max_parser.sml $(GEN)/SML/Push_Relabel.sml
	cd code/sml_pr && $(MLTON) -inline 10000 -mlb-path-var 'GEN $(GEN)' -output $(CURDIR)/$@ bench_sml_pr.mlb
# bench_sml_afp: the export of the AFP's FIFO push-relabel (Prpu_Maxflow), supplied pregenerated
bench_sml_afp: code/sml_afp/bench_sml_afp.mlb code/sml_afp/main_afp.sml code/sml_afp/max_parser.sml code/sml_afp/csr.sml $(GEN)/AFP/SML/AFP_FIFO_Push_Relabel.sml
	cd code/sml_afp && $(MLTON) -inline 10000 -mlb-path-var 'GEN $(GEN)' -output $(CURDIR)/$@ bench_sml_afp.mlb
GENS := $(if $(filter rmf-long,$(FAMILIES)),bin/genrmf) $(if $(filter wash-rlg-long,$(FAMILIES)),bin/washington) $(if $(filter ak,$(FAMILIES)),bin/ak)
generators:
	$(if $(strip $(GENS)),$(MAKE) -C instances/generators $(GENS),@echo "no generator needed for $(FAMILIES)")
clean:
	rm -f bench_sml_pr bench_sml_afp
	for d in competitors/*/ instances/generators/; do [ -f $$d/Makefile ] && $(MAKE) -C $$d clean; done; true
