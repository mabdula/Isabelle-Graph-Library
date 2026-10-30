# Goldberg & Kennedy's CSA (cost-scaling push-relabel assignment, "CSAS
# vestion 1.2" as the distribution's version file spells it), variant csa_q,
# with the clock opened before its arc-array pack: the paper's "CSA CSR"
# column (csa_q_csr).
#
#   make            unpacks the pristine tarball (fetched by ../../setup_libraries.sh), applies the patches
#                   (build_csa.sh; recorded in build/PATCHES.txt), compiles
#                   build/csa_q and writes the launcher bench_csa here
#   make clean
#
# VERSIONS USED: cc = gcc 11.4.0 (Ubuntu 11.4.0-1ubuntu1~22.04.3) with
# -O4 -w -DMIN_COST -DQUEUE_ORDER (the shipped Makefile's -O4; gcc reads it
# as -O3); python3 (any 3.x, used only to apply the patches); the launcher
# wraps the C program in code/csa_solve.py (python3, standard library only),
# which feeds it the instance on stdin and prints the CSV row.

CC     ?= cc
PYTHON ?= python3

.PHONY: all clean
all: bench_csa

build/csa_q: build_csa.sh csa-flows20.tar.gz
	CC=$(CC) bash ./build_csa.sh

bench_csa: build/csa_q code/csa_solve.py
	printf '%s\n' '#!/bin/bash' \
	  '# Launcher for the CSA benchmark program: the wrapper on the patched csa_q.' \
	  'here="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' \
	  'exec $(PYTHON) "$$here/code/csa_solve.py" --binary "$$here/build/csa_q" "$$@"' > $@
	chmod +x $@

clean:
	rm -rf build csa-flows20 bench_csa
