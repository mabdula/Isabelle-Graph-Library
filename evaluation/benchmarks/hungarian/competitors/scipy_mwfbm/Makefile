# SciPy 1.15.3 scipy.sparse.csgraph.min_weight_full_bipartite_matching on a csr_matrix built inside the clock: the paper's "SciPy MWFBM CSR" column (scipy_mwfbm_csr).
#
#   make            creates a virtual environment with the pinned packages and
#                   writes the launcher bench_scipy_mwfbm here
#   make clean
#
# VERSIONS USED: Python 3.10.12 with numpy 2.2.6 and scipy 1.15.3
# (requirements.txt pins them).  PYTHON names the interpreter used to
# create the environment.  The launcher fixes --solver sparse; everything
# else on its command line goes to code/scipy_solve.py.

PYTHON ?= python3

.PHONY: all clean
all: bench_scipy_mwfbm

# .venv links to the environment setup/python_env.sh keeps for these pinned packages (shared by every program
# with the same requirements.txt; each set of packages is installed once)
.venv/bin/python: requirements.txt
	rm -rf .venv && ln -s "$$(bash ../../../../setup/python_env.sh requirements.txt)" .venv
	test -x .venv/bin/python

bench_scipy_mwfbm: .venv/bin/python code/scipy_solve.py
	printf '%s\n' '#!/bin/bash' \
	  '# Launcher for the scipy_mwfbm benchmark program: the pinned interpreter on the driver.' \
	  'here="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' \
	  'exec "$$here/.venv/bin/python" "$$here/code/scipy_solve.py" --solver sparse "$$@"' > $@
	chmod +x $@

clean:
	rm -rf .venv bench_scipy_mwfbm
