# SciPy 1.15.3 scipy.optimize.linear_sum_assignment on a dense cost matrix filled outside the clock: the paper's "SciPy LSA" column (scipy_lsa).
#
#   make            creates a virtual environment with the pinned packages and
#                   writes the launcher bench_scipy_lsa here
#   make clean
#
# VERSIONS USED: Python 3.10.12 with numpy 2.2.6 and scipy 1.15.3
# (requirements.txt pins them).  PYTHON names the interpreter used to
# create the environment.  The launcher fixes --solver dense; everything
# else on its command line goes to code/scipy_solve.py.

PYTHON ?= python3

.PHONY: all clean
all: bench_scipy_lsa

# .venv links to the environment setup/python_env.sh keeps for these pinned packages (shared by every program
# with the same requirements.txt; each set of packages is installed once)
.venv/bin/python: requirements.txt
	rm -rf .venv && ln -s "$$(bash ../../../../setup/python_env.sh requirements.txt)" .venv
	test -x .venv/bin/python

bench_scipy_lsa: .venv/bin/python code/scipy_solve.py
	printf '%s\n' '#!/bin/bash' \
	  '# Launcher for the scipy_lsa benchmark program: the pinned interpreter on the driver.' \
	  'here="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' \
	  'exec "$$here/.venv/bin/python" "$$here/code/scipy_solve.py" --solver dense "$$@"' > $@
	chmod +x $@

clean:
	rm -rf .venv bench_scipy_lsa
