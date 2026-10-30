# Google OR-Tools 9.15.6755 SimpleLinearSumAssignment: the paper's "OR-Tools"
# column (ortools).
#
#   make            creates a virtual environment with the pinned packages and
#                   writes the launcher bench_ortools here
#   make clean
#
# VERSIONS USED: Python 3.10.12 with ortools 9.15.6755 and its dependencies;
# requirements.txt is the exact `pip freeze' of the environment the campaign
# ran in (it also holds scipy and networkx, which this program does not
# import).  PYTHON names the interpreter used to create the environment.

PYTHON ?= python3

.PHONY: all clean
all: bench_ortools

# .venv links to the environment setup/python_env.sh keeps for these pinned packages (shared by every program
# with the same requirements.txt; each set of packages is installed once)
.venv/bin/python: requirements.txt
	rm -rf .venv && ln -s "$$(bash ../../../../setup/python_env.sh requirements.txt)" .venv
	test -x .venv/bin/python

bench_ortools: .venv/bin/python code/ortools_solve.py
	printf '%s\n' '#!/bin/bash' \
	  '# Launcher for the ortools benchmark program: the pinned interpreter on the driver.' \
	  'here="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' \
	  'exec "$$here/.venv/bin/python" "$$here/code/ortools_solve.py" "$$@"' > $@
	chmod +x $@

clean:
	rm -rf .venv bench_ortools
