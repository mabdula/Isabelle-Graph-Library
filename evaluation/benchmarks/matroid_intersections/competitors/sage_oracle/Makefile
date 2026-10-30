# Sage's matroid intersection with the two partition matroids answering its queries through Python transcriptions of the verified Isabelle oracles: the "Sage (our oracle)" column.
#
#   make            creates a virtual environment with the pinned packages and
#                   writes the launcher bench_sage_oracle here
#   make clean
#
# VERSIONS USED: Python 3.10.12 with passagemath 10.6.48 (the modular pip
# distribution of the Sage library: passagemath-modules and passagemath-graphs
# with their dependencies; requirements.txt is the `pip freeze' of the venv
# the campaign ran in).  PYTHON names the interpreter used to create the
# environment.  The solver code in code/sage_matroid_intersection/ is the uploaded baseline,
# unchanged; code/run_sage.py is the launcher the campaign used and
# code/asn_reader.py the study's one instance reader (never on the clock).

PYTHON ?= python3

.PHONY: all clean
all: bench_sage_oracle

# .venv links to the environment setup/python_env.sh keeps for these pinned packages (shared by every program
# with the same requirements.txt; each set of packages is installed once)
.venv/bin/python: requirements.txt
	rm -rf .venv && ln -s "$$(bash ../../../../setup/python_env.sh requirements.txt)" .venv
	test -x .venv/bin/python

bench_sage_oracle: .venv/bin/python code/run_sage.py code/asn_reader.py
	printf '%s\n' '#!/bin/bash' \
	  '# Launcher for the sage_oracle benchmark program: the pinned interpreter on the driver.' \
	  '#   bench_sage_oracle PROBLEM INSTANCE' \
	  'here="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' \
	  'exec "$$here/.venv/bin/python" "$$here/code/run_sage.py" sage_oracle "$$@"' > $@
	chmod +x $@

clean:
	rm -rf .venv bench_sage_oracle
