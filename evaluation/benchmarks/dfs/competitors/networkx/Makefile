# NetworkX 3.4.2 networkx.dfs_predecessors on a DiGraph built outside the clock: the networkx column.
#
#   make            creates a virtual environment with the pinned packages and
#                   writes the launcher bench_networkx here
#   make clean
#
# VERSIONS USED: Python 3.10.12 with numpy 2.2.6, scipy 1.15.3, networkx 3.4.2
# (requirements.txt pins all three; the campaign venv held nothing else).
# PYTHON names the interpreter used to create the environment (from PATH).

PYTHON ?= python3

.PHONY: all clean
all: bench_networkx

# .venv links to the environment setup/python_env.sh keeps for these pinned packages (shared by every program
# with the same requirements.txt; each set of packages is installed once)
.venv/bin/python: requirements.txt
	rm -rf .venv && ln -s "$$(bash ../../../../setup/python_env.sh requirements.txt)" .venv
	test -x .venv/bin/python

bench_networkx: .venv/bin/python code/networkx_dfs.py code/gr_read.py
	printf '%s\n' '#!/bin/bash' \
	  '# Launcher for the networkx benchmark program: the pinned interpreter on the driver.' \
	  'here="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' \
	  'exec "$$here/.venv/bin/python" "$$here/code/networkx_dfs.py" "$$@"' > $@
	chmod +x $@

clean:
	rm -rf .venv bench_networkx
