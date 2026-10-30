# Builds the two 9th DIMACS Challenge generators that produced the synthetic
# families, from the challenge's own code suite (ch9-1.1.tar.gz, md5
# 96c9761eec9dcd27dfb3711203ee4aa6, http://www.diag.uniroma1.it/~challenge9/code/ch9-1.1.tar.gz;
# not in the package: ../../setup_instances.sh fetches it here, and makes the two driving
# scripts genSquare-n.gr.pl and genLong-n.gr.pl from the suite's copies and the
# patches *.pl.patch beside this file, which hold the study's edits).
#
#   make        -> spgrid.exe (Square-n, Long-n) and sprand.exe (Dense-n, used by the BFS, DFS and Kruskal studies)
#
# The challenge's makefiles put -lm before the sources, which a current GNU ld
# rejects (undefined reference to log), so the compile line is given here with
# -lm last; it is otherwise the challenge's (its -O6 is -O3 to gcc).  gcc
# 11.4.0 built the copies that generated our instances with exactly this line,
# and the generators are integer code, so the optimisation level does not
# touch the output: ../MD5SUM_instances.txt lets you check.
CC     ?= gcc
CFLAGS := -O3 -DNDEBUG -DPERMUTE_NODES -I ../../lib -I ../../lib/ll-core/include
.PHONY: all clean
all: spgrid.exe sprand.exe
ch9-1.1/gens/grid/spgrid.c:
	tar xzf ch9-1.1.tar.gz
spgrid.exe: ch9-1.1/gens/grid/spgrid.c
	cd ch9-1.1/gens/grid && $(CC) $(CFLAGS) -o spgrid.exe spgrid.c ../../lib/ll-core/src/*.c -lm 2>/dev/null
	cp ch9-1.1/gens/grid/spgrid.exe .
sprand.exe: ch9-1.1/gens/grid/spgrid.c
	cd ch9-1.1/gens/rand && $(CC) $(CFLAGS) -o sprand.exe sprand.c ../../lib/ll-core/src/*.c -lm 2>/dev/null
	cp ch9-1.1/gens/rand/sprand.exe .
clean:
	rm -rf ch9-1.1 spgrid.exe sprand.exe
