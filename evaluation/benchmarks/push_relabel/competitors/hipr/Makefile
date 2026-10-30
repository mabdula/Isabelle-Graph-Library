# Goldberg's hi_pr 3.5 (highest label, gap and periodic global relabelling):
# the hipr column, "GC" [code 10] in the paper.
#
#   make            builds bench_hipr here
#   make clean
#
# VERSIONS USED: hi_pr 3.5 as distributed (hipr.tar, md5
# cb7bd4cf8db1f15b12e3a9228b6f774b).  Nothing of it is in the package:
# ../../setup_libraries.sh fetches the archive to code/hipr-3.5.tar, unpacks it to
# code/hipr-3.5/ and applies parser.c.patch, ONE character in parser.c
# (PATCHES-FOR-THIS-STUDY beside this file says which and why; it is outside
# the measured region).  hi_pr.c itself is
# untouched and is compiled from the archive's bytes: code/solve_hipr.c
# includes it with main renamed and supplies the study's shell around it.
# Compiled with  gcc -O3 -march=native -DNDEBUG -DEXCESS_TYPE_LONG  (gcc 11.4.0;
# EXCESS_TYPE_LONG is his makefile's own setting; never -DCUT_ONLY).

CC     ?= gcc
CFLAGS := -O3 -march=native -DNDEBUG -DEXCESS_TYPE_LONG

.PHONY: all clean
all: bench_hipr

bench_hipr: code/solve_hipr.c code/hipr-3.5/hi_pr.c code/hipr-3.5/parser.c code/hipr-3.5/types.h code/hipr-3.5/timer.c
	cd code && $(CC) $(CFLAGS) -o $(CURDIR)/bench_hipr solve_hipr.c

clean:
	rm -f bench_hipr
