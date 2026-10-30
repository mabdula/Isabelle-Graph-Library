# Builds the two 1st DIMACS Challenge generators the assignment families come
# from.  Nothing of them is in the package: ../../setup_instances.sh fetches the pristine
# files here and makes build/assign_patched.c and build/dcube_patched.c by
# applying assign.c.patch and dcube.c.patch beside this file.
# assign.c and dcube.c are the pristine downloads (md5
# 98bba042619c8f1c1664b74631958a86 and 3b1fcbbb4e1689444c20954fa7042e28,
# https://archive.dimacs.rutgers.edu/pub/netflow/generators/network/assign.c and
# .../generators/matching/dcube.c); both are K&R C that does not build or run
# on x86-64, so build/assign_patched.c and build/dcube_patched.c carry the
# minimal fixes (`diff assign.c build/assign_patched.c': includes, exit(1),
# MAXNODES raised from 10000 to 1048576, `char *cmd' declared; dcube: includes,
# a forward declaration, the seed read and printed as long).  twocost.a and
# geomasn.a are the challenge's awk filters, unmodified (md5
# f51724183524b2a2d7dbb19bd1b32dce, e390c3b59ba217ce8c1e5f2112c5b1ad).
#
#   make      -> build/assign, build/dcube   (gcc 11.4.0 built ours, same lines)
CC ?= gcc
.PHONY: all clean
all: build/assign build/dcube
build/assign: build/assign_patched.c
	$(CC) -w -std=gnu89 -O2 -o $@ $< -lm
build/dcube: build/dcube_patched.c
	$(CC) -O2 -w -o $@ $< -lm
clean:
	rm -f build/assign build/dcube
