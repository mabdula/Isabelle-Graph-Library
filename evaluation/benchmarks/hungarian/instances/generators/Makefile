# Builds the two First DIMACS Challenge generators that produced the three
# families, from the patched copies in build/.  Neither the pristine files
# (assign.c, dcube.c, twocost.a, geomasn.a) nor the patched copies are in the
# package: ../../setup_instances.sh fetches the pristine files here (sources and md5 in
# the script) and makes build/assign_patched.c and build/dcube_patched.c by
# applying assign.c.patch and dcube.c.patch beside this file.  The patches are
# the whole change: headers, a
# declared `cmd', exit(1), MAXNODES raised to 1048576 (assign.c), and a %ld
# for the seed (dcube.c) -- K&R C made to build and run on x86-64.
#
#   make            -> build/assign, build/dcube
#   ./gen_instances.sh --nodes 2048 --seeds 1     -> out/low-cost, out/two-cost
#   ./gen_geometric.sh --nodes 256 --seeds 1      -> out/geometric
#
# gcc 11.4.0 with -O2 built the copies that generated our instances; the
# generators are deterministic integer code, so ../MD5SUM_instances.txt lets
# you check any regenerated file byte for byte.  awk (gawk 5.1.0 was used)
# runs the two DIMACS filters.
CC     ?= cc
CFLAGS ?= -O2
.PHONY: all clean
all: build/assign build/dcube
build/assign: build/assign_patched.c
	$(CC) $(CFLAGS) -w -o $@ build/assign_patched.c -lm
build/dcube: build/dcube_patched.c
	$(CC) $(CFLAGS) -w -o $@ build/dcube_patched.c -lm
clean:
	rm -rf build/assign build/dcube out
