# Builds the two first-DIMACS-Challenge generators that produced the three
# families, from the patched sources assign_patched.c and dcube_patched.c.
# Neither they nor the pristine files (assign.c, dcube.c, twocost.a, geomasn.a)
# are in the package: ../../setup_instances.sh fetches the pristine files here (sources
# and md5 in the script) and applies assign.c.patch and dcube.c.patch beside
# this file.  The patches add missing includes and declarations, give exit() an argument,
# adjust a %d/%ld seed format and raise dcube's MAXNODES, nothing else).
#
#   make        -> assign, dcube
#   then, e.g.   ./gen_instances.sh --nodes 32,64,128,256,512,1024,2048,4096,8192,16384,32768 --seeds 1,2,3,4,5
#                ./gen_geometric.sh --nodes 32,64,128,256,512,1024,2048,4096 --seeds 1,2,3,4,5
#                ./stamp_instances.sh --families low-cost,two-cost,geometric
#   writes out/<family>/<family>_n<N>_s<K>.asn and .bmatch; compare with ../MD5SUM_instances.txt.
#
# gcc 11.4.0 built the copies that generated our instances; both generators
# are integer code and the output does not depend on the optimisation level.
CC     ?= gcc
CFLAGS ?= -O2
.PHONY: all clean
all: assign dcube
assign: assign_patched.c
	$(CC) $(CFLAGS) -w -o assign assign_patched.c -lm
dcube: dcube_patched.c
	$(CC) $(CFLAGS) -w -o dcube dcube_patched.c -lm
clean:
	rm -rf assign dcube out
