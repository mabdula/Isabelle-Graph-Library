# Builds the three DIMACS maximum-flow generators that produced every instance
# of the study, exactly as the study built them (push_relabel/bench/build_all.sh:
# gcc -O2 -w for ak and washington; genrmf through its own makefile with
# CFLAGS="-O2 -w").  gcc 11.4.0.  All three are deterministic given their
# arguments; ../seeds/<family>.txt gives every command line that was run.
#
#   make        -> bin/ak, bin/washington, bin/genrmf
#
# Provenance (md5 of the file as downloaded; none of it is in the package,
# ../../setup_instances.sh fetches and places all three):
#   genrmfDimacs/   Flow Challenge 2.0, http://coral.ise.lehigh.edu/flow-challenge-2-0/files/2026/09/genrmfDimacs.zip
#                   (Goldberg's corrected genrmf; genrmf.c 47718b07ece55b0e57236ae0a1fb9f30)
#   washington/     Flow Challenge 2.0, https://coral.ise.lehigh.edu//wp-content/uploads/washington.c
#                   (11c0e0b48daf9a08599ab0811d9cd0f8)
#   ak/             PRF 1.8, Cherkassky and Goldberg, http://web.archive.org/web/2018id_/http://www.avglab.com/andrew/soft/prf.tar
#                   (ak.c a55236f7732aa733b3c1b5ebd62da00d)
CC ?= gcc
.PHONY: all clean
all: bin/ak bin/washington bin/genrmf
bin/ak: ak/ak.c
	mkdir -p bin && $(CC) -O2 -w -o bin/ak ak/ak.c
bin/washington: washington/washington.c
	mkdir -p bin && $(CC) -O2 -w -o bin/washington washington/washington.c
bin/genrmf: genrmfDimacs/genrmf.c genrmfDimacs/genmain.c genrmfDimacs/genio.c
	$(MAKE) -C genrmfDimacs CC=$(CC) CFLAGS="-O2 -w" >/dev/null
	mkdir -p bin && cp genrmfDimacs/genrmf.exe bin/genrmf
clean:
	rm -rf bin genrmfDimacs/*.o genrmfDimacs/genrmf.exe
