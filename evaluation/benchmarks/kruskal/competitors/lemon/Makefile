# LEMON 1.3.1 kruskal(g, cost, tree) on SmartGraph + EdgeMap, the lemon column.
#
#   make            unpacks and builds LEMON from the tarball ../../setup_libraries.sh fetched (needs
#                   cmake), then builds bench_lemon here
#   make clean
#
# VERSIONS USED: LEMON 1.3.1 (lemon-1.3.1.tar.gz, put here by ../../setup_libraries.sh, md5
# e89f887559113b68657eca67cf3329b5), built with CMake, CMAKE_BUILD_TYPE=Release,
# g++ 11.4.0 (Ubuntu 11.4.0-1ubuntu1~22.04.3).  The driver was compiled with
# g++ -O3 -march=native -DNDEBUG  and linked against libemon.a.  -march=native:
# the numbers of the paper appendix are for an AMD EPYC 7343 (Zen 3); see ../../ENVIRONMENT.txt.
#
# LEMON_HOME may point at an existing LEMON 1.3.1 install (include/lemon and
# lib/libemon.a) instead of the in-tree build.

LEMON_HOME ?= $(CURDIR)/lemon-install
CXX        ?= g++
CXXFLAGS   := -O3 -march=native -DNDEBUG

.PHONY: all clean
all: bench_lemon

$(CURDIR)/lemon-install/lib/libemon.a:
	tar xzf lemon-1.3.1.tar.gz
	mkdir -p lemon-1.3.1/build && cd lemon-1.3.1/build && \
	  cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(CURDIR)/lemon-install .. && \
	  make -j4 && make install

bench_lemon: code/solve_lemon_kruskal.cc $(if $(filter $(CURDIR)/lemon-install,$(LEMON_HOME)),$(CURDIR)/lemon-install/lib/libemon.a,)
	$(CXX) $(CXXFLAGS) -I$(LEMON_HOME)/include -o $@ code/solve_lemon_kruskal.cc -L$(LEMON_HOME)/lib -lemon

clean:
	rm -rf bench_lemon lemon-1.3.1 lemon-install
