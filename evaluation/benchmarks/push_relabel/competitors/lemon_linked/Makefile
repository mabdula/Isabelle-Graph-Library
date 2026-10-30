# LEMON 1.3.1 Preflow (highest label) on SmartDigraph (a linked arc list) filled
# OUTSIDE the clock: the lemon_linked column.
#
#   make            builds bench_lemon_linked here
#   make clean
#
# VERSIONS USED: LEMON 1.3.1 (lemon-1.3.1.tar.gz, put here by ../../setup_libraries.sh, md5
# e89f887559113b68657eca67cf3329b5), built with CMake, CMAKE_BUILD_TYPE=Release,
# the system g++ 11.4.0 (Ubuntu 11.4.0-1ubuntu1~22.04.3).  The driver was
# compiled with  g++ -O3 -march=native -DNDEBUG  and linked against libemon.a.
# -march=native: the numbers of the paper appendix are for an AMD EPYC 7343 (Zen 3); see
# ../../ENVIRONMENT.txt.
#
# If LEMON is already installed, point LEMON_HOME at the prefix that holds
# include/lemon and lib/libemon.a; otherwise the tarball is unpacked and built
# into ./lemon-install (needs cmake and make).

LEMON_HOME ?= $(CURDIR)/lemon-install
CXX        ?= g++
CXXFLAGS   := -O3 -march=native -DNDEBUG

.PHONY: all clean
all: bench_lemon_linked

$(CURDIR)/lemon-install/lib/libemon.a:
	tar xzf lemon-1.3.1.tar.gz
	mkdir -p lemon-1.3.1/build && cd lemon-1.3.1/build && \
	  cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(CURDIR)/lemon-install .. && \
	  make -j4 && make install

bench_lemon_linked: code/solve_lemon_pr.cc $(if $(filter $(CURDIR)/lemon-install,$(LEMON_HOME)),$(CURDIR)/lemon-install/lib/libemon.a,)
	$(CXX) $(CXXFLAGS) -I$(LEMON_HOME)/include -o $@ code/solve_lemon_pr.cc -L$(LEMON_HOME)/lib -lemon

clean:
	rm -rf bench_lemon_linked lemon-1.3.1 lemon-install
