# JGraphT 1.5.3 MaximumWeightBipartiteMatching on jgrapht-core's
# SimpleWeightedGraph (an object per edge, hash maps around it) built OUTSIDE
# the clock, on the bare thread clock: the paper's "JGraphT MWBM hash" column
# (jgrapht_mwbm_hashgraph).
#
#   make            compiles the driver and writes the launcher bench_jgrapht_mwbm_hashgraph_hashgraph here
#   make clean
#
# VERSIONS USED: JDK Eclipse Temurin 21.0.12.1+1 (javac and java).  Jars in
# lib/, fetched from Maven Central by ../../setup_libraries.sh, md5:
#   f73efc783603c57d8e8e53c90af21e88  jgrapht-core-1.5.3.jar
#   53dfa9f277efd1d392148eb607d9b4a6  jheaps-0.14.jar
#   19e0ad08927787a9c8bdb9c18070723c  apfloat-1.14.0.jar
# The launcher runs the JVM exactly as the sweep did:
#   java -XX:ActiveProcessorCount=1 -XX:+UseSerialGC -Xmx24g ... JGraphTSolve --solver mwbm
# JAVA_HOME is optional; without it javac (at build time) and java (read by the
# launcher at run time) come from PATH.

JAVAC ?= $(if $(JAVA_HOME),$(JAVA_HOME)/bin/javac,javac)
CP := $(CURDIR)/lib/jgrapht-core-1.5.3.jar:$(CURDIR)/lib/jheaps-0.14.jar:$(CURDIR)/lib/apfloat-1.14.0.jar

.PHONY: all clean
all: bench_jgrapht_mwbm_hashgraph

classes/JGraphTSolve.class: code/JGraphTSolve.java
	rm -rf classes && mkdir -p classes
	$(JAVAC) -cp "$(CP)" -d classes code/JGraphTSolve.java

bench_jgrapht_mwbm_hashgraph: classes/JGraphTSolve.class
	printf '%s\n' '#!/bin/bash' \
	  '# Launcher for the jgrapht_mwbm_hashgraph benchmark program: one JVM, one instance, then exit.' \
	  '# java comes from JAVA_HOME if set at run time, else from PATH; the jars are in lib/.' \
	  'here="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' \
	  'exec "$${JAVA_HOME:+$$JAVA_HOME/bin/}java" -XX:ActiveProcessorCount=1 -XX:+UseSerialGC -Xmx24g \' \
	  '  -cp "$$here/lib/jgrapht-core-1.5.3.jar:$$here/lib/jheaps-0.14.jar:$$here/lib/apfloat-1.14.0.jar:$$here/classes" JGraphTSolve --solver mwbm "$$@"' > $@
	chmod +x $@

clean:
	rm -rf classes bench_jgrapht_mwbm_hashgraph
