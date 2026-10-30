# JGraphT 1.5.3 BreadthFirstIterator, drained, on jgrapht-opt's
# SparseIntDirectedGraph, a CSR graph built inside the clock: the
# jgrapht_csr column.
#
#   make            compiles the driver and writes the launcher bench_jgrapht here
#   make clean
#
# VERSIONS USED: JDK Eclipse Temurin 21.0.12.1+1 (javac and java).  Jars in
# lib/, fetched from Maven Central by ../../setup_libraries.sh, md5:
#   f73efc783603c57d8e8e53c90af21e88  jgrapht-core-1.5.3.jar
#   16186f39791c4ca131ef00908a0bd984  jgrapht-opt-1.5.3.jar
#   e8335a737dbff6c6912f31e8cad5730a  fastutil-8.5.18.jar   (jgrapht-opt's dependency)
#   53dfa9f277efd1d392148eb607d9b4a6  jheaps-0.14.jar
#   19e0ad08927787a9c8bdb9c18070723c  apfloat-1.14.0.jar
# The launcher runs the JVM exactly as the campaign did:
#   java -Xmx45g -XX:ActiveProcessorCount=1 -XX:+UseSerialGC
# javac and java come from JAVA_HOME if it is set, else from PATH.

JAVA_HOME ?=
JAVAC := $(if $(JAVA_HOME),$(JAVA_HOME)/bin/javac,javac)
JARS := jgrapht-core-1.5.3.jar jgrapht-opt-1.5.3.jar fastutil-8.5.18.jar jheaps-0.14.jar apfloat-1.14.0.jar
CP := $(subst $(eval) ,:,$(addprefix $(CURDIR)/lib/,$(JARS)))

.PHONY: all clean
all: bench_jgrapht

classes/JGraphTBfs.class: code/JGraphTBfs.java
	rm -rf classes && mkdir -p classes
	$(JAVAC) -cp "$(CP)" -d classes code/JGraphTBfs.java

bench_jgrapht: classes/JGraphTBfs.class
	printf '%s\n' '#!/bin/bash' \
	  '# Launcher for the JGraphT benchmark program: one JVM, one problem, then exit.' \
	  '# JAVA_HOME is optional; without it java comes from PATH.' \
	  'here="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' \
	  'cp="$$here/classes"; for j in $(JARS); do cp="$$cp:$$here/lib/$$j"; done' \
	  'java="$${JAVA_HOME:+$$JAVA_HOME/bin/}java"' \
	  'exec "$$java" -Xmx45g -XX:ActiveProcessorCount=1 -XX:+UseSerialGC -cp "$$cp" JGraphTBfs "$$@"' > $@
	chmod +x $@

clean:
	rm -rf classes bench_jgrapht
