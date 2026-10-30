# JGraphT 1.5.3 depth-first search (DepthFirstIterator, drained, no
# cross-component traversal) on jgrapht-opt's SparseIntDirectedGraph, a CSR
# graph built inside the clock: the jgrapht_csr column.
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
# javac and java are taken from JAVA_HOME if it is set, else from PATH
# (JAVAC and JAVA override).  The launcher runs the JVM exactly as the
# campaign did:  java -Xmx45g -XX:ActiveProcessorCount=1 -XX:+UseSerialGC

ifeq ($(JAVA_HOME),)
JAVAC ?= javac
JAVA  ?= java
else
JAVAC ?= $(JAVA_HOME)/bin/javac
JAVA  ?= $(JAVA_HOME)/bin/java
endif
CP := $(CURDIR)/lib/jgrapht-core-1.5.3.jar:$(CURDIR)/lib/jgrapht-opt-1.5.3.jar:$(CURDIR)/lib/fastutil-8.5.18.jar:$(CURDIR)/lib/jheaps-0.14.jar:$(CURDIR)/lib/apfloat-1.14.0.jar

.PHONY: all clean
all: bench_jgrapht

classes/JGraphTDfs.class: code/JGraphTDfs.java
	rm -rf classes && mkdir -p classes
	$(JAVAC) -cp "$(CP)" -d classes code/JGraphTDfs.java

bench_jgrapht: classes/JGraphTDfs.class
	printf '%s\n' '#!/bin/bash' \
	  '# Launcher for the JGraphT benchmark program: one JVM, one problem, then exit.' \
	  'here="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' \
	  'exec "$(JAVA)" -Xmx45g -XX:ActiveProcessorCount=1 -XX:+UseSerialGC \' \
	  '  -cp "$$here/classes:$(CP)" JGraphTDfs "$$@"' > $@
	chmod +x $@

clean:
	rm -rf classes bench_jgrapht
