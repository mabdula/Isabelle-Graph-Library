# JGraphT 1.5.3 KruskalMinimumSpanningTree on DefaultUndirectedWeightedGraph
# (filled outside the clock), the jgrapht column.
#
#   make            compiles the driver and writes the launcher bench_jgrapht here
#   make clean
#
# VERSIONS USED: JDK Eclipse Temurin 21.0.12.1+1 (javac and java).  Jars in
# lib/, fetched from Maven Central by ../../setup_libraries.sh, md5:
#   f73efc783603c57d8e8e53c90af21e88  jgrapht-core-1.5.3.jar
#   53dfa9f277efd1d392148eb607d9b4a6  jheaps-0.14.jar   (on the classpath, unused by Kruskal)
# jgrapht-opt is deliberately NOT used in this study.  The launcher runs the
# JVM exactly as the campaign did:
#   java -Xmx45g -XX:ActiveProcessorCount=1 -XX:+UseSerialGC
# JAVA_HOME names a JDK 21 (for javac here and, read from the environment at
# run time, for the launcher); if unset, javac and java come from PATH.

JAVA_HOME ?=
JAVAC := $(if $(JAVA_HOME),$(JAVA_HOME)/bin/javac,javac)
JAVA  := $(if $(JAVA_HOME),$(JAVA_HOME)/bin/java,java)
CP := $(CURDIR)/lib/jgrapht-core-1.5.3.jar:$(CURDIR)/lib/jheaps-0.14.jar

.PHONY: all clean
all: bench_jgrapht

classes/JGraphTKruskal.class: code/JGraphTKruskal.java
	rm -rf classes && mkdir -p classes
	$(JAVAC) -cp "$(CP)" -d classes code/JGraphTKruskal.java

bench_jgrapht: classes/JGraphTKruskal.class
	printf '%s\n' '#!/bin/bash' \
	  '# Launcher for the JGraphT benchmark program: one JVM, one problem, then exit.' \
	  '# JAVA_HOME (a JDK 21) is read from the environment at run time; else java from PATH.' \
	  'here="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' \
	  'exec "$${JAVA_HOME:+$$JAVA_HOME/bin/}java" -Xmx45g -XX:ActiveProcessorCount=1 -XX:+UseSerialGC \' \
	  '  -cp "$$here/classes:$$here/lib/jgrapht-core-1.5.3.jar:$$here/lib/jheaps-0.14.jar" JGraphTKruskal "$$@"' > $@
	chmod +x $@

clean:
	rm -rf classes bench_jgrapht
