# JGraphT 1.5.3 PushRelabelMFImpl on a DirectedWeightedPseudograph filled
# while the file is read (outside the clock; the algorithm copies it into its
# own arrays inside the measured call): the jgrapht column.
#
#   make            compiles the driver and writes the launcher bench_jgrapht here
#   make clean
#
# VERSIONS USED: JDK Eclipse Temurin 21.0.12.1+1 (javac and java).  Jars in
# lib/, fetched from Maven Central by ../../setup_libraries.sh, md5:
#   f73efc783603c57d8e8e53c90af21e88  jgrapht-core-1.5.3.jar
#   53dfa9f277efd1d392148eb607d9b4a6  jheaps-0.14.jar
#   19e0ad08927787a9c8bdb9c18070723c  apfloat-1.14.0.jar
# The launcher runs the JVM exactly as the campaign did (drivers/java/run.sh
# with PR_XMX=42g exported by the runner: the 45 GB cap less the JVM's overhead):
#   java -Xmx42g -XX:ActiveProcessorCount=1 -XX:+UseSerialGC
# PR_XMX in the environment overrides the heap size.

# JAVA_HOME is optional: when unset, javac (here) and java (in the launcher,
# which reads JAVA_HOME at run time) are taken from PATH.
JAVAC := $(if $(JAVA_HOME),$(JAVA_HOME)/bin/javac,javac)
CP := lib/jgrapht-core-1.5.3.jar:lib/jheaps-0.14.jar:lib/apfloat-1.14.0.jar

.PHONY: all clean
all: bench_jgrapht

classes/JGraphTMaxFlow.class: code/JGraphTMaxFlow.java
	rm -rf classes && mkdir -p classes
	$(JAVAC) -cp "$(CP)" -d classes code/JGraphTMaxFlow.java

bench_jgrapht: classes/JGraphTMaxFlow.class
	printf '%s\n' '#!/bin/bash' \
	  '# Launcher for the JGraphT benchmark program: one JVM, one problem, then exit.' \
	  'here="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' \
	  'java="$${JAVA_HOME:+$$JAVA_HOME/bin/}java"' \
	  'cp="$$here/classes:$$here/lib/jgrapht-core-1.5.3.jar:$$here/lib/jheaps-0.14.jar:$$here/lib/apfloat-1.14.0.jar"' \
	  'exec "$$java" -Xmx$${PR_XMX:-42g} -XX:ActiveProcessorCount=1 -XX:+UseSerialGC -cp "$$cp" JGraphTMaxFlow "$$@"' > $@
	chmod +x $@

clean:
	rm -rf classes bench_jgrapht
