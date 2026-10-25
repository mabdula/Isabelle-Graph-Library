#!/bin/bash
# Gate build: ASCII copies of the theories listed in the session ROOT, built as session BXG in a
# scratch directory (the real files keep jEdit's glyphs until Phase 9), plus the provenance check.
set -u
R=/media/llms/Isabelle-Graph-Library-Blossom-Executable
S=$R/Edmonds_Blossom_Executable
G=/home/llm/.claude/jobs/d07b4540/tmp/v2/BXG
rm -rf $G && mkdir -p $G
sed 's/^session Blossom_Executable = /session BXG = /' $S/ROOT > $G/ROOT
for T in $(awk '/^  theories/{f=1;next} f && NF{print $1}' $S/ROOT); do cp $S/$T.thy $G/; done
python3 $R/.claude/iq/to_ascii.py $G/*.thy | sed 's|.*/||'
cd $R
USER_HOME=/media/llms/isabelle-home-blossom timeout 3000 isabelle build -o document=false -d $G BXG > $G/build.log 2>&1
echo "build exit: $?"; grep -E '^\*\*\*|Finished|Unfinished|elapsed' $G/build.log | head -20
USER_HOME=/media/llms/isabelle-home-blossom timeout 600 isabelle ai_provenance -s -t -D $G 2>&1 | tail -20
