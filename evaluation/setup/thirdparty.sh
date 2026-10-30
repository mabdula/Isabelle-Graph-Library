#!/bin/bash
# thirdparty.sh MODE -- fetches the third-party code and the generators of the mode's columns and families:
# each benchmark's setup_libraries.sh and setup_instances.sh, told the columns, families and road networks of
# modes.conf, download into work/downloads (sources and md5s: third_party/SOURCES.txt) and place the files
# where the Makefiles expect them.  What cannot be fetched is recorded in NOT_AVAILABLE.txt.
set -uo pipefail
EVAL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "$EVAL/setup/lib.sh"
mode=$1
export REPRO_CACHE="$WORK/downloads"
rm -f "$REPRO_CACHE"/*.unreachable
say "== third-party code and generators (into work/downloads; third_party/SOURCES.txt lists the sources)"
for b in $(conf "$mode.benchmarks"); do
  cols=$(conf "$mode.columns.$b"); fams=$(conf "$mode.families.$b"); roads=$(conf "$mode.roads")
  d="$EVAL/benchmarks/$b"
  if [[ -f "$d/setup_libraries.sh" ]]; then
    if ( cd "$d" && bash ./setup_libraries.sh --columns "$cols" ) >>"$LOG" 2>&1; then say "   $b/setup_libraries.sh: ok"
    else say "   $b/setup_libraries.sh: did not complete, see $LOG (and NOT_AVAILABLE.txt)"; fi
  fi
  if ( cd "$d" && bash ./setup_instances.sh --families "$fams" --roads "$roads" ) >>"$LOG" 2>&1; then say "   $b/setup_instances.sh: ok"
  else say "   $b/setup_instances.sh: did not complete, see $LOG (and NOT_AVAILABLE.txt)"; fi
done
