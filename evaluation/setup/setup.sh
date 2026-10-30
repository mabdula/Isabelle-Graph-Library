#!/bin/bash
# setup.sh MODE [--old-generated-code] -- prepares everything run/run.sh MODE needs, on a fresh Ubuntu
# VM (with build-essential, curl, patch, perl and python3), without root, with network access:
#   1. the toolchains (setup/toolchains.sh): MLton with GMP and the paper's gcc 11.4; CMake, the JDK and CPython
#      when the mode's library columns need them; Isabelle2025-2 when the mode builds the code exports
#   2. for built exports: the AFP entries the sessions need, and the Isabelle build of the export sessions
#      (setup/isabelle.sh)
#   3. the code exports the mode measures, placed in work/exports/current (setup/exports.sh)
#   4. the third-party code and generators of the mode's columns and families (setup/thirdparty.sh)
#   5. the single-run program of every column, and the generators (setup/programs.sh)
# MODE is smoke, 8h or full; modes.conf says what each one runs.  --old-generated-code measures the code
# exports of the paper's campaign (exports/campaign) instead of the pregenerated or freshly built ones; Isabelle
# is then neither downloaded nor built.
# A download that fails never stops the script: it prints the sources, the md5 and where to put the file,
# records it in NOT_AVAILABLE.txt, and what depends on it is left out.  A second run skips what is done.
# The mode's clock starts when this script starts (work/started_<mode>); run/run.sh 8h counts its hours from it.
set -uo pipefail
EVAL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
usage() { echo "usage: setup/setup.sh smoke|8h|full [--old-generated-code]" >&2; exit 2; }
mode=${1:-}; case "$mode" in smoke|8h|full) ;; *) usage ;; esac
old=0
case "${2:-}" in "") ;; --old-generated-code) old=1 ;; *) usage ;; esac
export EVAL WORK="$EVAL/work" LOG="$EVAL/work/setup_$mode.log"
mkdir -p "$WORK"; : > "$LOG"
# shellcheck disable=SC1091
source "$EVAL/setup/lib.sh"
t0=$(date +%s); echo "$t0" > "$WORK/started_$mode"
exports=$(conf "$mode.exports"); [[ $old == 1 ]] && exports=campaign
echo "$exports" > "$WORK/exports_$mode"
rm -f "$NA"
need gcc build-essential; need g++ build-essential; need make build-essential; need patch patch
need perl perl; need tar tar; need md5sum coreutils; need python3 python3
say "== setup $mode (code exports: $exports), $(date)"
bash "$EVAL/setup/toolchains.sh" "$mode" "$exports" || fail "toolchains.sh failed"
if [[ "$exports" == built ]]; then
  bash "$EVAL/setup/isabelle.sh" "$mode" || say "   the Isabelle build did not complete (see $LOG); exports it did not write are left out"
fi
bash "$EVAL/setup/exports.sh" "$exports" "$mode" || fail "exports.sh failed"
bash "$EVAL/setup/thirdparty.sh" "$mode"
bash "$EVAL/setup/programs.sh" "$mode"
if [[ -f "$NA" ]]; then
  say ""; say "   NOT AVAILABLE (NOT_AVAILABLE.txt): what could not be fetched or built, and what to do about it."
  say "   The measurement script leaves out the columns and rows that depend on it and says so in its tables."
  sed 's/^/     /' "$NA" | tee -a "$LOG"
fi
say ""; say "== setup $mode done in $(( ($(date +%s) - t0) / 60 )) min; next: run/run.sh $mode$( [[ $old == 1 ]] && echo ' --old-generated-code' )"
