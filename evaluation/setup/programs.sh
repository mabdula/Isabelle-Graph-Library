#!/bin/bash
# programs.sh MODE -- builds the single-run program of every column of the mode (make COLUMNS=... in each
# benchmark directory: the SML programs from work/exports/current, the library programs in their
# competitors/<name> directories against one LEMON build in work/lemon and shared Python environments in
# work/venvs, see setup/python_env.sh) and the
# instance generators of the mode's families (make generators FAMILIES=...).  A column whose program cannot
# be built is recorded in NOT_AVAILABLE.txt and left out of the measurements.
set -uo pipefail
EVAL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "$EVAL/setup/lib.sh"
# shellcheck disable=SC1091
source "$WORK/env.sh"
mode=$1
allcols=$(for b in $(conf "$mode.benchmarks"); do conf "$mode.columns.$b"; done)
# LEMON is built once, into work/lemon, for every lemon column (the competitor Makefiles link against LEMON_HOME)
# shellcheck disable=SC2086
if any_matches '^lemon' $allcols; then
  if [[ -f "$WORK/lemon/lib/libemon.a" ]]; then say "   LEMON 1.3.1: already built"
  elif [[ -f "$WORK/downloads/lemon-1.3.1.tar.gz" ]]; then
    say "   building LEMON 1.3.1 into work/lemon"
    if ( rm -rf "$WORK/lemon-src" && mkdir -p "$WORK/lemon-src" && tar xzf "$WORK/downloads/lemon-1.3.1.tar.gz" -C "$WORK/lemon-src" --strip-components=1 \
         && mkdir -p "$WORK/lemon-src/build" && cd "$WORK/lemon-src/build" && cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX="$WORK/lemon" .. && make -j4 && make install ) >>"$LOG" 2>&1
    then rm -rf "$WORK/lemon-src"; say "   ok     LEMON 1.3.1"
    else say "   FAILED LEMON 1.3.1 (see $LOG); the lemon columns are left out"; echo "LEMON could not be built (see work/setup_$mode.log); the lemon columns are left out" >> "$NA"; fi
  else say "   LEMON 1.3.1: lemon-1.3.1.tar.gz was not downloaded; the lemon columns are left out"; fi
fi
[[ -f "$WORK/lemon/lib/libemon.a" ]] && export LEMON_HOME="$WORK/lemon"
say "== building the single-run programs and generators (log: $LOG)"
ok=0; bad=0
for b in $(conf "$mode.benchmarks"); do
  d="$EVAL/benchmarks/$b"
  for c in $(conf "$mode.columns.$b"); do
    if ( cd "$d" && make --no-print-directory "column-$c" ) >>"$LOG" 2>&1; then say "   ok     $b $c"; ok=$((ok+1))
    else say "   FAILED $b $c"; echo "$b: column $c not built (see work/setup_$mode.log); it is left out" >> "$NA"; bad=$((bad+1)); fi
  done
  if ( cd "$d" && make --no-print-directory generators FAMILIES="$(conf "$mode.families.$b")" ) >>"$LOG" 2>&1; then say "   ok     $b generators"
  else say "   FAILED $b generators"; echo "$b: generators not built (see work/setup_$mode.log)" >> "$NA"; bad=$((bad+1)); fi
done
say "   $ok built, $bad failed"
