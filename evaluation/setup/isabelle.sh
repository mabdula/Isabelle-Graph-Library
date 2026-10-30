#!/bin/bash
# isabelle.sh MODE -- the Isabelle part of the setup: fetches the AFP entries the mode's sessions need (setup/afp.sh),
# builds the sessions modes.conf names for the mode with the Isabelle2025-2 that toolchains.sh unpacked, and leaves
# the generated code where the export theories write it (<session dir>/<Name>_code_exports/).
# No LaTeX document is produced, so no TeX is needed: the library's ROOT files ask for one (ROOT options override
# -o document=false), so the build reads a copy of them, work/isabelle/roots/ROOT: the same sessions, each pointing
# at its original directory (an absolute `in' path), with the document switched off.
# Log of the build: work/isabelle_build.log.
set -uo pipefail
EVAL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "$EVAL/setup/lib.sh"
# shellcheck disable=SC1091
source "$WORK/env.sh"
mode=$1
sessions=$(conf "$mode.isabelle_sessions")
libdirs=$(for d in $(conf "$mode.isabelle_dirs"); do printf -- "%s/../%s " "$EVAL" "$d"; done)
roots="$WORK/isabelle/roots"
[[ -x "$ISABELLE" ]] || { say "   Isabelle2025-2 is not available (see above); the code exports cannot be built"; exit 1; }
bash "$EVAL/setup/afp.sh" "$mode" || exit 1
afp="$WORK/isabelle/afp/thys"

mkdir -p "$roots"; : > "$roots/ROOT"
for d in $libdirs; do
  d=$(cd "$d" && pwd) || fail "no library directory $d"
  { echo "(* from $d/ROOT *)"
    awk -v lib="$d" '
      /^[[:space:]]*session[[:space:]]/ && match($0, /^[[:space:]]*session[[:space:]]+("[^"]+"|[A-Za-z0-9_.-]+)/) {
        head = substr($0, 1, RLENGTH); rest = substr($0, RLENGTH + 1); grp = ""; dir = ""
        if (match(rest, /^[[:space:]]*\([^)]*\)/)) { grp = substr(rest, 1, RLENGTH); rest = substr(rest, RLENGTH + 1) }
        if (match(rest, /^[[:space:]]+in[[:space:]]+("[^"]+"|[A-Za-z0-9_.\/-]+)/)) { dir = substr(rest, 1, RLENGTH); rest = substr(rest, RLENGTH + 1); sub(/^[[:space:]]+in[[:space:]]+/, "", dir); gsub(/"/, "", dir) }
        if (match(rest, /^[[:space:]]*=/)) { print head grp " in \"" lib (dir == "" ? "" : "/" dir) "\"" rest; next }
      }
      { gsub(/document[[:space:]]*=[[:space:]]*pdf/, "document = false"); print }' "$d/ROOT"
    echo; } >> "$roots/ROOT"
done
say "== isabelle build $sessions (sessions of $(conf "$mode.isabelle_dirs" | wc -w) library directories via $roots/ROOT; log: $WORK/isabelle_build.log)"
t0=$(date +%s)
"$ISABELLE" build -j 1 -v -o document=false -d "$roots" -d "$afp" $sessions > "$WORK/isabelle_build.log" 2>&1
rc=$?
tail -3 "$WORK/isabelle_build.log" | sed 's/^/   /' | tee -a "$LOG"
say "   isabelle build: rc=$rc, $(( ($(date +%s) - t0) / 60 )) min"
[[ $rc -eq 0 ]] || echo "isabelle build of $sessions failed (rc=$rc), see work/isabelle_build.log" >> "$NA"
exit $rc
