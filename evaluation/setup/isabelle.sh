#!/bin/bash
# isabelle.sh MODE -- the Isabelle part of the setup: fetches the AFP entries the mode's sessions need
# (setup/afp_entries.txt: the Isabelle2025-2 release branch of the AFP, pinned to one state, entry by entry),
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
afp="$WORK/isabelle/afp/thys"; dl="$WORK/downloads/afp"; mkdir -p "$afp" "$dl"
# The pinned state of the AFP's Isabelle2025-2 release branch: Heptapod changeset $cs = GitHub mirror commit $gh.
cs=c931af8d9eb959e1554fe07c95b630c8f3bc9ab3
gh=fa30b560ab754bfbb7a721ee45a921d4b3c04358
gh_tar="$dl/mirror-afp-2025-2-$gh.tar.gz"; gh_md5=9c0f4373a61eb0ef5853d3511abb119e
cur_tar="$dl/afp-current.tar.gz"

say "== AFP entries for $sessions (setup/afp_entries.txt)"
missing=()
while read -r entry md5 modes; do
  [[ -z "$entry" || "$entry" == \#* ]] && continue
  # shellcheck disable=SC2086
  has "$mode" $modes || continue
  if [[ -f "$afp/$entry/.installed" ]]; then say "   have   $entry"; continue; fi
  if try_fetch "$dl/$entry.tar.gz" "$md5" "https://foss.heptapod.net/isa-afp/afp-2025-2/-/archive/$cs/afp-2025-2-$cs.tar.gz?path=thys/$entry"; then
    rm -rf "${afp:?}/$entry"; tar xzf "$dl/$entry.tar.gz" -C "$afp" --strip-components=2 >>"$LOG" 2>&1 && touch "$afp/$entry/.installed" && say "   fetch  $entry" || missing+=("$entry")
  else missing+=("$entry"); fi
done < "$EVAL/setup/afp_entries.txt"
if [[ ${#missing[@]} -gt 0 ]]; then
  say "   ${#missing[@]} entries did not come from Heptapod (${missing[*]}); trying the whole release branch instead"
  tar_=
  if fetch_file "$gh_tar" "$gh_md5" "https://github.com/isabelle-prover/mirror-afp-2025-2/archive/$gh.tar.gz"; then tar_=$gh_tar
  elif fetch_file "$cur_tar" - "https://www.isa-afp.org/release/afp-current.tar.gz"; then tar_=$cur_tar
    say "   NOTE:  afp-current.tar.gz is the AFP for the current Isabelle release and is not pinned; it is right while Isabelle2025-2 is the current release"
  fi
  still=()
  for entry in "${missing[@]}"; do
    if [[ -n "$tar_" ]] && tar xzf "$tar_" -C "$afp" --strip-components=2 --wildcards "*/thys/$entry/*" >>"$LOG" 2>&1 && [[ -d "$afp/$entry" ]]; then touch "$afp/$entry/.installed"; say "   unpack $entry (from $(basename "$tar_"))"
    else still+=("$entry"); fi
  done
  if [[ ${#still[@]} -gt 0 ]]; then
    say "   AFP entries not available: ${still[*]}"; echo "AFP entries ${still[*]} not available; the Isabelle build of $sessions cannot run" >> "$NA"; exit 1
  fi
fi
ls -1 "$afp" | while read -r e; do [[ -f "$afp/$e/.installed" ]] && echo "$e"; done > "$afp/ROOTS"
say "   AFP: $(wc -l < "$afp/ROOTS") entries in $afp"

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
