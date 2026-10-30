#!/bin/bash
# exports.sh SOURCE MODE -- places the code exports the mode measures in work/exports/current/<benchmark>/,
# where every Makefile reads them.  SOURCE is campaign (exports/campaign: the code of the paper's campaign),
# pregenerated (exports/pregenerated: generated from the current library and shipped), or built (written by the
# Isabelle build of setup/isabelle.sh).  setup/export_files.txt lists every file.  A file the build did not
# write is recorded in NOT_AVAILABLE.txt and its column is left out.  work/exports/current/SOURCE.txt records
# where every file came from, with its md5.
set -uo pipefail
EVAL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "$EVAL/setup/lib.sh"
source=$1 mode=$2
case "$source" in campaign|pregenerated|built) ;; *) echo "usage: setup/exports.sh campaign|pregenerated|built MODE" >&2; exit 2 ;; esac
cur="$WORK/exports/current"; rm -rf "$cur"; mkdir -p "$cur"
benchmarks=$(conf "$mode.benchmarks")
say "== code exports: $source -> work/exports/current"
{ echo "# code exports measured by this setup ($source, mode $mode): file, origin, md5"; } > "$cur/SOURCE.txt"
while read -r b f origin; do
  [[ -z "$b" || "$b" == \#* ]] && continue
  # shellcheck disable=SC2086
  has "$b" $benchmarks || continue
  from=
  case "$source:$origin" in
    campaign:*)            from="$EVAL/exports/campaign/$b/$f" ;;
    *:campaign)            from="$EVAL/exports/campaign/$b/$f" ;;
    pregenerated:*|*:pregenerated) from="$EVAL/exports/pregenerated/$b/$f" ;;
    built:*)               from="$EVAL/../$origin" ;;
  esac
  if [[ -f "$from" ]]; then
    mkdir -p "$cur/$b/$(dirname "$f")"; cp "$from" "$cur/$b/$f"
    echo "$b/$f  $(realpath --relative-to="$EVAL/.." "$from")  $(sum "$from")" >> "$cur/SOURCE.txt"
  else
    say "   $b/$f: not found at $from"
    echo "$b: code export $f not found at $(realpath -m --relative-to="$EVAL/.." "$from"); the columns compiled from it are left out" >> "$NA"
  fi
done < "$EVAL/setup/export_files.txt"
sed 's/^/   /' "$cur/SOURCE.txt" | tail -n +2 | tee -a "$LOG"
