#!/bin/bash
# afp.sh MODE -- fetches the AFP entries that MODE's Isabelle sessions need (setup/afp_entries.txt: the Isabelle2025-2
# release branch of the AFP, pinned to one state) into work/isabelle/afp/thys, entry by entry from Heptapod, or else
# from an archive of the whole branch, and writes the ROOTS file that lists the entries present.  MODE is 8h or full
# (the sessions of the code exports), or jedit (every entry the library needs; browse_library_jedit.sh).
set -uo pipefail
EVAL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "$EVAL/setup/lib.sh"
mode=$1
afp="$WORK/isabelle/afp/thys"; dl="$WORK/downloads/afp"; mkdir -p "$afp" "$dl"
# The pinned state of the AFP's Isabelle2025-2 release branch: Heptapod changeset $cs = GitHub mirror commit $gh.
cs=c931af8d9eb959e1554fe07c95b630c8f3bc9ab3
gh=fa30b560ab754bfbb7a721ee45a921d4b3c04358
gh_tar="$dl/mirror-afp-2025-2-$gh.tar.gz"; gh_md5=9c0f4373a61eb0ef5853d3511abb119e
cur_tar="$dl/afp-current.tar.gz"

say "== AFP entries for $mode (setup/afp_entries.txt)"
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
    say "   AFP entries not available: ${still[*]}"; echo "AFP entries ${still[*]} not available; the Isabelle sessions of $mode cannot be built or opened" >> "$NA"; exit 1
  fi
fi
ls -1 "$afp" | while read -r e; do [[ -f "$afp/$e/.installed" ]] && echo "$e"; done > "$afp/ROOTS"
say "   AFP: $(wc -l < "$afp/ROOTS") entries in $afp"
