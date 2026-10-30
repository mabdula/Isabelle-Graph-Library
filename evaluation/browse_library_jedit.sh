#!/bin/bash
# browse_library_jedit.sh [THEORY ...] -- opens the paper's index theories (../Paper_Index, one per section of the paper) in
# Isabelle/jEdit, to browse the library from them: every listing of the paper is an entry there that links to its theorem,
# definition or locale in the library.  Downloads Isabelle2025-2 and the AFP entries the library needs into work/ (shared
# with the setup of the experiments) and builds HOL-Library, the session the index theories start from, and nothing more:
# Isabelle/jEdit checks the opened theories and the library theories they import while they are shown.
# THEORY: an index theory by name (Paper_Index/README.md lists them), several at once, or all;
# the default is Index_00_Introduction_Main_Theorems.  Needs a display.  Log: work/setup_jedit.log.
set -uo pipefail
EVAL="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
index="$EVAL/../Paper_Index"
usage() {
  echo "usage: browse_library_jedit.sh [THEORY ...]   (default: Index_00_Introduction_Main_Theorems)" >&2
  echo "THEORY: one of the index theories, or all:" >&2
  find "$index" -mindepth 2 -name 'Index_*.thy' | sed 's|.*/||; s|\.thy$||' | sort | sed 's/^/   /' >&2
  exit 2
}
[[ $# -gt 0 ]] || set -- Index_00_Introduction_Main_Theorems
files=()
for t in "$@"; do
  if [[ "$t" == all ]]; then while read -r f; do files+=("$f"); done < <(find "$index" -mindepth 2 -name 'Index_*.thy' | sort)
  else f=$(find "$index" -mindepth 2 -name "$t.thy" | head -1); [[ -n "$f" ]] || { echo "no index theory $t" >&2; usage; }; files+=("$f"); fi
done
export EVAL WORK="$EVAL/work" LOG="$EVAL/work/setup_jedit.log"
mkdir -p "$WORK"; : > "$LOG"
# shellcheck disable=SC1091
source "$EVAL/setup/lib.sh"
need tar tar; need md5sum coreutils
say "== Isabelle/jEdit on ${files[*]#"$index/"}, $(date)"
bash "$EVAL/setup/toolchains.sh" jedit built || fail "toolchains.sh failed"
# shellcheck disable=SC1091
source "$WORK/env.sh"
[[ -x "$ISABELLE" ]] || fail "Isabelle2025-2 is not available (see above)"
bash "$EVAL/setup/afp.sh" jedit || fail "AFP entries are missing (see above)"
afp="$WORK/isabelle/afp/thys"
say "== isabelle build HOL-Library (the session the index theories start from; log: work/jedit_build.log)"
t0=$(date +%s)
"$ISABELLE" build -b HOL-Library > "$WORK/jedit_build.log" 2>&1 || fail "the build of HOL-Library failed, see work/jedit_build.log"
say "   done in $(( ($(date +%s) - t0) / 60 )) min"
say "== isabelle jedit -l HOL-Library -d .. -d work/isabelle/afp/thys ${files[*]#"$index/"}"
exec "$ISABELLE" jedit -d "$EVAL/.." -d "$afp" -l HOL-Library "${files[@]}"
