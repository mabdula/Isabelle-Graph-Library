#!/bin/bash
# setup_libraries.sh -- fetches the third-party code the oracle is built from (CSA) and the
# unmodified files the oracle's modifications are diffed against.
# Run it once, before `make'; it needs the network.  Every download is compared
# with the md5 of the file the numbers of the paper appendix were made with, and every file
# the script derives (an unpacked source, a patched copy) with the md5 of the
# copy that was used for the paper; a mismatch stops the script.
#
#   ./setup_libraries.sh            fetch, check, place
#
# Needs: bash, curl (or wget), tar, patch, md5sum; python3 where a zip is
# unpacked.  Downloads are kept in $REPRO_CACHE (default: .downloads beside
# this script), so the other setup script and the other packages, given the
# same cache, do not fetch a file twice.  The sources below are the places the
# files were taken from for the paper; where a site has since gone or answers
# unreliably, the Wayback Machine copy of the same bytes is listed too (its
# "id_" form returns the file unchanged).  Any other copy with the same md5 is
# as good: put it into the cache under the same name and the script uses it.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$here"
# Options: --columns "<name> ..." fetches only what those columns need (all when absent); --families "<name> ..."
# only the generators and instances of those families; --roads none|NY|all the USA-road-t networks (default: all).
columns= families= roads=all
while [[ $# -gt 0 ]]; do case $1 in
  --columns) columns=$2; shift 2;; --families) families=$2; shift 2;; --roads) roads=$2; shift 2;;
  *) echo "usage: $0 [--columns \"...\"] [--families \"...\"] [--roads none|NY|all]" >&2; exit 2;; esac; done
# wants REGEX   is one of the wanted columns or families matched by REGEX?  (everything is, when neither was given)
wants() { [[ -z "$columns$families" ]] && return 0; local x; for x in $columns $families; do [[ "$x" =~ $1 ]] && return 0; done; return 1; }
cache="${REPRO_CACHE:-$here/.downloads}"
manifest="$here/.setup_libraries_files"
UA="Mozilla/5.0 (IsaGraphLib evaluation)"   # coral.ise.lehigh.edu refuses curl's default agent

mkdir -p "$cache"
sum() { md5sum "$1" | cut -c1-32; }
note() { echo "$1" >> "$manifest"; }
# fetch NAME MD5 URL...   -> $cache/NAME, verified
fetch() {
  local name=$1 md5=$2 f u; shift 2; f="$cache/$name"
  if [[ -f "$f" && "$(sum "$f")" == "$md5" ]]; then echo "have   $name"; return 0; fi
  if [[ -f "$f.unreachable" ]]; then echo "skip   $name: could not be downloaded earlier in this setup (see NOT_AVAILABLE.txt)"; return 0; fi
  for u in "$@"; do
    echo "fetch  $name  <-  $u"; rm -f "$f.part"
    if command -v curl >/dev/null 2>&1; then
      curl -fsSL -A "$UA" --connect-timeout 30 --retry 2 --speed-limit 1024 --speed-time 60 --max-time 3600 -o "$f.part" "$u" || { echo "       no answer"; continue; }
    else
      wget -q -U "$UA" --timeout=60 --tries=2 -O "$f.part" "$u" || { echo "       no answer"; continue; }
    fi
    if [[ "$(sum "$f.part")" == "$md5" ]]; then mv "$f.part" "$f"; return 0; fi
    echo "       md5 $(sum "$f.part") is not $md5, trying the next source"; rm -f "$f.part"
  done
  touch "$f.unreachable"
  missing "$name" "$md5" "$@"
  return 0
}
# fetch_optional NAME MD5 URL...   like fetch, but returns 1 instead of stopping: for third-party code
# that is not redistributed with the evaluation (Andrew Goldberg's hi_pr, PRF and CSA).  A copy with the
# right md5 placed in the cache beforehand is used without any download.
fetch_optional() {
  local name=$1 md5=$2 f u; shift 2; f="$cache/$name"
  if [[ -f "$f" && "$(sum "$f")" == "$md5" ]]; then echo "have   $name"; return 0; fi
  if [[ -f "$f.unreachable" ]]; then echo "skip   $name: could not be downloaded earlier in this setup (see NOT_AVAILABLE.txt)"; return 1; fi
  for u in "$@"; do
    echo "fetch  $name  <-  $u"; rm -f "$f.part"
    if command -v curl >/dev/null 2>&1; then
      curl -fsSL -A "$UA" --connect-timeout 20 --retry 1 --speed-limit 1024 --speed-time 60 --max-time 3600 -o "$f.part" "$u" || { echo "       no answer"; continue; }
    else
      wget -q -U "$UA" --timeout=30 --tries=1 -O "$f.part" "$u" || { echo "       no answer"; continue; }
    fi
    if [[ "$(sum "$f.part")" == "$md5" ]]; then mv "$f.part" "$f"; return 0; fi
    echo "       md5 $(sum "$f.part") is not $md5, trying the next source"; rm -f "$f.part"
  done
  touch "$f.unreachable"
  missing "$name" "$md5" "$@"
  return 1
}
# not_available TEXT     records, in NOT_AVAILABLE.txt at the top of evaluation/, what is left out
not_available() { echo "$1" >> "$here/../../NOT_AVAILABLE.txt"; echo "NOTE:  $1"; }
# missing NAME MD5 URL...   a file that could not be downloaded: say where to get it by hand and where to
# put it, record it in NOT_AVAILABLE.txt at the top of evaluation/, and go on without it (what is built
# on it is left out until the file is there and the setup is run again)
missing() {
  local name=$1 md5=$2; shift 2
  echo ""
  echo "NOTE:  $name could not be downloaded.  Fetch it by hand from"
  local u; for u in "$@"; do echo "         $u"; done
  echo "       (md5 $md5), put it at"
  echo "         $cache/$name"
  echo "       and run the setup again; everything built on it is left out until then."
  echo ""
  echo "$(basename "$here"): $name (md5 $md5) not downloaded; put it at $cache/$name and run the setup again; sources: $*" >> "$here/../../NOT_AVAILABLE.txt"
}
# have NAME     is the file in the cache?
have() { [[ -f "$cache/$1" ]]; }
# place NAME DEST       copy from the cache to DEST (relative to this directory)
place() { have "$1" || { echo "skip   $2 ($1 was not downloaded)"; return 0; }; mkdir -p "$(dirname "$2")"; cp "$cache/$1" "$2"; note "$2"; echo "place  $2"; }
# check DEST MD5        a derived file must be byte for byte what was used
check() { [[ -f "$1" ]] || { echo "skip   $1 (not made: its source was not downloaded)"; return 0; }; [[ "$(sum "$1")" == "$2" ]] || { echo "ERROR: $1 has md5 $(sum "$1"), expected $2" >&2; exit 1; }; note "$1"; echo "ok     $1"; }

if wants '^hybrid$'; then
# CSA, the DIMACS reference assignment solver (Goldberg and Kennedy), the
# Flow Challenge 2.0's tarball
if fetch_optional csa-flows20.tar.gz e07d8ad4b68bba1096f39eba7cfd7dda https://coral.ise.lehigh.edu//wp-content/uploads/flows20/csa-flows20.tar.gz http://web.archive.org/web/2026id_/https://coral.ise.lehigh.edu/wp-content/uploads/flows20/csa-flows20.tar.gz; then
  place csa-flows20.tar.gz code/oracle/csa-flows20.tar.gz
  # the unmodified distribution files the oracle was made from, so that
  # code/oracle/ORACLE_MODIFICATIONS.diff can be checked with  diff -ru pristine_csa csa
  mkdir -p code/oracle/pristine_csa
  tar xzf "$cache/csa-flows20.tar.gz" -O csa-flows20/csa/main.c > code/oracle/pristine_csa/main.c
  tar xzf "$cache/csa-flows20.tar.gz" -O csa-flows20/csa/queue.c > code/oracle/pristine_csa/queue.c
  tar xzf "$cache/csa-flows20.tar.gz" -O csa-flows20/csa/stack.c > code/oracle/pristine_csa/stack.c
  tar xzf "$cache/csa-flows20.tar.gz" -O csa-flows20/csa/timer.c > code/oracle/pristine_csa/timer.c
  tar xzf "$cache/csa-flows20.tar.gz" -O csa-flows20/csa/csa_defs.h > code/oracle/pristine_csa/csa_defs.h
  tar xzf "$cache/csa-flows20.tar.gz" -O csa-flows20/csa/parse.c > code/oracle/pristine_csa/parse.c
  tar xzf "$cache/csa-flows20.tar.gz" -O csa-flows20/csa/prec_costs/csa_types.h > code/oracle/pristine_csa/csa_types.h
  tar xzf "$cache/csa-flows20.tar.gz" -O csa-flows20/csa/prec_costs/debug.c > code/oracle/pristine_csa/debug.c
  tar xzf "$cache/csa-flows20.tar.gz" -O csa-flows20/csa/prec_costs/refine.c > code/oracle/pristine_csa/refine.c
  tar xzf "$cache/csa-flows20.tar.gz" -O csa-flows20/csa/prec_costs/update_epsilon.c > code/oracle/pristine_csa/update_epsilon.c
  check code/oracle/pristine_csa/csa_defs.h 6699744e6e13319cec127052a100ba6e
  check code/oracle/pristine_csa/csa_types.h 3188067a037cee138eeb1d4ca392fb2a
  check code/oracle/pristine_csa/debug.c 3b480055c66925e2c6922f1fa7abcce0
  check code/oracle/pristine_csa/main.c 8866450e88135d9ea81d875c085c5aaa
  check code/oracle/pristine_csa/parse.c d465887324e5e271be14f9858644e0f7
  check code/oracle/pristine_csa/queue.c 8ba83aed949d820c699bf8c47a74948e
  check code/oracle/pristine_csa/refine.c 1ef323b317dd4f0100f99798ec1f922d
  check code/oracle/pristine_csa/stack.c 25ba31d18feb4dd70e26819c07992248
  check code/oracle/pristine_csa/timer.c 538574d38c290d9726587dc1d326c243
  check code/oracle/pristine_csa/update_epsilon.c 4c6bf143ed27fa19d9294a2a72f22dbb
  note code/oracle/pristine_csa
  # code/oracle/csa/: the oracle's sources, the unmodified files plus ORACLE_MODIFICATIONS.diff
  rm -rf code/oracle/csa && mkdir -p code/oracle/csa
  for f in COPYRIGHT README; do tar xzf "$cache/csa-flows20.tar.gz" -O csa-flows20/csa/$f > code/oracle/csa/$f; done
  for f in csa_defs.h csa_types.h debug.c queue.c stack.c timer.c update_epsilon.c; do cp code/oracle/pristine_csa/$f code/oracle/csa/$f; done
  for f in main.c parse.c refine.c; do sed 's/\r$//' code/oracle/pristine_csa/$f > code/oracle/csa/$f; done
  patch -s -p1 -d code/oracle/csa --no-backup-if-mismatch < code/oracle/ORACLE_MODIFICATIONS.diff
  check code/oracle/csa/COPYRIGHT a007db23e8065bc682db09000246f948
  check code/oracle/csa/README 7417352aea6ea73cf656d7ee8a3d727e
  check code/oracle/csa/main.c 27570a685d873b4baf1a12409aa39b72
  check code/oracle/csa/parse.c a6025b16e9257e9c92e0eef9884e9e25
  check code/oracle/csa/refine.c 8cac59fefc7133c177adadfa41074ba5
  note code/oracle/csa
else
  not_available "hybrid_bipartite_matching: CSA (csa-flows20.tar.gz, the oracle) is not available; Tables 35 to 37 cannot be run"
fi
fi

echo "setup_libraries.sh complete: hybrid_bipartite_matching"
