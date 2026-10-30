#!/bin/bash
# setup_instances.sh -- fetches the generators (and, where the study used them, the downloadable
# instances) and puts them where instances/generators/Makefile expects them.
# Run it once, before `make'; it needs the network.  Every download is compared
# with the md5 of the file the numbers of the paper appendix were made with, and every file
# the script derives (an unpacked source, a patched copy) with the md5 of the
# copy that was used for the paper; a mismatch stops the script.
#
#   ./setup_instances.sh            fetch, check, place
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
manifest="$here/.setup_instances_files"
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

if wants '^(low-cost|two-cost|geometric)$'; then
# The First DIMACS Challenge assignment generators (pristine files), and the
# patched copies that compile today, made by applying the patches beside them
fetch assign.c 98bba042619c8f1c1664b74631958a86 https://archive.dimacs.rutgers.edu/pub/netflow/generators/network/assign.c \
      http://web.archive.org/web/2026id_/https://archive.dimacs.rutgers.edu/pub/netflow/generators/network/assign.c
fetch twocost.a f51724183524b2a2d7dbb19bd1b32dce https://archive.dimacs.rutgers.edu/pub/netflow/generators/network/twocost.a \
      http://web.archive.org/web/2026id_/https://archive.dimacs.rutgers.edu/pub/netflow/generators/network/twocost.a
fetch geomasn.a e390c3b59ba217ce8c1e5f2112c5b1ad https://archive.dimacs.rutgers.edu/pub/netflow/generators/network/geomasn.a \
      http://web.archive.org/web/2026id_/https://archive.dimacs.rutgers.edu/pub/netflow/generators/network/geomasn.a
fetch dcube.c 3b1fcbbb4e1689444c20954fa7042e28 https://archive.dimacs.rutgers.edu/pub/netflow/generators/matching/dcube.c \
      http://web.archive.org/web/2026id_/https://archive.dimacs.rutgers.edu/pub/netflow/generators/matching/dcube.c
fetch readme 54e2cf2e11d86d0df42d9288a8fee68d https://archive.dimacs.rutgers.edu/pub/netflow/generators/network/readme \
      http://web.archive.org/web/2026id_/https://archive.dimacs.rutgers.edu/pub/netflow/generators/network/readme
place assign.c instances/generators/assign.c
place twocost.a instances/generators/twocost.a
place geomasn.a instances/generators/geomasn.a
place dcube.c instances/generators/dcube.c
place readme instances/generators/readme
mkdir -p instances/generators/build
if have assign.c; then
  patch -s -o instances/generators/build/assign_patched.c instances/generators/assign.c instances/generators/assign.c.patch
  check instances/generators/build/assign_patched.c 7795642305e83d4a64e7bdb843670899
fi
if have dcube.c; then
  patch -s -o instances/generators/build/dcube_patched.c instances/generators/dcube.c instances/generators/dcube.c.patch
  check instances/generators/build/dcube_patched.c 367925ab3fb6e6cffee28cab294df2ea
fi
fi
echo "setup_instances.sh complete: hungarian"
