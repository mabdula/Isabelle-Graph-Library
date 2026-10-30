#!/bin/bash
# setup_instances.sh -- fetches the generators (and, where the study used them, the downloadable
# instances) and puts them where instances/generators/Makefile expects them.
# Run it once, before `make'; it needs the network.  Every download is compared
# with the md5 of the file the published numbers were made with, and every file
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

# The three maximum-flow generators.  ak.c is from PRF 1.8 (Cherkassky and
# Goldberg), on the Wayback Machine only; genrmf is the Flow Challenge 2.0's
# corrected genrmf; washington.c the challenge's copy of the Washington generator.
if wants '^ak$'; then
if fetch_optional prf.tar 9d0ffcf2fce3e3fabfbc8743bfad7bc5 http://web.archive.org/web/2018id_/http://www.avglab.com/andrew/soft/prf.tar; then
  rm -rf "$cache/prf" && mkdir -p "$cache/prf" && tar xf "$cache/prf.tar" -C "$cache/prf"
  mkdir -p instances/generators/ak
  cp "$cache/prf/1.8/ak.c" instances/generators/ak/ak.c
  for f in README COPYRIGHT; do [[ -f "$cache/prf/1.8/$f" ]] && cp "$cache/prf/1.8/$f" instances/generators/ak/$f && note instances/generators/ak/$f; done
  check instances/generators/ak/ak.c a55236f7732aa733b3c1b5ebd62da00d
else
  not_available "push_relabel/instances/generators/ak: PRF 1.8 (prf.tar, the AK generator) is not available; the AK family of Table 21 cannot be generated"
fi
fi
if wants '^wash-rlg-long$'; then
fetch washington.c 11c0e0b48daf9a08599ab0811d9cd0f8 https://coral.ise.lehigh.edu//wp-content/uploads/washington.c \
      http://web.archive.org/web/2026id_/https://coral.ise.lehigh.edu/wp-content/uploads/washington.c
place washington.c instances/generators/washington/washington.c
fi
if wants '^rmf-long$'; then
fetch genrmfDimacs.zip 9b9f8bda810e02c842b4111066508063 http://coral.ise.lehigh.edu/flow-challenge-2-0/files/2026/09/genrmfDimacs.zip \
      http://web.archive.org/web/2026id_/http://coral.ise.lehigh.edu/flow-challenge-2-0/files/2026/09/genrmfDimacs.zip
if have genrmfDimacs.zip; then
  rm -rf instances/generators/genrmfDimacs
  python3 -c 'import sys, zipfile; zipfile.ZipFile(sys.argv[1]).extractall(sys.argv[2])' "$cache/genrmfDimacs.zip" instances/generators
  note instances/generators/genrmfDimacs
  check instances/generators/genrmfDimacs/genrmf.c 47718b07ece55b0e57236ae0a1fb9f30
  check instances/generators/genrmfDimacs/genmain.c a312ee41818590d1713c4ae1689fedd2
  check instances/generators/genrmfDimacs/genio.c 92c8a156576f296e0984f5891dd41a0d
  check instances/generators/genrmfDimacs/genio.h 338fe4a0d2f0d17e7234c17329ff6e4a
  check instances/generators/genrmfDimacs/gen_maxflow_typedef.h ab03a99052d661bec294fc4fbec10e40
  check instances/generators/genrmfDimacs/math_to_gcc.h ee6cc15631f525487b0aa8fe8a5f9e99
  check instances/generators/genrmfDimacs/makefile bf8a781ac25fb6495b0029b9ee5b3702
fi
fi
echo "setup_instances.sh complete: push_relabel"
