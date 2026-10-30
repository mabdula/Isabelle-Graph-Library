#!/bin/bash
# setup_instances.sh -- fetches the generators (and, where the study used them, the downloadable
# instances) and puts them where instances/generators/Makefile expects them.
# Run it once, before `make'; it needs the network.  Every download is compared
# with the md5 of the file the numbers of the paper appendix were made with, and every file
# the script derives (an unpacked source, a patched copy) with the md5 of the
# copy that was used for the paper; a mismatch stops the script.
#
#   ./setup_instances.sh            fetch, check, place (the road networks named by --roads)
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

if wants '^(Square-n|Long-n|Dense-n)$'; then
# The 9th DIMACS Challenge code suite: the generators spgrid and sprand and the
# scripts that drove them.  The two scripts are extracted from the suite and the
# edits made for the study (TRIALS, paths) applied from the patches beside them.
fetch ch9-1.1.tar.gz 96c9761eec9dcd27dfb3711203ee4aa6 http://www.diag.uniroma1.it/~challenge9/code/ch9-1.1.tar.gz \
      https://users.diag.uniroma1.it/challenge9/code/ch9-1.1.tar.gz \
      http://web.archive.org/web/20251111005635id_/http://www.diag.uniroma1.it/~challenge9/code/ch9-1.1.tar.gz
place ch9-1.1.tar.gz instances/generators/ch9-1.1.tar.gz
if have ch9-1.1.tar.gz; then
  tar xzf "$cache/ch9-1.1.tar.gz" -O ch9-1.1/scripts/genLong-n.gr.pl > instances/generators/genLong-n.gr.pl
  patch -s instances/generators/genLong-n.gr.pl instances/generators/genLong-n.gr.pl.patch
  check instances/generators/genLong-n.gr.pl b8b3f6849893b575aad384861066793c
  tar xzf "$cache/ch9-1.1.tar.gz" -O ch9-1.1/scripts/genSquare-n.gr.pl > instances/generators/genSquare-n.gr.pl
  patch -s instances/generators/genSquare-n.gr.pl instances/generators/genSquare-n.gr.pl.patch
  check instances/generators/genSquare-n.gr.pl 152584bb7f10226ba593133626cf56b6
fi
fi
# The road networks: the 9th DIMACS Challenge's USA-road-t files, downloaded
# as the study did, each archive checked against the md5 recorded in
# instances/seeds/USA-road-t.txt and each unpacked file against
# instances/MD5SUM_instances.txt.  All twelve by default (about 1.5 GB of
# archives, kept in the cache; 7 GB unpacked, shared between dfs, bfs and
# dijkstra by hard links); --no-roads skips them.  When the DIMACS site does not
# answer, the Wayback Machine's captures of the same archives are used.  A network
# neither delivers is recorded in NOT_AVAILABLE.txt and the script goes on.
case "$roads" in all) roads=$(grep -oE "USA-road-t\.[A-Z]+\.gr\.gz" instances/seeds/USA-road-t.txt | sed -E "s/USA-road-t\.([A-Z]+)\.gr\.gz/\1/" | tr "\n" " ");; none) roads=;; esac
wants '^USA-road-t$' || roads=
# wayback REGION: the Wayback Machine's captures of the archive (host:timestamp), byte for byte the files the study used
wayback() { case $1 in
  BAY) echo 'www.diag:20240122164126 www.dis:20161221082807';;
  CAL) echo 'www.diag:20240123141838 www.dis:20161221085328';;
  COL) echo 'www.diag:20240123142026 www.dis:20161221082151';;
  CTR) echo 'www.dis:20161221084523';;
  E) echo 'www.dis:20161221083917';;
  FLA) echo 'www.dis:20161221091815';;
  LKS) echo 'www.diag:20240123142034 www.dis:20161221092202';;
  NE) echo 'www.diag:20240122163738 www.dis:20161221092445';;
  NW) echo 'www.diag:20240123141251 www.dis:20161221090906';;
  NY) echo 'www.diag:20240123141344 www.dis:20161221080431';;
  USA) echo 'www.dis:20161221090240';;
  W) echo 'www.dis:20161221080253';;
  esac; }
for r in $roads; do
  gz=USA-road-t.$r.gr.gz
  md5=$(grep -oE "^ *[0-9a-f]{32}" <<< "$(grep -E " $gz\$" instances/seeds/USA-road-t.txt)" | tr -d " ")
  [[ -n "$md5" ]] || { echo "ERROR: no such road network: $r" >&2; exit 1; }
  wb=; for c in $(wayback $r); do wb="$wb http://web.archive.org/web/${c#*:}id_/http://${c%%:*}.uniroma1.it/challenge9/data/USA-road-t/$gz"; done
  # shellcheck disable=SC2086
  fetch_optional $gz $md5 http://www.diag.uniroma1.it/~challenge9/data/USA-road-t/$gz http://users.diag.uniroma1.it/challenge9/data/USA-road-t/$gz $wb \
    || not_available "$(basename "$here")/instances/USA-road-t/USA-road-t.$r.gr: neither the DIMACS site nor the Wayback Machine delivered $gz; the $r row of the road table cannot be run (rerun ./setup.sh later to fetch it)"
done
# the archives stay in the cache: the measurement script unpacks a network before its first run and deletes the copy after its last

echo "setup_instances.sh complete: bfs"
