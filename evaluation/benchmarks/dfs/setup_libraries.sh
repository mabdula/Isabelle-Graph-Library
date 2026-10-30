#!/bin/bash
# setup_libraries.sh -- fetches the third-party library and solver code this package's competitor
# programs are built on and puts it where their Makefiles expect it.
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

if wants '^jgrapht'; then
# JGraphT 1.5.3 and its dependencies, from Maven Central
fetch jgrapht-core-1.5.3.jar f73efc783603c57d8e8e53c90af21e88 https://repo1.maven.org/maven2/org/jgrapht/jgrapht-core/1.5.3/jgrapht-core-1.5.3.jar \
      https://repo.maven.apache.org/maven2/org/jgrapht/jgrapht-core/1.5.3/jgrapht-core-1.5.3.jar \
      https://maven.aliyun.com/repository/central/org/jgrapht/jgrapht-core/1.5.3/jgrapht-core-1.5.3.jar
fetch jgrapht-opt-1.5.3.jar 16186f39791c4ca131ef00908a0bd984 https://repo1.maven.org/maven2/org/jgrapht/jgrapht-opt/1.5.3/jgrapht-opt-1.5.3.jar \
      https://repo.maven.apache.org/maven2/org/jgrapht/jgrapht-opt/1.5.3/jgrapht-opt-1.5.3.jar \
      https://maven.aliyun.com/repository/central/org/jgrapht/jgrapht-opt/1.5.3/jgrapht-opt-1.5.3.jar
fetch fastutil-8.5.18.jar e8335a737dbff6c6912f31e8cad5730a https://repo1.maven.org/maven2/it/unimi/dsi/fastutil/8.5.18/fastutil-8.5.18.jar \
      https://repo.maven.apache.org/maven2/it/unimi/dsi/fastutil/8.5.18/fastutil-8.5.18.jar \
      https://maven.aliyun.com/repository/central/it/unimi/dsi/fastutil/8.5.18/fastutil-8.5.18.jar
fetch jheaps-0.14.jar 53dfa9f277efd1d392148eb607d9b4a6 https://repo1.maven.org/maven2/org/jheaps/jheaps/0.14/jheaps-0.14.jar \
      https://repo.maven.apache.org/maven2/org/jheaps/jheaps/0.14/jheaps-0.14.jar \
      https://maven.aliyun.com/repository/central/org/jheaps/jheaps/0.14/jheaps-0.14.jar
fetch apfloat-1.14.0.jar 19e0ad08927787a9c8bdb9c18070723c https://repo1.maven.org/maven2/org/apfloat/apfloat/1.14.0/apfloat-1.14.0.jar \
      https://repo.maven.apache.org/maven2/org/apfloat/apfloat/1.14.0/apfloat-1.14.0.jar \
      https://maven.aliyun.com/repository/central/org/apfloat/apfloat/1.14.0/apfloat-1.14.0.jar
place jgrapht-core-1.5.3.jar competitors/jgrapht/lib/jgrapht-core-1.5.3.jar
place jgrapht-opt-1.5.3.jar competitors/jgrapht/lib/jgrapht-opt-1.5.3.jar
place fastutil-8.5.18.jar competitors/jgrapht/lib/fastutil-8.5.18.jar
place jheaps-0.14.jar competitors/jgrapht/lib/jheaps-0.14.jar
place apfloat-1.14.0.jar competitors/jgrapht/lib/apfloat-1.14.0.jar
place jgrapht-core-1.5.3.jar competitors/jgrapht_hashgraph/lib/jgrapht-core-1.5.3.jar
place jgrapht-opt-1.5.3.jar competitors/jgrapht_hashgraph/lib/jgrapht-opt-1.5.3.jar
place fastutil-8.5.18.jar competitors/jgrapht_hashgraph/lib/fastutil-8.5.18.jar
place jheaps-0.14.jar competitors/jgrapht_hashgraph/lib/jheaps-0.14.jar
place apfloat-1.14.0.jar competitors/jgrapht_hashgraph/lib/apfloat-1.14.0.jar
fi

if wants '^lemon'; then
# LEMON 1.3.1 (the Makefiles unpack and build it with CMake)
fetch lemon-1.3.1.tar.gz e89f887559113b68657eca67cf3329b5 http://lemon.cs.elte.hu/pub/sources/lemon-1.3.1.tar.gz \
      http://web.archive.org/web/2024id_/http://lemon.cs.elte.hu/pub/sources/lemon-1.3.1.tar.gz
place lemon-1.3.1.tar.gz competitors/lemon/lemon-1.3.1.tar.gz
place lemon-1.3.1.tar.gz competitors/lemon_linked/lemon-1.3.1.tar.gz
fi

echo "setup_libraries.sh complete: dfs"
