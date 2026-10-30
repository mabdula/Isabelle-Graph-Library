#!/bin/bash
# setup_libraries.sh -- fetches the third-party library and solver code this package's competitor
# programs are built on and puts it where their Makefiles expect it.
# Run it once, before `make'; it needs the network.  Every download is compared
# with the md5 of the file the published numbers were made with, and every file
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
# try_optional NAME MD5 URL...   like fetch, but without recording a failure: returns 1 when no source
# answers, and the caller tries another way (fetch_files) before giving the file up.  For third-party code
# that is not redistributed with the evaluation (Andrew Goldberg's hi_pr and PRF).  A copy with the right
# md5 placed in the cache beforehand is used without any download.
try_optional() {
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
  return 1
}
# fetch_files DIR NAME:MD5:SHA1...   the files of an archive no site serves any more, one by one by their
# content from Software Heritage (which keeps every file of the public repositories it has archived, under
# its sha1) into $cache/DIR/, each checked by md5; returns 1 as soon as one cannot be got.
fetch_files() {
  local dir=$1 spec name md5 sha1 f u; shift
  for spec in "$@"; do
    IFS=: read -r name md5 sha1 <<< "$spec"; f="$cache/$dir/$name"
    if [[ -f "$f" && "$(sum "$f")" == "$md5" ]]; then continue; fi
    mkdir -p "$cache/$dir"; u="https://archive.softwareheritage.org/api/1/content/sha1:$sha1/raw/"
    echo "fetch  $dir/$name  <-  $u"; rm -f "$f.part"
    # Software Heritage answers a browser-like agent with a bot check; curl's and wget's own agents pass
    if command -v curl >/dev/null 2>&1; then
      curl -fsSL --connect-timeout 20 --retry 1 --max-time 600 -o "$f.part" "$u" || { echo "       no answer"; return 1; }
    else
      wget -q --timeout=30 --tries=1 -O "$f.part" "$u" || { echo "       no answer"; return 1; }
    fi
    [[ "$(sum "$f.part")" == "$md5" ]] || { echo "       md5 $(sum "$f.part") is not $md5"; rm -f "$f.part"; return 1; }
    mv "$f.part" "$f"
  done
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

if wants '^jgrapht'; then
# JGraphT 1.5.3 and its dependencies, from Maven Central
fetch jgrapht-core-1.5.3.jar f73efc783603c57d8e8e53c90af21e88 https://repo1.maven.org/maven2/org/jgrapht/jgrapht-core/1.5.3/jgrapht-core-1.5.3.jar \
      https://repo.maven.apache.org/maven2/org/jgrapht/jgrapht-core/1.5.3/jgrapht-core-1.5.3.jar \
      https://maven.aliyun.com/repository/central/org/jgrapht/jgrapht-core/1.5.3/jgrapht-core-1.5.3.jar
fetch jheaps-0.14.jar 53dfa9f277efd1d392148eb607d9b4a6 https://repo1.maven.org/maven2/org/jheaps/jheaps/0.14/jheaps-0.14.jar \
      https://repo.maven.apache.org/maven2/org/jheaps/jheaps/0.14/jheaps-0.14.jar \
      https://maven.aliyun.com/repository/central/org/jheaps/jheaps/0.14/jheaps-0.14.jar
fetch apfloat-1.14.0.jar 19e0ad08927787a9c8bdb9c18070723c https://repo1.maven.org/maven2/org/apfloat/apfloat/1.14.0/apfloat-1.14.0.jar \
      https://repo.maven.apache.org/maven2/org/apfloat/apfloat/1.14.0/apfloat-1.14.0.jar \
      https://maven.aliyun.com/repository/central/org/apfloat/apfloat/1.14.0/apfloat-1.14.0.jar
place jgrapht-core-1.5.3.jar competitors/jgrapht/lib/jgrapht-core-1.5.3.jar
place jheaps-0.14.jar competitors/jgrapht/lib/jheaps-0.14.jar
place apfloat-1.14.0.jar competitors/jgrapht/lib/apfloat-1.14.0.jar
fi

if wants '^lemon'; then
# LEMON 1.3.1 (the Makefiles unpack and build it with CMake)
fetch lemon-1.3.1.tar.gz e89f887559113b68657eca67cf3329b5 http://lemon.cs.elte.hu/pub/sources/lemon-1.3.1.tar.gz \
      http://web.archive.org/web/2024id_/http://lemon.cs.elte.hu/pub/sources/lemon-1.3.1.tar.gz
place lemon-1.3.1.tar.gz competitors/lemon/lemon-1.3.1.tar.gz
place lemon-1.3.1.tar.gz competitors/lemon_linked/lemon-1.3.1.tar.gz
fi

if wants '^hipr$'; then
# Goldberg's hi_pr 3.5.  www.avglab.com no longer resolves; the Wayback Machine holds the archive, and
# Software Heritage its files (fetch_files).  It unpacks as 3.5/, renamed to hipr-3.5/ as the study had it,
# and the parser patch (PATCHES-FOR-THIS-STUDY) is applied.
hipr=competitors/hipr/code/hipr-3.5
hipr_url=http://web.archive.org/web/2018id_/http://www.avglab.com/andrew/soft/hipr.tar
hipr_got=
if try_optional hipr.tar cb7bd4cf8db1f15b12e3a9228b6f774b $hipr_url; then
  place hipr.tar $hipr.tar
  rm -rf $hipr && mkdir -p $hipr
  tar xf "$cache/hipr.tar" -C $hipr --strip-components=1 && hipr_got=1
elif fetch_files hipr-3.5 \
       COPYRIGHT:3d4e6e287d82fb44e24cf7bed5b5cc4f:62273550a92661b0f5252675156932972a467dde \
       README:9be0cebffd3700e6ce6bc2aeaf72d6a8:4b341aea515398126edcebddf6b4778dc9b9dc4a \
       VERSION:47c85a0334acd897a70276fb94364d29:5902646c79a2cba79ac3052421336ed68defca8c \
       hi_pr.c:d2b09d39c97b4294be9543e58b569ed5:381cb67925f6748ff7655dbb0e84ba456a7788fd \
       makefile:71a3a5b28da1d09271c2737a10b51c6c:0fe0e05338b55ac87a2ae24894aa27639052bb67 \
       parser.c:de99c4800e1dfa2e0c376b41531175a0:c5aa62aed11059ab2a6964584147d21616ac30ad \
       sample.inp:db1779cdd45ae5c03d01c5aac2f28f26:16d4358a19d729a9eb09870b573e9b62c6b3b2fb \
       timer.c:7b7b24b6dd57f5fa90f7d9689d055aba:2e57f174d10494b9d5e6772198f323a91f33ab0f \
       types.h:c4806e95cc80d90149e22f21d3723e31:6c51ecf9cef7d84cb70b905e0ed5ad495d7720a0; then
  rm -rf $hipr && mkdir -p $hipr && cp "$cache"/hipr-3.5/* $hipr/ && hipr_got=1
fi
if [[ -n "$hipr_got" ]]; then
  note $hipr
  patch -s $hipr/parser.c competitors/hipr/parser.c.patch
  check $hipr/hi_pr.c d2b09d39c97b4294be9543e58b569ed5
  check $hipr/parser.c b9f61e6b7d5a45ac9b3cbef0585781b8
else
  touch "$cache/hipr.tar.unreachable"; missing hipr.tar cb7bd4cf8db1f15b12e3a9228b6f774b $hipr_url
  not_available "push_relabel/competitors/hipr: hi_pr 3.5 (hipr.tar) is not available; the hi_pr column of Tables 19 to 21 cannot be run"
fi
fi

echo "setup_libraries.sh complete: push_relabel"
