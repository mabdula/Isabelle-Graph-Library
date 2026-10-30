#!/bin/bash
# Generate the DIMACS Network Flows 2.0 geometric assignment benchmarks.
#
# Recipe, quoted from the challenge's "Assignment Problem Instances and
# Generators" page:
#
#   Geometric instances: use the DIMACS generator dcube.c and the DIMACS awk
#   script geomasn.a.  Use the dcube parameters as shown below, and the
#   following UNIX command line:
#
#       dcube | awk -f geomasn.a
#
#   dcube parameters are: nodes N, dimension 2, maxloc 1000000, seed K
#   Use N = 2^8, 2^9, 2^10, 2^11, 2^12
#
# The challenge page states that dcube is missing from the DIMACS depository,
# and the tar archive it offers instead answers 403.  dcube.c is in fact still
# in the depository, filed under the matching generators rather than the
# network ones:
#
#   http://archive.dimacs.rutgers.edu/pub/netflow/generators/matching/dcube.c
#
# That is where generators/dcube.c came from, unmodified.  The compiled copy in
# generators/build is patched only enough to build under a modern C compiler
# (see generators/build/dcube_patched.c; diff it against generators/dcube.c).
#
# dcube draws N points uniformly in the square [1,10^6]^2.  geomasn.a makes the
# first N/2 points the left side and the last N/2 the right, and joins every
# left point to every right point with cost equal to the Euclidean distance
# truncated to an integer.  So these are COMPLETE bipartite graphs with
# (N/2)^2 arcs -- dense, unlike the low-cost and two-cost families -- and a
# perfect matching always exists.
#
# One repair is applied to geomasn.a's output: it writes its arc lines with the
# letter "e", while the .asn format (and assign.c, and the DIMACS asnmin.a
# converter) use "a".  Left alone, every reader sees a file with no arcs at
# all.  The letter is rewritten; nothing else about the line is touched.
#
# usage: gen_geometric.sh [--nodes <list>] [--seeds <list>] [outdir]

set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# NOTE: the study ran this script from hungarian/bench with
# root=<study dir>, gen=$root/generators/build/<name>, the awk
# filter in $root/generators and out=$root/instances.  Here everything is
# relative to this directory; nothing else differs from the script as run.
root="$here"
gen="$root/build/dcube"
geomasn="$root/geomasn.a"
out="$root/out"

[[ -x "$gen" ]] || { echo "missing generator: $gen"; exit 1; }
[[ -s "$geomasn" ]] || { echo "missing converter: $geomasn"; exit 1; }

seeds=(1 2 3 4 5 6 7 8 9 10)
nodes_list=(256 512 1024 2048 4096)

while [[ $# -gt 0 ]]; do
  case "$1" in
    --nodes) IFS=',' read -r -a nodes_list <<< "$2"; shift 2;;
    --seeds) IFS=',' read -r -a seeds <<< "$2"; shift 2;;
    *) out="$1"; shift;;
  esac
done

mkdir -p "$out/geometric"

# dcube's main() has no return, so like assign.c its exit status says nothing.
# Each file is validated on its contents instead: it must carry a problem line
# and exactly the number of arc lines that line promises.
check() {
  local f="$1" p arcs
  p=$(grep -m1 '^p asn' "$f") || { echo "FAIL $f: no problem line"; return 1; }
  arcs=$(awk '$1 == "a"' "$f" | wc -l)
  [[ "$arcs" -eq "$(awk '{print $4}' <<<"$p")" ]] \
    || { echo "FAIL $f: $arcs arc lines, problem line says $(awk '{print $4}' <<<"$p")"; return 1; }
  return 0
}

for n in "${nodes_list[@]}"; do
  for k in "${seeds[@]}"; do
    f="$out/geometric/geometric_n${n}_s${k}.asn"
    [[ -s "$f" ]] && continue
    params=$(printf 'nodes %d\ndimension 2\nmaxloc 1000000\nseed %d\n' "$n" "$k")
    { printf '%s\n' "$params" | "$gen" || true; } \
      | awk -f "$geomasn" \
      | sed -e 's/^e /a /' > "$f"
    check "$f" && echo "wrote $f  ($(du -h "$f" | cut -f1))"
  done
done

echo
du -sh "$out/geometric" 2>/dev/null || true
