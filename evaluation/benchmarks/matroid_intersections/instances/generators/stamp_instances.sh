#!/bin/bash
# PACKAGE COPY: identical to the script that generated the instances except for
# the path lines marked "package:", which pointed into the study tree
# (<study>/generators/build/..., <study>/generators/*.a, <study>/instances).
# Run it from this directory after `make' has built the generators.
# Build the b-matching instances by stamping capacities onto the DIMACS
# assignment instances. The graphs are reused exactly as generated; only
# capacities are added, so <name>.asn and <name>.bmatch are the same graph.
#
#   cap(v) = min(U[1,20], deg(v)), drawn per vertex
#
# The capacity seed is the instance's own seed index, taken from the file name,
# so the draw is reproducible from the name alone and two files built from the
# same graph (low-cost and its two-cost recosting) get the same capacities.
#
# Existing .bmatch files are left alone, so the script can be re-run after new
# sizes are generated; --force re-stamps them (the draw is deterministic, so a
# forced run over an unchanged tree must leave every file byte-identical).
#
# usage: stamp_instances.sh [--src <dir>] [--families <list>] [--max <M>]
#                           [--force] [outdir]

set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(dirname "$here")"
src="$here/out"              # package: was $root/instances
out="$here/out"              # package: was $root/instances
maxcap=20
families=(low-cost two-cost geometric validation)
force=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --src)      src="$2"; shift 2;;
    --families) IFS=',' read -r -a families <<< "$2"; shift 2;;
    --max)      maxcap="$2"; shift 2;;
    --force)    force=1; shift;;
    -*)         echo "unknown option $1" >&2; exit 2;;
    *)          out="$1"; shift;;
  esac
done

[[ -d "$src" ]] || { echo "missing source tree: $src" >&2; exit 1; }

total=0
for fam in "${families[@]}"; do
  [[ -d "$src/$fam" ]] || { echo "skipping $fam: not in $src" >&2; continue; }
  mkdir -p "$out/$fam"
  n=0
  for f in "$src/$fam"/*.asn; do
    [[ -e "$f" ]] || continue
    base="$(basename "$f" .asn)"
    [[ $force -eq 0 && -s "$out/$fam/$base.bmatch" ]] && continue
    seed="${base##*_s}"
    [[ "$seed" =~ ^[0-9]+$ ]] || { echo "no seed in name: $base" >&2; exit 1; }
    python3 "$here/stamp_capacities.py" "$f" "$out/$fam/$base.bmatch" \
            --seed "$seed" --max "$maxcap" --quiet || exit 1
    n=$((n + 1))
  done
  echo "$fam: $n instances stamped"
  total=$((total + n))
done
echo "$total newly stamped in $out"
