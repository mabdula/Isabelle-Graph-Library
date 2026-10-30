#!/bin/bash
# Run it from this directory after `make' has built the generators.
# Generate the DIMACS Network Flows 2.0 core assignment benchmarks.
#
# Recipe, quoted from the challenge's "Assignment Problem Instances and
# Generators" page:
#
#   Low-cost instances: use the assign.c generator with the following
#   parameters: nodes N, sources N/2, degree 2 log_2 N, maxcost 100.
#   Use N = 2^11, 2^12, 2^13, 2^14, 2^15
#
#   Two-cost instances: ... derived from low-cost instances using the UNIX awk
#   program and the DIMACS awk script twocost.a.  The instance with N nodes and
#   seed K is generated using ... assign | awk -f twocost.a
#
# The geometric family needs dcube.c, which the challenge page itself records
# as missing from the DIMACS depository, and whose tar archive link is dead.
# It is not generated here; see README.md.
#
# Sizes may be given explicitly; the degree rule 2*log_2 N is applied at
# whatever N is asked for, so sizes outside the core list (such as the ~1000 and
# ~50000 vertex graphs used for the threshold search) follow the same recipe.
#
# usage: gen_instances.sh [--nodes <list>] [--seeds <list>] [outdir]

set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(dirname "$here")"
gen="$here/assign"
twocost="$here/twocost.a"
out="$here/out"

[[ -x "$gen" ]] || { echo "missing generator: $gen (run make -C $root/generators)"; exit 1; }

seeds=(1 2 3 4 5)
nodes_list=(2048 4096 8192 16384 32768)

while [[ $# -gt 0 ]]; do
  case "$1" in
    --nodes) IFS=',' read -r -a nodes_list <<< "$2"; shift 2;;
    --seeds) IFS=',' read -r -a seeds <<< "$2"; shift 2;;
    *) out="$1"; shift;;
  esac
done

mkdir -p "$out/low-cost" "$out/two-cost"

# assign.c has no return at the end of main and exits with a junk status (20
# here) even on a clean run, so its status says nothing.  Each generated file is
# validated instead: it must carry a problem line and the number of arc lines
# that line promises.
check() {
  local f="$1"
  local p arcs
  p=$(grep -m1 '^p asn' "$f") || { echo "FAIL $f: no problem line"; return 1; }
  arcs=$(awk '$1 == "a"' "$f" | wc -l)
  [[ "$arcs" -eq "$(awk '{print $4}' <<<"$p")" ]] \
    || { echo "FAIL $f: $arcs arc lines, problem line says $(awk '{print $4}' <<<"$p")"; return 1; }
  return 0
}

for n in "${nodes_list[@]}"; do
  sources=$((n / 2))
  # degree = 2 * log_2 N, rounded, exactly as the challenge recipe prescribes
  degree=$(awk -v n="$n" 'BEGIN { printf "%d", int(2 * log(n) / log(2) + 0.5) }')
  for k in "${seeds[@]}"; do
    params=$(printf 'nodes %d\nsources %d\ndegree %d\nmaxcost 100\nseed %d\n' \
                    "$n" "$sources" "$degree" "$k")

    f="$out/low-cost/low-cost_n${n}_s${k}.asn"
    if [[ ! -s "$f" ]]; then
      printf '%s' "$params" | "$gen" > "$f" || true
      check "$f" && echo "wrote $f"
    fi

    g="$out/two-cost/two-cost_n${n}_s${k}.asn"
    if [[ ! -s "$g" ]]; then
      # twocost.a's BEGIN banner is printed without a trailing newline, so it
      # arrives glued to the problem line as "c ...graphp asn <n> <m>".  Left
      # alone, every reader skips that line as a comment and the instance has
      # no problem line at all.  Split it back apart.
      { printf '%s' "$params" | "$gen" || true; } \
        | awk -f "$twocost" \
        | sed -e 's/^\(c .*graph\)\(p asn\)/\1\n\2/' > "$g"
      check "$g" && echo "wrote $g"
    fi
  done
done

echo
echo "instances under $out:"
du -sh "$out"/* 2>/dev/null || true
