#!/bin/bash
# run.sh MODE [--old-generated-code] -- runs the measurements of MODE (smoke, 8h or full; modes.conf says what
# each one runs) after setup/setup.sh MODE has prepared everything, and writes the paper's tables as CSV to
# results/<date>_<mode>/.  Every measured run is one process: run/run_experiments.py starts the single-run
# program of one solver on one instance, as a user would from the command line, and records the row it prints.
# --old-generated-code says the setup was run with that option (the code exports of the paper's campaign are
# measured); the script refuses to run when the setup prepared the other kind of exports.
set -uo pipefail
EVAL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
usage() { echo "usage: run/run.sh smoke|8h|full [--old-generated-code]" >&2; exit 2; }
mode=${1:-}; case "$mode" in smoke|8h|full) ;; *) usage ;; esac
old=0; case "${2:-}" in "") ;; --old-generated-code) old=1 ;; *) usage ;; esac
work="$EVAL/work"
[[ -f "$work/env.sh" && -f "$work/exports_$mode" ]] || { echo "run setup/setup.sh $mode first" >&2; exit 1; }
prepared=$(cat "$work/exports_$mode")
if [[ $old == 1 && "$prepared" != campaign ]]; then echo "the setup prepared $prepared code exports; run setup/setup.sh $mode --old-generated-code first" >&2; exit 1; fi
if [[ $old == 0 && "$prepared" == campaign ]]; then echo "the setup prepared the campaign's code exports; run with --old-generated-code, or run setup/setup.sh $mode first" >&2; exit 1; fi
# shellcheck disable=SC1091
source "$work/env.sh"
exec python3 "$EVAL/run/run_experiments.py" "$mode"
