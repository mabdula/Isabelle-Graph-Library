#!/bin/bash
# python_env.sh REQUIREMENTS -- prints the path of a Python virtual environment holding exactly the packages
# pinned in REQUIREMENTS (a requirements.txt), creating it under work/venvs/<md5 of the file> with $PYTHON if it
# is not there yet.  Library programs with the same pinned packages share one environment (the competitor
# Makefiles link their .venv to it), so each set of packages is installed once.
set -uo pipefail
EVAL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
req=$1
key=$(md5sum "$req" | cut -c1-32)
venv="$EVAL/work/venvs/$key"
py="${PYTHON:-python3}"
if [[ ! -x "$venv/bin/python" || ! -f "$venv/.installed" ]]; then
  rm -rf "$venv"; mkdir -p "$EVAL/work/venvs"
  { "$py" -m venv "$venv" && "$venv/bin/python" -m pip install --quiet --upgrade pip && "$venv/bin/python" -m pip install --quiet -r "$req" && cp "$req" "$venv/requirements.txt" && touch "$venv/.installed"; } >&2 || { rm -rf "$venv"; echo "python_env.sh: could not install $req" >&2; exit 1; }
fi
echo "$venv"
