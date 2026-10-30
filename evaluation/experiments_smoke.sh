#!/bin/bash
# experiments_smoke.sh [--old-generated-code] -- smoke test: every solver of every table of the paper's body once, on the smallest instance of each family, with the shipped
# code exports (exports/pregenerated).
# Setup (setup/setup.sh smoke) and then the measurements (run/run.sh smoke); both can also be run on their own.
# --old-generated-code measures the code exports the paper's numbers were made with (exports/campaign) instead.
# Takes about 1 to 2 hours (downloads and builds about 45 minutes, runs about 15 minutes).  Results: evaluation/results/<date>_smoke/.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "$here/setup/setup.sh" smoke "$@" || { echo "setup failed, see evaluation/work/setup_smoke.log" >&2; exit 1; }
exec bash "$here/run/run.sh" smoke "$@"
