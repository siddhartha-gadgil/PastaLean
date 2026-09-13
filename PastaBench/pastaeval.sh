#!/usr/bin/env bash
# pastaeval — one unified eval harness (HumanEval contract/non-contract + CP/leetcode), numpy in every mode.
#   bash PastaBench/pastaeval.sh humaneval               # non-contract solution.py: translate → compile
#   bash PastaBench/pastaeval.sh humaneval --contract --prove
#   bash PastaBench/pastaeval.sh cp --source leetcode --num max
#   bash PastaBench/pastaeval.sh numpy
# Do NOT run a concurrent `lake build`/`regen` — a warm backend + parallel `lake env lean` share oleans.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
source .venv/bin/activate
lake build py2lean >/dev/null 2>&1 || true
exec python3 PastaBench/pastaeval.py "$@"
