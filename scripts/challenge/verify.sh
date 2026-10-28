#!/usr/bin/env bash
# Protected worker script. Invoke only in an isolated candidate build worker.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/python-version.sh"
"$challenge_python" "$(dirname "${BASH_SOURCE[0]}")/../paper935/source_root.py"
: "${ECDSAADD_ROOT:=$(git rev-parse --show-toplevel)}"
export ECDSAADD_ROOT
cd "$ECDSAADD_ROOT"
"$challenge_python" scripts/challenge/gate.py --source-only
"$challenge_python" scripts/challenge/check-layers.py
lake --wfail build ECDSAAdd.Challenge.Contract ECDSAAdd.Judge.Main ECDSAAdd.Submission.Entrant.Main
"$challenge_python" scripts/challenge/gate.py --replay ECDSAAdd.Challenge
"$challenge_python" scripts/challenge/gate.py --replay ECDSAAdd.Submission.Entrant
# Acceptance is performed by the protected controller after the worker stops.
