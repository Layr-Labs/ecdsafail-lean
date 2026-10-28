#!/usr/bin/env bash
# Organizer development checks; separate from untrusted candidate worker script.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/python-version.sh"
"$challenge_python" "$(dirname "${BASH_SOURCE[0]}")/../paper935/source_root.py"
cd "$(dirname "$0")/../.."
export ECDSAADD_ROOT="$PWD"
bash -n scripts/benchmark.sh scripts/challenge/verify.sh
"$challenge_python" scripts/challenge/test-editable.py
"$challenge_python" scripts/challenge/test-runner-boundary.py
"$challenge_python" scripts/challenge/test-source-preflight.py
"$challenge_python" scripts/challenge/check-layers.py
lake --wfail build ECDSAAdd.Baselines.SkywalkCertificate ECDSAAdd.Challenge.Regression ECDSAAdd.Judge.Main ECDSAAdd.Submission.Entrant.Main
"$challenge_python" scripts/challenge/gate.py --replay ECDSAAdd.Challenge
"$challenge_python" scripts/challenge/gate.py --replay ECDSAAdd.Judge
"$challenge_python" scripts/challenge/judge_regressions.py
lake env lean scripts/challenge/audit.lean

"$challenge_python" scripts/challenge/valuewalk_acceptance.py

"$challenge_python" scripts/challenge/skywalk_acceptance.py
