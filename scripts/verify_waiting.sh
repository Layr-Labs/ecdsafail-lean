#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Separate module: deliberately not imported by the strict root.
lake build ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer
task_waiting_log="${ECDSA_WAITING_AXIOM_LOG:-/tmp/ecdsadd-waiting-axioms.log}"
lake env lean scripts/paper935/WaitingAudit.lean > "$task_waiting_log" 2>&1
cat "$task_waiting_log"
python3 scripts/paper935/check_waiting_audit.py "$task_waiting_log"
