#!/usr/bin/env bash
# Time the standard build and unchanged public-axiom audit separately.
set -euo pipefail
cd "$(dirname "$0")/.."
task_log_dir="${1:-verification-logs}"
mkdir -p "$task_log_dir"
task_log_dir="$(cd "$task_log_dir" && pwd -P)"
task_start="$(date +%s)"
task_build_start="$task_start"
task_build_end=""
task_audit_start=""
task_audit_end=""
task_audit_script=""
python3 - "$task_log_dir" "$task_start" "$$" <<'PY'
import json,sys
from pathlib import Path
folder,start,pid=sys.argv[1:]
Path(folder,'started.json').write_text(json.dumps({
    'status':'running','start_utc':int(start),'build_start_utc':int(start),
    'runner_pid':int(pid),'queue_seconds':0},indent=2)+'\n')
PY
finish() {
  task_rc=$?
  task_end="$(date +%s)"
  python3 - "$task_log_dir" "$task_rc" "$task_start" "$task_end" \
    "$task_build_start" "$task_build_end" "$task_audit_start" "$task_audit_end" <<'PY'
import json,sys
from pathlib import Path
folder,rc,start,end,bs,be,ast,aend=sys.argv[1:]
num=lambda x: int(x) if x else None
delta=lambda a,b: int(b)-int(a) if a and b else None
Path(folder,'timing.json').write_text(json.dumps({
    'exit_code':int(rc),'start_utc':int(start),'end_utc':int(end),
    'status':'completed' if int(rc)==0 else 'failed',
    'total_seconds':int(end)-int(start),
    'build_start_utc':num(bs),'build_end_utc':num(be or end) if not ast else num(be),
    'build_seconds':delta(bs,be or end) if not ast else delta(bs,be),
    'build_status':'completed' if be else 'failed',
    'axiom_start_utc':num(ast),'axiom_end_utc':num(aend or end) if ast else None,
    'axiom_status':('completed' if aend else 'failed') if ast else 'not_started',
    'axiom_seconds':delta(ast,aend or end) if ast else None,
    'queue_seconds':0},indent=2)+'\n')
PY
  if [[ -n "$task_audit_script" ]]; then rm -f "$task_audit_script"; fi
  exit "$task_rc"
}
trap finish EXIT
lake --wfail build ECDSAAdd ECDSAAdd.Arithmetic.RecordedRailApplyProof ECDSAAdd.Arithmetic.RecordedRailApplyResources ECDSAAdd.Arithmetic.NativeFirstDirectCallerSupport ECDSAAdd.Arithmetic.TerminalParityOldSupport > "$task_log_dir/build.log" 2>&1
task_build_end="$(date +%s)"
# Preserve verify.sh's selected declarations and whitelist verbatim. The
# separately timed build above replaces only its identical build command.
task_audit_script="$(mktemp "$(pwd)/scripts/.axiom-audit.XXXXXX")"
python3 - "$task_audit_script" <<'PY'
import sys
from pathlib import Path
text=Path('scripts/verify.sh').read_text()
assert text.count('lake --wfail build')==1
Path(sys.argv[1]).write_text(text.replace('lake --wfail build',': # build already passed',1))
PY
task_audit_start="$(date +%s)"
bash "$task_audit_script" > "$task_log_dir/axioms.log" 2>&1
task_audit_end="$(date +%s)"
