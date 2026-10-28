#!/usr/bin/env bash
# Checks selected Skywalk components; verify.sh checks the complete point circuit.
set -euo pipefail
cd "$(dirname "$0")/.."
task_log_dir="${1:-skywalk-verification-logs}"
mkdir -p "$task_log_dir"
task_log_dir="$(cd "$task_log_dir" && pwd -P)"
task_start="$(date +%s)"
task_build_end=""
task_audit_start=""
task_audit_end=""
finish() {
  task_rc=$?
  task_end="$(date +%s)"
  python3 - "$task_log_dir" "$task_rc" "$task_start" "$task_end" \
    "$task_build_end" "$task_audit_start" "$task_audit_end" <<'PY'
import json,sys
from pathlib import Path
folder,rc,start,end,be,ast,ae=sys.argv[1:]
delta=lambda a,b: int(b)-int(a) if a and b else None
Path(folder,'timing.json').write_text(json.dumps({
 'scope':'Skywalk development modules; full point integration pending',
 'exit_code':int(rc),'start_utc':int(start),'end_utc':int(end),
 'status':'completed' if int(rc)==0 else 'failed',
 'build_start_utc':int(start),'build_end_utc':int(be or end) if not ast else int(be),
 'axiom_start_utc':int(ast) if ast else None,'axiom_end_utc':int(ae or end) if ast else None,
 'build_status':'completed' if be else 'failed',
 'axiom_status':('completed' if ae else 'failed') if ast else 'not_started',
 'total_seconds':int(end)-int(start),'build_seconds':delta(start,be or end),
 'axiom_seconds':delta(ast,ae)},indent=2)+'\n')
PY
  exit "$task_rc"
}
trap finish EXIT
task_modules=(
  ECDSAAdd.Math.SkywalkNat ECDSAAdd.Math.SkywalkRailsBridge
  ECDSAAdd.Math.SkywalkPayload ECDSAAdd.Arithmetic.SignedWord
  ECDSAAdd.Math.SkywalkTrace ECDSAAdd.Arithmetic.SignedWordBits
  ECDSAAdd.Arithmetic.ControlledNegRaw ECDSAAdd.Arithmetic.SkywalkSignedModAdd
  ECDSAAdd.Arithmetic.SignedRecordProgram ECDSAAdd.Arithmetic.SkywalkSeed
  ECDSAAdd.Arithmetic.SkywalkTerminal ECDSAAdd.Arithmetic.SkywalkDialog
  ECDSAAdd.Arithmetic.SkywalkIntegerTick ECDSAAdd.Arithmetic.SkywalkPool
  ECDSAAdd.Arithmetic.SkywalkShared ECDSAAdd.Arithmetic.SkywalkPointPool
  ECDSAAdd.Arithmetic.SkywalkPointLayout ECDSAAdd.Arithmetic.SkywalkControlled
  ECDSAAdd.Math.FusedSignedHalf ECDSAAdd.Arithmetic.TrailingZeroCompare
  ECDSAAdd.Arithmetic.SkywalkIntegerLoopCore ECDSAAdd.Arithmetic.SkywalkIntegerLoop
  ECDSAAdd.Arithmetic.SkywalkArithmeticCore ECDSAAdd.Arithmetic.SkywalkArithmetic
  ECDSAAdd.Arithmetic.SkywalkControlledPort
  ECDSAAdd.Arithmetic.SignedHalf ECDSAAdd.Arithmetic.SkywalkSign
  ECDSAAdd.Arithmetic.SkywalkRoute ECDSAAdd.Arithmetic.SkywalkPayloadProgram
)
if [[ $# -gt 1 ]]; then task_modules=("${@:2}"); fi
# Bound runaway proof reduction before it can exhaust the pod's64GB cgroup.
# This limits the compiler process, not the theorem's inputs or proof checks.
ulimit -v 25165824
lake --wfail build "${task_modules[@]}" > "$task_log_dir/build.log" 2>&1
task_build_end="$(date +%s)"
python3 - "$task_log_dir" "${task_modules[@]}" <<'PY'
import hashlib,json,re,sys
from pathlib import Path
folder=Path(sys.argv[1]); modules=sys.argv[2:]
if 'ECDSAAdd.Math.SkywalkRailsBridge' in modules:
 modules.insert(modules.index('ECDSAAdd.Math.SkywalkRailsBridge'),'ECDSAAdd.Math.SkywalkRails')
if 'ECDSAAdd.Arithmetic.SkywalkIntegerTick' in modules:
 modules.insert(modules.index('ECDSAAdd.Arithmetic.SkywalkIntegerTick'),'ECDSAAdd.Arithmetic.SkywalkIntegerLayout')
if 'ECDSAAdd.Arithmetic.SkywalkIntegerLoop' in modules and 'ECDSAAdd.Arithmetic.SkywalkIntegerLoopCore' not in modules:
 modules.insert(modules.index('ECDSAAdd.Arithmetic.SkywalkIntegerLoop'),'ECDSAAdd.Arithmetic.SkywalkIntegerLoopCore')
queries=[]; sources=[]; text=[]
for module in modules:
 path=Path(module.replace('.','/')+'.lean'); source=path.read_text()
 scopes=[]
 for line in source.splitlines():
  match=re.match(r'^namespace (\S+)\s*$',line)
  if match:
   scopes.append(('namespace',match.group(1)))
   continue
  match=re.match(r'^section(?: (\S+))?\s*$',line)
  if match:
   scopes.append(('section',match.group(1)))
   continue
  match=re.match(r'^end(?: (\S+))?\s*$',line)
  if match:
   assert scopes,(path,line)
   kind,name=scopes.pop()
   assert match.group(1) is None or match.group(1)==name,(path,line,name)
   continue
  match=re.match(r'^(?:theorem|lemma) ([A-Za-z_][A-Za-z_0-9]*)',line)
  if match:
   namespace='.'.join(name for kind,name in scopes if kind=='namespace')
   assert namespace,(path,line)
   queries.append(namespace+'.'+match.group(1))
 assert not scopes,(path,scopes)
 sources.append({'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
 text.append('import '+module)
assert len(set(queries))==len(queries)
text += ['#print axioms '+name for name in queries]
(folder/'audit.lean').write_text('\n'.join(text)+'\n')
(folder/'manifest.json').write_text(json.dumps({'sources':sources,'declarations':queries},indent=2)+'\n')
PY
task_audit_start="$(date +%s)"
lake env lean "$task_log_dir/audit.lean" > "$task_log_dir/axioms.log" 2>&1
python3 - "$task_log_dir" <<'PY'
import json,re,sys
from pathlib import Path
folder=Path(sys.argv[1]); wanted=json.loads((folder/'manifest.json').read_text())['declarations']
text=(folder/'axioms.log').read_text(); actual=re.findall(r"^'([^']+)'",text,re.M)
assert actual==wanted,(len(actual),len(wanted))
allowed={'propext','Classical.choice','Quot.sound'}
entries=re.findall(r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",text,re.M)
assert [name for name,_ in entries]==wanted,('Unparsed axiom output',len(entries),len(wanted))
for name,body in entries:
 names=set(filter(None,re.split(r'[\s,]+',body)))
 assert names<=allowed,(name,names)
print('All',len(actual),'public Skywalk development declarations passed the axiom whitelist.')
PY
task_audit_end="$(date +%s)"
