#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${root}"

export PATH="${HOME}/.elan/bin:${PATH}"

score_path="scripts/score.json"
rm -f "${score_path}" "${score_path}.tmp"

if ! command -v lake >/dev/null 2>&1; then
  echo "benchmark.sh: lake not found; run ./setup.sh first" >&2
  exit 1
fi

if [[ ! -f .lake/trusted-oleans.sha256 ]]; then
  echo "benchmark.sh: missing .lake/trusted-oleans.sha256; run ./setup.sh first" >&2
  exit 1
fi

# 1. Source-hygiene check on editablePaths (ECDSAAdd/Submission/Entrant) + prune orphaned build artifacts.
python3 - <<'PY'
import os
import re
import sys
from pathlib import Path

editable = Path("ECDSAAdd/Submission/Entrant")
if not editable.is_dir() or editable.is_symlink():
    print("Editable root ECDSAAdd/Submission/Entrant must be a regular directory", file=sys.stderr)
    sys.exit(1)

for dirpath, dirnames, filenames in os.walk(editable, followlinks=False):
    for name in [*dirnames, *filenames]:
        p = Path(dirpath) / name
        if p.is_symlink():
            print(f"Symlinks are forbidden in editablePaths: {p}", file=sys.stderr)
            sys.exit(1)


def strip_comments(source: str) -> str:
    """Remove nested block and line comments while retaining newlines and token gaps."""
    out = []
    i = depth = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            out.append(" ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            out.append(" ")
            i += 2
        elif depth:
            if source[i] == "\n":
                out.append("\n")
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError("unclosed block comment")
    return "".join(out)


FORBIDDEN = [
    r"@\[extern\b",
    r"@\[implemented_by\b",
    r"@\[csimp\b",
    r"@\[never_extract\b",
    r"\bunsafe\b",
    r"\bpartial\b",
    r"\bopaque\b",
    r"\baxiom\b",
    r"\bsorry\b",
    r"\badmit\b",
    r"\binitialize\b",
    r"\bbuiltin_initialize\b",
    r"\bIO\.Process\b",
    r"\bIO\.FS\b",
    r"\bSystem\.FilePath\b",
    r"\brun_tac\b",
    r"\brun_cmd\b",
    r"\bby_elab\b",
    r"#eval\b",
    r"\belab\b",
    r"\belab_rules\b",
    r"\bmacro\b",
    r"\bmacro_rules\b",
    r"\bsyntax\b",
    r"\blocal\s+notation\b",
    r"\bscoped\s+notation\b",
    r"\blocal\s+instance\b",
]

for p in sorted(editable.rglob("*.lean")):
    text = p.read_text(encoding="utf-8")
    clean = strip_comments(text)
    for pat in FORBIDDEN:
        m = re.search(pat, clean)
        if m:
            print(f"Forbidden token {m.group(0)!r} in {p}", file=sys.stderr)
            sys.exit(1)

# Delete all build outputs under ECDSAAdd/Submission/Entrant so the submission is
# compiled from scratch on every run rather than relying on Lake staleness checks.
for sub_dir in (
    Path(".lake/build/lib/lean/ECDSAAdd/Submission/Entrant"),
    Path(".lake/build/ir/ECDSAAdd/Submission/Entrant"),
):
    if sub_dir.exists():
        import shutil
        shutil.rmtree(sub_dir)
PY

# 2. Run upstream source-only kernel-disable gate and import-layer check.
export ECDSAADD_ROOT="${PWD}"
python3 scripts/challenge/gate.py --root "${PWD}" --source-only
python3 scripts/challenge/check-layers.py

# 3. Snapshot trusted .olean manifest, protected challenge/judge files, and all non-editable tracked files before build.
trusted_snapshot="$(mktemp)"
judge_snapshot="$(mktemp)"
contract_snapshot="$(mktemp)"
judge_main_snapshot="$(mktemp)"
repo_snapshot="$(mktemp)"
judge_log="$(mktemp)"
trusted_lib="$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/ecdsaadd-trusted-lib.XXXXXX")"
overlay="$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/ecdsaadd-entrant.XXXXXX")"
trap 'rm -rf "${trusted_snapshot}" "${judge_snapshot}" "${contract_snapshot}" "${judge_main_snapshot}" "${repo_snapshot}" "${judge_log}" "${trusted_lib}" "${overlay}"' EXIT

cp .lake/trusted-oleans.sha256 "${trusted_snapshot}"
cp scripts/challenge/judge.lean "${judge_snapshot}"
cp ECDSAAdd/Challenge/Contract.lean "${contract_snapshot}"
cp ECDSAAdd/Judge/Main.lean "${judge_main_snapshot}"

python3 - "${repo_snapshot}" <<'PY'
import hashlib
import subprocess
import sys
from pathlib import Path

out = Path(sys.argv[1])
files = subprocess.check_output(["git", "ls-files", "-z"]).split(b"\0")
entries = []
for raw in files:
    if not raw:
        continue
    rel = raw.decode("utf-8")
    if rel == "ECDSAAdd/Submission/Entrant" or rel.startswith("ECDSAAdd/Submission/Entrant/"):
        continue
    p = Path(rel)
    if p.is_file():
        h = hashlib.sha256(p.read_bytes()).hexdigest()
        entries.append(f"{h}  {rel}")
out.write_text("\n".join(entries) + "\n", encoding="utf-8")
PY

# 4. Build the protected contract, judge, and entrant target with warnings as errors.
lake --wfail build \
  ECDSAAdd.Challenge.Contract \
  ECDSAAdd.Judge.Main \
  ECDSAAdd.Submission.Entrant.Main

# 5. Verify protected .olean integrity and non-editable tracked files against pre-build snapshots.
cmp -s scripts/challenge/judge.lean "${judge_snapshot}" || {
  echo "Protected file modified: scripts/challenge/judge.lean" >&2
  exit 1
}
cmp -s ECDSAAdd/Challenge/Contract.lean "${contract_snapshot}" || {
  echo "Protected file modified: ECDSAAdd/Challenge/Contract.lean" >&2
  exit 1
}
cmp -s ECDSAAdd/Judge/Main.lean "${judge_main_snapshot}" || {
  echo "Protected file modified: ECDSAAdd/Judge/Main.lean" >&2
  exit 1
}

python3 - "${trusted_snapshot}" "${repo_snapshot}" <<'PY'
import hashlib
import sys
from pathlib import Path

for snap_arg, label in [(sys.argv[1], "Protected artifact"), (sys.argv[2], "Protected source")]:
    manifest = Path(snap_arg)
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        expected, relpath = line.split("  ", 1)
        p = Path(relpath)
        if not p.is_file():
            print(f"{label} missing: {relpath}", file=sys.stderr)
            sys.exit(1)
        actual = hashlib.sha256(p.read_bytes()).hexdigest()
        if actual != expected:
            print(f"{label} modified: {relpath}", file=sys.stderr)
            sys.exit(1)
PY

# 6. Stage the entrant overlay into a temp dir using stage-entrant.py.
# stage-entrant.py requires --trusted-lib to reside outside --candidate "$PWD",
# so we materialize the verified "$PWD/.lake/build/lib/lean" tree (minus Entrant) in "$trusted_lib".
python3 - "${PWD}/.lake/build/lib/lean" "${trusted_lib}" <<'PY'
import shutil
import sys
from pathlib import Path

src = Path(sys.argv[1]).resolve(strict=True)
dst = Path(sys.argv[2]).resolve(strict=True)
shutil.copytree(src, dst, dirs_exist_ok=True)
entrant_sub = dst / "ECDSAAdd/Submission/Entrant"
if entrant_sub.exists():
    shutil.rmtree(entrant_sub)
PY

python3 scripts/challenge/stage-entrant.py \
  --candidate "${PWD}" \
  --overlay "${overlay}" \
  --trusted-lib "${trusted_lib}"

# 7. Replay ECDSAAdd.Challenge, ECDSAAdd.Judge, and ECDSAAdd.Submission.Entrant using gate.py.
unset LEAN_PATH LEAN_SRC_PATH
python3 scripts/challenge/gate.py --root "${PWD}" --replay ECDSAAdd.Challenge
python3 scripts/challenge/gate.py --root "${PWD}" --replay ECDSAAdd.Judge
python3 scripts/challenge/gate.py --root "${PWD}" --replay ECDSAAdd.Submission.Entrant --artifact-path "${overlay}"

# 8. Run upstream's Expr-level kernel judge against the sealed entrant overlay.
lake env lean --run scripts/challenge/judge.lean "${overlay}" > "${judge_log}" 2>&1 || {
  cat "${judge_log}" >&2
  exit 1
}
cat "${judge_log}"

# 9. Parse judge JSON output and write scripts/score.json.
python3 - "${judge_log}" "${score_path}" <<'PY'
import json
import os
import sys
from pathlib import Path

lines = [
    line.strip()
    for line in Path(sys.argv[1]).read_text(encoding="utf-8").splitlines()
    if line.strip().startswith("{") and line.strip().endswith("}")
]
if len(lines) != 1:
    print(f"Expected exactly one JSON verdict line from judge.lean, got {len(lines)}", file=sys.stderr)
    sys.exit(1)

report = json.loads(lines[0])
if report.get("accepted") is not True:
    print(f"Judge did not accept entrant: {report}", file=sys.stderr)
    sys.exit(1)

toffoli = int(report["score_toffoli_upper_bound"])
qubits = int(report["qubits_upper_bound"])
measurements = int(report["measurements_upper_bound"])
gate_slots = int(report["all_syntax_slots_upper_bound"])
q_times_t = int(report["qubits_times_toffoli_upper_bound"])

if toffoli <= 0 or qubits <= 0 or measurements < 0 or gate_slots <= 0:
    print(
        f"Invalid resource bounds: toffoli={toffoli}, qubits={qubits}, "
        f"measurements={measurements}, gateSlots={gate_slots}",
        file=sys.stderr,
    )
    sys.exit(1)

score = qubits * toffoli
if score != q_times_t:
    print(f"Score mismatch: qubits * toffoli = {score} != {q_times_t}", file=sys.stderr)
    sys.exit(1)

if score >= 2**53:
    print(f"Score {score} exceeds IEEE-754 exact integer range (2^53 - 1)", file=sys.stderr)
    sys.exit(1)

payload = {
    "score": score,
    "metrics": {
        "toffoli": toffoli,
        "qubits": qubits,
        "measurements": measurements,
        "gateSlots": gate_slots,
        "axioms": ["Classical.choice", "Quot.sound", "propext"],
    },
}
score_path = Path(sys.argv[2])
score_path.parent.mkdir(parents=True, exist_ok=True)
tmp_path = score_path.with_suffix(".json.tmp")
tmp_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
os.replace(tmp_path, score_path)
print(
    f"Verified score={score} "
    f"(toffoli={toffoli}, qubits={qubits}, measurements={measurements}, gateSlots={gate_slots})"
)
PY
