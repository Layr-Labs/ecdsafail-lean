#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${root}"

export PATH="${HOME}/.elan/bin:${PATH}"

if ! command -v elan >/dev/null 2>&1; then
  curl --proto '=https' --tlsv1.2 -sSfL \
    https://raw.githubusercontent.com/leanprover/elan/464c9d28395000a2a0128e07081e4956d50eced2/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi

toolchain="$(tr -d '[:space:]' < lean-toolchain)"
elan toolchain install "${toolchain}"

# Fetch Mathlib's prebuilt oleans unless the checkout already holds a build for exactly the
# pinned revision and toolchain. A cache restored via restore-keys can carry Mathlib for an
# older revision: Lake re-checks out the pinned revision by itself, but without `cache get`
# it would then rebuild Mathlib from source.
mathlib_dir=.lake/packages/mathlib
mathlib_rev="$(python3 -c 'import json; print(next(p["rev"] for p in json.load(open("lake-manifest.json"))["packages"] if p["name"] == "mathlib"))')"
if [[ ! -d "${mathlib_dir}/.lake/build" || ! -d "${mathlib_dir}/.git" ]] \
  || [[ "$(git -C "${mathlib_dir}" rev-parse HEAD 2>/dev/null)" != "${mathlib_rev}" ]] \
  || [[ "$(tr -d '[:space:]' < "${mathlib_dir}/lean-toolchain" 2>/dev/null)" != "${toolchain}" ]]; then
  lake exe cache get
fi

python3 scripts/paper935/generate_schedule.py --check
python3 scripts/paper935/check_fused_repack.py
python3 scripts/sample_b5.py --check --output data/b5-empirical.json
python3 tests/test_sample_b5.py
python3 scripts/paper935/check_hmr_call_ports.py

# Prebuild the protected contract, judge, and certified baseline targets.
# Never compile Submission/Entrant here; remove any stale entrant build outputs
# so the shared cache holds only trusted artifacts.
rm -rf .lake/build/lib/lean/ECDSAAdd/Submission/Entrant .lake/build/ir/ECDSAAdd/Submission/Entrant
lake --wfail build \
  ECDSAAdd.Challenge.Contract \
  ECDSAAdd.Judge.Main \
  ECDSAAdd.Baselines.SkywalkCertificate \
  ECDSAAdd.Baselines.ValueWalkCertificate
rm -rf .lake/build/lib/lean/ECDSAAdd/Submission/Entrant .lake/build/ir/ECDSAAdd/Submission/Entrant

# A cache restored via restore-keys can hold build outputs for modules that were since removed
# from source. Lake never deletes them, and leanchecker replays every olean under a prefix, so
# prune them to make the trusted tree and the manifest below identical to a cold build.
python3 - <<'PY'
from pathlib import Path

for build_root in (Path(".lake/build/lib/lean"), Path(".lake/build/ir")):
    tree = build_root / "ECDSAAdd"
    if not tree.is_dir():
        continue
    for p in sorted(tree.rglob("*")):
        if not p.is_file():
            continue
        rel = p.relative_to(build_root)
        source = rel.parent / (rel.name.split(".", 1)[0] + ".lean")
        if not source.is_file():
            p.unlink()
            print(f"Pruned orphaned build artifact: {p}")
PY

# Record the SHA-256 digest of all protected .olean artifacts so benchmark.sh
# can verify that building untrusted submission modules did not alter them.
python3 - <<'PY'
import hashlib
from pathlib import Path

build_lib = Path(".lake/build/lib/lean/ECDSAAdd")
protected_dirs = [
    "Framework",
    "Math",
    "Circuit",
    "Arithmetic",
    "Challenge",
    "Judge",
    "Baselines",
]
entries = []
for sub in protected_dirs:
    d = build_lib / sub
    if not d.exists():
        continue
    for p in sorted(d.rglob("*.olean")):
        h = hashlib.sha256(p.read_bytes()).hexdigest()
        entries.append(f"{h}  {p.as_posix()}")

manifest = Path(".lake/trusted-oleans.sha256")
manifest.parent.mkdir(parents=True, exist_ok=True)
manifest.write_text("\n".join(entries) + "\n", encoding="utf-8")
print(f"Recorded {len(entries)} protected .olean digests in {manifest}")
PY
