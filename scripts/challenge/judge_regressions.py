"""Actual-contract rejection tests. Baseline acceptance is tested separately
when a complete baseline certificate is available; none is fabricated here.
"""
import shutil
from pathlib import Path
import subprocess
import tempfile
import gate

BASE = """import ECDSAAdd.Challenge.Contract
open ECDSAAdd ECDSAAdd.Challenge
namespace ECDSAAdd.Entrant
def entry : Entry := fun _ => []
def bounds : Bounds := ⟨0, 0, 0, 0⟩
"""
END = '\nend ECDSAAdd.Entrant\n'
CASES = [
 ('MacroZeroScore', BASE + 'theorem certificate : True := True.intro\n' + END +
  """macro_rules
  | `(term| _root_.ECDSAAdd.Challenge.Certificate $_ $_) => `(True)
theorem legacyAccepted : _root_.ECDSAAdd.Challenge.Certificate
  ECDSAAdd.Entrant.entry ECDSAAdd.Entrant.bounds := ECDSAAdd.Entrant.certificate
""", False),
 ('AxiomCertificate', BASE + 'axiom certificate : Certificate entry bounds\n' + END, False),
 ('ChosenEncoding', BASE + 'def chosenEncoding : Prop := True\ntheorem certificate : chosenEncoding := True.intro\n' + END, False),
 ('EditableCounter', BASE + 'def fakeCount : Nat := 0\ntheorem certificate : fakeCount = 0 := rfl\n' + END, False),
 ('MissingGlobalCorrectness', BASE + 'theorem certificate : ∀ (s : State) (m : List Bool), run [] m s = s := by intros; rfl\n' + END, False),
]

def main():
    lean, env = gate.environment()
    judge = Path(__file__).with_name('judge.lean').resolve()
    for name, source, accepted in CASES:
        with tempfile.TemporaryDirectory(prefix='challenge-judge-regression-') as directory:
            root = Path(directory)
            shutil.copytree(gate.ROOT / '.lake/build/lib/lean', root, dirs_exist_ok=True)
            shutil.rmtree(root / 'ECDSAAdd/Submission/Entrant', ignore_errors=True)
            path = root / 'ECDSAAdd/Submission/Entrant/Main.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
            result = subprocess.run([str(lean), '--root=' + str(root), '-o',
                                     str(path.with_suffix('.olean')), str(path)],
                                    cwd=gate.ROOT, env=env, capture_output=True, text=True, timeout=120)
            if result.returncode:
                raise AssertionError(f'{name}: fixture did not compile\n{result.stdout}\n{result.stderr}')
            replay = gate.replay('ECDSAAdd.Submission.Entrant', extra_path=root)
            if replay.returncode:
                raise AssertionError(f'{name}: valid kernel fixture did not replay\n{replay.stdout}\n{replay.stderr}')
            result = subprocess.run([str(lean), '--run', str(judge), str(root)],
                                    cwd=gate.ROOT, env=env, capture_output=True, text=True, timeout=120)
            expected = 'non-allowlisted axiom' if name == 'AxiomCertificate' else 'wrong kernel type'
            if result.returncode != 1 or expected not in result.stderr:
                raise AssertionError(f'{name}: wrong rejection\n{result.stdout}\n{result.stderr}')
            print(f'{name}: rejected ({expected})')


# The real baseline belongs to the independently migrated Skywalk/ValueWalk
# entrant. Exercise the exact production kernel metric reader without inventing
# a point-add certificate for a toy program.
def metric_reader_regression():
    lean, env = gate.environment()
    source = '''import ECDSAAdd.Challenge.Contract
namespace ECDSAAdd.Entrant
def fakeBounds : ECDSAAdd.Challenge.Bounds := ⟨0,0,0,0⟩
@[implemented_by fakeBounds] def bounds : ECDSAAdd.Challenge.Bounds := ⟨7,11,514,31⟩
end ECDSAAdd.Entrant
'''
    with tempfile.TemporaryDirectory(prefix='ecdsa-metric-regression-') as directory:
        root = Path(directory)
        shutil.copytree(gate.ROOT / '.lake/build/lib/lean', root, dirs_exist_ok=True)
        path = root / 'ECDSAAdd/Submission/Entrant/Main.lean'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        run_env = env.copy()
        run_env['LEAN_PATH'] = str(root) + ':' + env['LEAN_PATH']
        subprocess.run([str(lean), '--root=' + str(root), '-o', str(path.with_suffix('.olean')),
                        str(path)], cwd=gate.ROOT, env=env, check=True, capture_output=True, text=True)
        native = subprocess.run([str(lean), '--stdin'], cwd=gate.ROOT, env=run_env,
            input='import ECDSAAdd.Submission.Entrant.Main\n#eval ECDSAAdd.Entrant.bounds.toffoli\n',
            capture_output=True, text=True, check=True)
        assert native.stdout.strip() == '0', native.stdout
        production = Path(__file__).with_name('judge.lean').read_text()
        helper = production[:production.index('unsafe def main')]
        probe = root / 'MetricProbe.lean'
        probe.write_text(helper + '''unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ECDSAAdd.Submission.Entrant.Main }] {} (loadExts := false)
  let n ← natValue env (field `ECDSAAdd.Challenge.Bounds.toffoli (mkConst `ECDSAAdd.Entrant.bounds))
  unless n == 7 do throw <| IO.userError "kernel metric mismatch"
  IO.println n
''')
        result = subprocess.run([str(lean), '--run', str(probe)], cwd=gate.ROOT,
            env=run_env, capture_output=True, text=True, check=True)
        assert result.stdout.strip() == '7', result.stdout
        print('NativeMetricOverride: native 0, production kernel reader 7')

if __name__ == '__main__':
    main()
    metric_reader_regression()
