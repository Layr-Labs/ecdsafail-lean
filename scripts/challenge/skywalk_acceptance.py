"""Organizer regression: compile a Skywalk entrant in a trusted temporary overlay."""
import json
import shutil
import subprocess
import tempfile
from pathlib import Path
import gate

SOURCE = '''import ECDSAAdd.Baselines.SkywalkCertificate
namespace ECDSAAdd.Entrant
def entry : Challenge.Entry := Baselines.normalizedSkywalk
def bounds : Challenge.Bounds := Baselines.skywalkBounds
theorem certificate : Challenge.Certificate entry bounds := Baselines.skywalkCertificate
end ECDSAAdd.Entrant
'''


def main():
    lean, env = gate.environment()
    with tempfile.TemporaryDirectory(prefix='ecdsa-skywalk-acceptance-') as directory:
        root = Path(directory)
        shutil.copytree(gate.ROOT / '.lake/build/lib/lean', root, dirs_exist_ok=True)
        shutil.rmtree(root / 'ECDSAAdd/Submission/Entrant', ignore_errors=True)
        source = root / 'ECDSAAdd/Submission/Entrant/Main.lean'
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(SOURCE)
        result = subprocess.run([str(lean), '--root=' + str(root), '-o',
                                 str(source.with_suffix('.olean')), str(source)],
                                cwd=gate.ROOT, env=env, capture_output=True, text=True, timeout=120)
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)
        replay = gate.replay('ECDSAAdd.Submission.Entrant', extra_path=root)
        if replay.returncode:
            raise AssertionError(replay.stdout + replay.stderr)
        result = subprocess.run([str(lean), '--run', str(Path(__file__).with_name('judge.lean').resolve()),
                                 str(root)], cwd=gate.ROOT, env=env,
                                capture_output=True, text=True, timeout=600)
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)
        expected = dict(accepted=True, score_toffoli_upper_bound=2217386,
                        measurements_upper_bound=1557928, qubits_upper_bound=1899,
                        all_syntax_slots_upper_bound=47000000,
                        qubits_times_toffoli_upper_bound=1899*2217386)
        assert json.loads(result.stdout) == expected, result.stdout
    print('Skywalk: independent kernel replay and trusted judge acceptance passed')


if __name__ == '__main__':
    main()
