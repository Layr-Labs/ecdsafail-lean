"""Organizer regression for the real ValueWalk entrant, with kernel replay."""
import json
import subprocess
from pathlib import Path
import gate


def main():
    replay = gate.replay('ECDSAAdd.Submission.Entrant')
    if replay.returncode:
        raise AssertionError(replay.stdout + replay.stderr)
    lean, env = gate.environment()
    result = subprocess.run([str(lean), '--run', str(Path(__file__).with_name('judge.lean').resolve())],
                            cwd=gate.ROOT, env=env, text=True, capture_output=True, timeout=600)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    expected = dict(accepted=True, score_toffoli_upper_bound=6286806,
                    measurements_upper_bound=3779274, qubits_upper_bound=3134,
                    all_syntax_slots_upper_bound=61000000,
                    qubits_times_toffoli_upper_bound=19702850004)
    assert json.loads(result.stdout) == expected, result.stdout
    print('ValueWalk: independent kernel replay and trusted judge acceptance passed')


if __name__ == '__main__':
    main()
