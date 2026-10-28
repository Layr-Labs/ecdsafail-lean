#!/usr/bin/env python3
import contextlib
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent


def load(path):
    spec = importlib.util.spec_from_file_location('boundary_fixture', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class RunnerBoundary(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.candidate = self.root / 'candidate'
        self.candidate.mkdir()

    def test_source_gate_uses_explicit_candidate(self):
        (self.candidate / 'ECDSAAdd.lean').write_text('-- debug.skipKernelTC\n')
        result = subprocess.run([sys.executable, str(HERE / 'gate.py'), '--root',
                                 str(self.candidate), '--source-only'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn('skipKernelTC is forbidden', result.stderr)

    def test_import_layers_block_both_directions(self):
        with mock.patch.dict(os.environ, ECDSAADD_ROOT=str(self.candidate)):
            module = load(HERE / 'check-layers.py')
        for relative, source in [
                ('Submission/Entrant/Bad.lean', 'import ECDSAAdd.Judge.Main\n'),
                ('Judge/Bad.lean', 'import ECDSAAdd.Submission.Entrant.Main\n'),
                ('Challenge/Bad.lean', 'import ECDSAAdd.Submissions.Skywalk\n')]:
            path = self.candidate / 'ECDSAAdd' / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
            with self.assertRaises(ValueError):
                module.main()
            path.unlink()

    def fixture_artifacts(self):
        prefix = Path('ECDSAAdd/Submission/Entrant')
        source = self.candidate / prefix / 'Main.lean'
        source.parent.mkdir(parents=True)
        source.write_text('entrant')
        artifact = self.candidate / '.lake/build/lib/lean' / prefix / 'Main.olean'
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b'entrant-output')
        injected = self.candidate / '.lake/build/lib/lean/ECDSAAdd/Challenge/Contract.olean'
        injected.parent.mkdir(parents=True)
        injected.write_bytes(b'forged-protected')
        trusted = self.root / 'trusted-lib'
        protected = trusted / 'ECDSAAdd/Challenge/Contract.olean'
        protected.parent.mkdir(parents=True)
        protected.write_bytes(b'trusted-protected')
        overlay = self.root / 'overlay'
        overlay.mkdir()
        return artifact, trusted, overlay

    def test_only_entrant_outputs_replace_trusted_artifacts(self):
        artifact, trusted, overlay = self.fixture_artifacts()
        module = load(HERE / 'stage-entrant.py')
        self.assertEqual(module.stage(self.candidate, overlay, trusted), 1)
        self.assertEqual((overlay / 'ECDSAAdd/Challenge/Contract.olean').read_bytes(), b'trusted-protected')
        self.assertEqual((overlay / 'ECDSAAdd/Submission/Entrant/Main.olean').read_bytes(), artifact.read_bytes())

    def test_worker_artifact_symlink_rejected(self):
        artifact, trusted, overlay = self.fixture_artifacts()
        artifact.unlink()
        artifact.symlink_to(trusted / 'ECDSAAdd/Challenge/Contract.olean')
        with self.assertRaisesRegex(ValueError, 'symlink'):
            load(HERE / 'stage-entrant.py').stage(self.candidate, overlay, trusted)


if __name__ == '__main__':
    unittest.main()
