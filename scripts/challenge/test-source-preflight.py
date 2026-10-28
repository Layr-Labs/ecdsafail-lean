#!/usr/bin/env python3
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('source_root', HERE.parent / 'paper935/source_root.py')
resolver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(resolver)

class Preflight(unittest.TestCase):
    def test_missing_environment(self):
        with patch.dict(os.environ, {}, clear=True):
            with self.assertRaisesRegex(ValueError, 'must explicitly'):
                resolver.pinned_source()

    def test_missing_directory(self):
        with tempfile.TemporaryDirectory() as root:
            with patch.dict(os.environ, ECDSA_PAPER_SOURCE=str(Path(root)/'missing')):
                with self.assertRaisesRegex(ValueError, 'not a directory'):
                    resolver.pinned_source()

    def test_wrong_revision(self):
        with tempfile.TemporaryDirectory() as root:
            subprocess.run(['git','init','-q',root],check=True)
            subprocess.run(['git','-C',root,'-c','user.name=Test','-c','user.email=test@example.test',
                            'commit','-q','--allow-empty','-m','different source'],check=True)
            with patch.dict(os.environ, ECDSA_PAPER_SOURCE=root):
                with self.assertRaisesRegex(ValueError, 'HEAD must be'):
                    resolver.pinned_source()

    def test_correct_head_dirty_worktree(self):
        with tempfile.TemporaryDirectory() as root:
            subprocess.run(['git','init','-q',root],check=True)
            tracked = Path(root)/'engine.py'
            tracked.write_text('original\n')
            subprocess.run(['git','-C',root,'add','engine.py'],check=True)
            subprocess.run(['git','-C',root,'-c','user.name=Test','-c','user.email=test@example.test',
                            'commit','-q','-m','pinned fixture'],check=True)
            pin = subprocess.check_output(['git','-C',root,'rev-parse','HEAD'],text=True).strip()
            with patch.dict(os.environ, ECDSA_PAPER_SOURCE=root), patch.object(resolver, 'PIN', pin):
                self.assertEqual(resolver.pinned_source(),Path(root).resolve())
                tracked.write_text('modified while HEAD stays pinned\n')
                self.assertEqual(subprocess.check_output(['git','-C',root,'rev-parse','HEAD'],text=True).strip(),pin)
                with self.assertRaisesRegex(ValueError, 'working tree must be clean'):
                    resolver.pinned_source()
                tracked.write_text('original\n')
                (Path(root)/'extra.py').write_text('untracked\n')
                with self.assertRaisesRegex(ValueError, 'working tree must be clean'):
                    resolver.pinned_source()

    def test_all_entries_check_source_before_build(self):
        for relative in ('scripts/benchmark.sh','scripts/challenge/validate.sh','scripts/challenge/verify.sh'):
            env = os.environ.copy()
            env.pop('ECDSA_PAPER_SOURCE', None)
            env['ECDSA_SOURCE_PYTHON'] = os.sys.executable
            result = subprocess.run(['bash',str(HERE.parents[1]/relative)],env=env,
                                    capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('ECDSA_PAPER_SOURCE must explicitly',result.stderr)

if __name__ == '__main__':
    unittest.main()
