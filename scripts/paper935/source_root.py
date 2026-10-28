"""Resolve the explicitly configured, pinned source checkout before expensive work."""
import os
from pathlib import Path
import subprocess

PIN = '64b5a13aa249f1360846657392e6c66817b26d0f'

def pinned_source():
    value = os.environ.get('ECDSA_PAPER_SOURCE')
    if not value:
        raise ValueError('ECDSA_PAPER_SOURCE must explicitly name the pinned source checkout')
    root = Path(value).expanduser().resolve()
    if not root.is_dir():
        raise ValueError(f'ECDSA_PAPER_SOURCE is not a directory: {root}')
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
    try:
        head = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'],
                                       env=env, text=True, stderr=subprocess.PIPE).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ValueError('ECDSA_PAPER_SOURCE must be a Git checkout at ' + PIN) from exc
    if head != PIN:
        raise ValueError(f'ECDSA_PAPER_SOURCE HEAD must be {PIN}, found {head}')
    dirty = subprocess.check_output(
        ['git', '-c', 'core.fsmonitor=false', '-C', str(root),
         'status', '--porcelain', '--untracked-files=all'],
        env=env, text=True, stderr=subprocess.PIPE)
    if dirty:
        raise ValueError('ECDSA_PAPER_SOURCE working tree must be clean (including untracked files)')
    return root

if __name__ == '__main__':
    try:
        pinned_source()
    except ValueError as exc:
        raise SystemExit(str(exc))
