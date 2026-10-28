#!/usr/bin/env python3
"""Conservative source-layer check, run in the isolated compiler worker.
Protected source integrity and kernel replay are separate mandatory boundaries.
"""
import os
from pathlib import Path
import re
ROOT = Path(os.environ.get('ECDSAADD_ROOT', Path(__file__).resolve().parents[2])).resolve()
def main():
    count = 0
    for folder in ('Challenge', 'Judge', 'Submission/Entrant'):
        for source in (ROOT / 'ECDSAAdd' / folder).rglob('*.lean'):
            imports = re.findall(r'^\s*import\s+([^\n]+)', source.read_text(), re.M)
            for line in imports:
                for module in line.split('--')[0].split():
                    if folder == 'Challenge' and module.startswith('ECDSAAdd.'):
                        if not module.startswith(('ECDSAAdd.Framework.', 'ECDSAAdd.Math.', 'ECDSAAdd.Challenge.')):
                            raise ValueError(f'{source}: protected contract imports implementation {module}')
                    if folder == 'Judge' and module.startswith('ECDSAAdd.') and not module.startswith('ECDSAAdd.Challenge.'):
                        raise ValueError(f'{source}: judge imports non-contract module {module}')
                    if folder == 'Submission/Entrant' and module.startswith('ECDSAAdd.Judge'):
                        raise ValueError(f'{source}: entrant imports judge')
            count += 1
    print(f'challenge source layer check passed: {count} files')
if __name__ == '__main__':
    main()
