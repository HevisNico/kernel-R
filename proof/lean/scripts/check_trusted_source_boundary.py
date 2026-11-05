#!/usr/bin/env python3
"""Authenticate the unchanged Lean base of the dedicated trusted-headline PR."""
import hashlib
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[3]
BASE = '17928f25086bd8e1765dee1fbf6acce8ebc1b673'
IMPORTS = {
    'import KernelR.ExplicitFiniteChainRouter',
    'import KernelR.TrustedHeadline',
    'import KernelR.TrustedBaseChecker',
    'import KernelR.TrustedBase',
}
NEW_MODULES = {f'proof/lean/KernelR/{name}.lean' for name in
               ['ExplicitFiniteChainRouter', 'TrustedHeadline', 'TrustedBaseChecker', 'TrustedBase']}
ENTRY = 'proof/lean/KernelR.lean'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def check_imports(before, after):
    expected = before.splitlines()
    index = 0
    for line in after.splitlines():
        if index < len(expected) and line == expected[index]:
            index += 1
        elif line not in IMPORTS:
            raise ValueError('KernelR.lean contains a change other than a declared added import.')
    if index != len(expected):
        raise ValueError('An existing KernelR.lean import was changed or removed.')


def main():
    old = {}
    for entry in git('ls-tree', '-rz', BASE, 'proof/lean').split(b'\0'):
        if not entry:
            continue
        metadata, path = entry.split(b'\t', 1)
        path = path.decode()
        if path.endswith('.lean'):
            old[path] = metadata.split()[2].decode()
    for path, expected in old.items():
        if path == ENTRY:
            check_imports(git('show', f'{BASE}:{path}').decode(), (ROOT / path).read_text())
        elif not (ROOT / path).is_file() or blob((ROOT / path).read_bytes()) != expected:
            raise SystemExit('Existing Lean source changed or removed: ' + path)
    current = {path.decode() for path in git('ls-files', '-z', 'proof/lean').split(b'\0')
               if path.endswith(b'.lean')}
    unexpected = current - old.keys() - NEW_MODULES
    if unexpected:
        raise SystemExit('Unexpected new Lean module: ' + ', '.join(sorted(unexpected)))
    print(f'Existing Lean sources unchanged at base {BASE}; only declared imports/modules added.')


if __name__ == '__main__':
    main()
