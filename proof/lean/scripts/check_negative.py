#!/usr/bin/env python3
"""Ensure an impossible version of a published endpoint obligation is rejected."""
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    source = (ROOT / 'KernelR/Certificates/Local003.lean').read_text()
    left, right = re.search(
        r'theorem \w+_verified : RationalBox.StrictBefore (\w+) (\w+) :=', source
    ).groups()
    template = '''import KernelR.Certificates.Local003
open KernelR KernelR.Certificates.Local003
example : RationalBox.StrictBefore {left} {right} := by
  norm_num [RationalBox.StrictBefore, {left}, {right}]
'''
    with tempfile.TemporaryDirectory(prefix='lean-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        for should_pass, end in [(True, right), (False, left)]:
            path.write_text(template.format(left=left, right=end))
            result = subprocess.run(
                ['lake', 'env', 'lean', str(path)], cwd=ROOT,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=600,
            )
            if should_pass and result.returncode != 0:
                raise SystemExit('Positive control failed:\n' + result.stdout)
            if not should_pass and (result.returncode == 0 or 'unsolved goals' not in result.stdout):
                raise SystemExit('Expected a failed proof of a strict self-comparison:\n' + result.stdout)
    print('Negative check passed: a real obligation compiles; its strict self-comparison is rejected.')


if __name__ == '__main__':
    main()
