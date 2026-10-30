#!/usr/bin/env python3
"""Reject corrupted endpoint obligations and cadence trace counters."""
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    cases = []
    files = [ROOT / 'KernelR/Certificates/Local003.lean']
    # Exercise the newly introduced return-before-ERROR boundary, not just a
    # generic threshold check that already existed in the previous theorem.
    cadence = next(path for path in sorted((ROOT / 'KernelR/Certificates/Cadence010').glob('Checks*.lean'))
                   if 'return_before_ERROR_verified' in path.read_text())
    files.append(cadence)
    for path in files:
        source = path.read_text()
        pattern = (r'theorem \w*return_before_ERROR_verified : RationalBox.StrictBefore (\w+) (\w+) :='
                   if path == cadence else r'theorem \w+_verified : RationalBox.StrictBefore (\w+) (\w+) :=')
        left, right = re.search(pattern, source).groups()
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        namespace = module.rsplit('.', 1)[0] if path == cadence else module
        template = '''import {module}
open KernelR {namespace}
example : RationalBox.StrictBefore {left} {right} := by
  norm_num [RationalBox.StrictBefore, {left}, {right}]
'''
        cases.append((path.stem,
                      template.format(module=module, namespace=namespace, left=left, right=right),
                      template.format(module=module, namespace=namespace, left=left, right=left),
                      'unsolved goals'))
    trace = '''import KernelR.CadenceRecorded.Cadence010
open KernelR.Cadence KernelR.CadenceRecorded.Cadence010
example : checkSteps 3 0 {steps} = true := by decide
'''
    cases.append(('cadence counters', trace.format(steps='bFast'),
                  trace.format(steps='(bFast.map fun row => { row with gainDoses := 0 })'),
                  'false'))
    with tempfile.TemporaryDirectory(prefix='lean-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        for name, good, bad, diagnostic in cases:
            for should_pass, source in [(True, good), (False, bad)]:
                path.write_text(source)
                result = subprocess.run(
                    ['lake', 'env', 'lean', str(path)], cwd=ROOT,
                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    timeout=600,
                )
                if should_pass and result.returncode != 0:
                    raise SystemExit(name + ': positive control failed:\n' + result.stdout)
                if not should_pass and (result.returncode == 0 or diagnostic not in result.stdout):
                    raise SystemExit(name + ': expected proof rejection:\n' + result.stdout)
            print(name + ': valid evidence accepted; corruption rejected.', flush=True)


if __name__ == '__main__':
    main()
