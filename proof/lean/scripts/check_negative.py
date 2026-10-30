#!/usr/bin/env python3
"""Reject corrupted endpoint obligations, cadence counters and adaptive scores."""
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
    files.append(ROOT / 'KernelR/Certificates/Composition010.lean')
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
    recorded=(ROOT/'KernelR/Recorded.lean').read_text()
    score=int(re.search(r'theorem test_successes : successes test = (\d+)',recorded).group(1))
    replay='''import KernelR.Recorded
open KernelR.Recorded
set_option maxRecDepth 100000
set_option maxHeartbeats 0
example : successes test = {score} := by decide
'''
    cases.append(('adaptive score',replay.format(score=score),replay.format(score=score+1),'false'))
    chain = '''import KernelR.Chain.Induction
open KernelR.Chain
example : traffic 16 1 = {count} := by decide
'''
    cases.append(('N-cell traffic', chain.format(count=11), chain.format(count=12), 'false'))
    jitter = '''import KernelR.Chain.Induction
open KernelR.Chain
example : pathJitter (fun _ => (1 / 20 : ℝ)) {links} ≤ 3 / 20 := by
  norm_num [pathJitter]
'''
    cases.append(('N-cell jitter', jitter.format(links=3), jitter.format(links=4), 'unsolved goals'))
    robust = '''import KernelR.Robust.Induction
open KernelR.Robust KernelR.Chain
example : 15/2 + 2 * pathJitter (fun _ => (187/25000 : ℝ)) {links} ≤ 8 := by
  rw [constant_jitter]
  norm_num
'''
    cases.append(('robust latency budget', robust.format(links=31),
                  robust.format(links=34), 'unsolved goals'))
    counts = '''import KernelR.Robust.Induction
open KernelR.Robust
example : traffic 104 32 = {count} := by decide
'''
    cases.append(('robust exact traffic', counts.format(count=1744),
                  counts.format(count=1745), 'false'))
    decomposition = '''import KernelR.Robust.Packets
open KernelR.Robust
example : (4/5 : ℝ) = 3/5 - max (3/5-4/5) 0 + {late} := by norm_num
'''
    cases.append(('first firing delay is retained', decomposition.format(late='1/5'),
                  decomposition.format(late='0'), 'unsolved goals'))
    entry = '''import KernelR.Robust.Evidence.Birth0
open KernelR KernelR.Robust.Evidence.Birth0
example : RationalBox.StrictBefore
    entry_charge_radius_inside_local_section_left {right} := by
  norm_num [RationalBox.StrictBefore, entry_charge_radius_inside_local_section_left,
    entry_charge_radius_inside_local_section_right]
'''
    cases.append(('robust entry boundary',
                  entry.format(right='entry_charge_radius_inside_local_section_right'),
                  entry.format(right='entry_charge_radius_inside_local_section_left'), 'unsolved goals'))
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
