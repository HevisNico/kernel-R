#!/usr/bin/env python3
"""Paired contract controls for recovery-limited native and crossing firings.

Each valid use must compile before its altered conclusion is tested. Rejections
must be semantic Lean errors, not missing imports, names or parse failures.
These are contract mutation controls, not proofs of counterexamples.
"""
from pathlib import Path
import re
import subprocess
import tempfile
from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
MODULE = 'KernelR.HybridResetRateCrossing'
PREFIX = f'import {MODULE}\nopen KernelR.Hybrid\n'

def main():
    gap = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (β : ℝ) (hβ : 0 < β) (bound : e.RecoveryBound i β) :
    (e.emissionTimes i).Pairwise
      (fun first second => first + ({fast} + Real.log (5 / 2) / β) ≤ second) := by
  exact e.emissionTimes_separated_of_recovery_bound i β hβ bound
"""
    capped = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (bound : s.x i .b ≤ 11 / 10) :
    (e.emissionTimes i).Pairwise
      (fun first second => first + (1 + Real.log (5 / 2) / ({cap})) ≤ second) := by
  exact e.emissionTimes_separated i bound
"""
    count = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (β : ℝ) (hβ : 0 < β) (bound : e.RecoveryBound i β) :
    (((e.emissionTimes i).length : ℝ) - {allowance}) *
      (1 + Real.log (5 / 2) / β) ≤ u.time - s.time := by
  exact e.firing_count_bound_of_recovery_bound i β hβ bound
"""
    ceiling = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (β : ℝ) (hβ : 0 < β) (bound : e.RecoveryBound i β) :
    ((e.emissionTimes i).length : ℝ) ≤ {allowance} +
      (u.time - s.time) / (1 + Real.log (5 / 2) / β) := by
  exact e.firing_count_ceiling_of_recovery_bound i β hβ bound
"""
    envelope = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (β : ℝ) (hβ : 0 < β) (bound : {bound}) :
    (e.emissionTimes i).Pairwise
      (fun first second => first + (1 + Real.log (5 / 2) / β) ≤ second) := by
  exact e.emissionTimes_separated_of_recovery_bound i β hβ bound
"""
    slow = """example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (β : ℝ) (hβ : 0 < β) (modes : e.MainFlows i .slow)
    (initial : s.x i .q = 1 / 4) (final : u.x i .q = 1 / 10)
    (bound : e.RecoveryBound i β) :
    Real.log ({ratio}) / β ≤ u.time - s.time := by
  exact e.slow_duration_lower_of_bound i β hβ modes initial final bound
"""
    decimal = """example : (18329915 / 10000000 : ℝ) <
    1 + Real.log (5 / 2) / (11 / 10) ∧
    1 + Real.log (5 / 2) / (11 / 10) < {upper} := by
  exact reset_gap_cap_bounds
"""
    weak = """example {{n θ route s u}} (e : @WeakExecution n θ route s u)
    (i : Fin n) (bound : s.x i .b ≤ 11 / 10) :
    (e.emissionTimes i).Pairwise
      (fun first second => first + ({fast} + Real.log (5 / 2) / (11 / 10)) ≤ second) := by
  exact e.emissionTimes_separated i bound
"""
    crossing = """example {{n θ route s u}} (e : @CrossingExecution n θ route s u)
    (i : Fin n) (bound : s.x i .b ≤ 11 / 10) :
    (e.execution.emissionTimes i).Pairwise
      (fun first second => first + ({fast} + Real.log (5 / 2) / (11 / 10)) ≤ second) := by
  exact e.emissionTimes_separated i bound
"""
    crossing_count = """example {{n θ route s u}} (e : @CrossingExecution n θ route s u)
    (i : Fin n) (β : ℝ) (hβ : 0 < β) (bound : e.execution.RecoveryBound i β) :
    ((e.execution.emissionTimes i).length : ℝ) ≤ {allowance} +
      (u.time - s.time) / (1 + Real.log (5 / 2) / β) := by
  exact e.firing_count_ceiling_of_recovery_bound i β hβ bound
"""
    cases = [
      ('native exact FAST contribution', gap.format(fast='1'), gap.format(fast='2')),
      ('uniform recovery cap', capped.format(cap='11 / 10'), capped.format(cap='1')),
      ('finite count boundary allowance', count.format(allowance='1'), count.format(allowance='0')),
      ('finite rate ceiling allowance', ceiling.format(allowance='1'), ceiling.format(allowance='0')),
      ('pathwise envelope is required',
       envelope.format(bound='e.RecoveryBound i β'), envelope.format(bound='s.x i .b ≤ β')),
      ('SLOW integrated recovery ratio', slow.format(ratio='5 / 2'), slow.format(ratio='4')),
      ('certified decimal bracket',
       decimal.format(upper='18329916 / 10000000'), decimal.format(upper='18329915 / 10000000')),
      ('weak execution bound', weak.format(fast='1'), weak.format(fast='2')),
      ('crossing execution bound', crossing.format(fast='1'), crossing.format(fast='2')),
      ('crossing finite-window ceiling', crossing_count.format(allowance='1'), crossing_count.format(allowance='0')),
    ]
    with tempfile.TemporaryDirectory(prefix='reset-rate-controls-',dir=ROOT) as tmp:
        command=lean_check_command(tmp,root_module=MODULE)
        path=Path(tmp)/'Check.lean'
        for name,good,bad in cases:
            for expected,source in [(True,good),(False,bad)]:
                path.write_text(PREFIX+source)
                result=subprocess.run([*command,str(path)],cwd=ROOT,text=True,
                    stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
                if (result.returncode==0)!=expected:
                    raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
                if not expected:
                    if 'error:' not in result.stdout or not re.search(
                            r'Type mismatch|type mismatch|Application type mismatch|failed to synthesize',result.stdout):
                        raise SystemExit(f'{name}: rejection was not a contract mismatch:\n{result.stdout}')
                    if re.search(r'unknown identifier|unknown module|object file.*does not exist|unexpected token|unexpected end',result.stdout):
                        raise SystemExit(f'{name}: invalid negative fixture:\n{result.stdout}')
            print(f'{name}: valid contract accepted; mutation rejected.',flush=True)
    print(f'Passed {len(cases)} paired reset-rate controls.',flush=True)

if __name__=='__main__':
    main()
