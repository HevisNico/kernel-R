#!/usr/bin/env python3
"""Paired interface controls for the parametric family's quiet witnesses.

Each valid application compiles before its altered conclusion is rejected.
Rejection of a proof mutation is a regression check, not by itself a formal
proof of the negated proposition. These are quiet witnesses, not evidence of
active learning or of the nominal protocol at changed constants.
"""
from pathlib import Path
import re
import subprocess
import tempfile

from lean_check import lean_check_command


ROOT = Path(__file__).resolve().parents[1]
MODULE = 'KernelR.Family.Witnesses'
PREFIX = f'import {MODULE}\nnamespace KernelR.Family\nopen KernelR.Hybrid\n'
SUFFIX = '\nend KernelR.Family\n'


def main():
    field = '''example {n} (c : Constants) (theta : Fin n → Parameters)
    (s t : ℝ) (i : Fin n) (k : Coord) :
    field c theta (quiet c s) (quiet c s).x t i k = VALUE := by
  exact quiet_field c theta s t i k
'''
    safe = '''example {n} (c : Constants) (hc : Admissible c)
    (theta : Fin n → Parameters) {T : ℝ} (hT : 0 < T) (i : Fin n) :
    ENERGY_SIGN := by
  exact (quietFlow_safe c hc theta hT 0 ⟨le_refl _, hT.le⟩ i).1
'''
    jump = '''example {n} (c : Constants) (hc : Admissible c)
    (route : Router n) (T : ℝ) (u : Snapshot n) :
    AVAILABILITY (Jump c route (quiet c T) u) := by
  exact quiet_no_jump c hc
'''
    flow = '''example {n} (c : Constants) (hc : Admissible c)
    (theta : Fin n → Parameters) {T : ℝ} (hT : 0 < T) :
    ∃ f : Flow c theta (quiet c 0) (quiet c T), SAFETY := by
  exact safe_quiet_flow_exists c hc theta hT
'''
    complete = '''example {n} (c : Constants) (hc : Admissible c)
    (theta : Fin n → Parameters) (route : Router n) {T : ℝ} (hT : 0 < T) :
    ∃ e : Execution c theta route (quiet c 0) (quiet c T),
      CompleteThrough e HORIZON := by
  exact quiet_complete_exists c hc theta route hT
'''
    family = '''example {n} (theta : Fin n → Parameters)
    {T gain recovery : ℝ} (hT : 0 < T) (hg : 0 < gain) (hr : 0 < recovery) :
    ∃ f : Flow (nominal.withLearningFactors gain recovery) theta
      (quiet (nominal.withLearningFactors gain recovery) 0)
      (quiet (nominal.withLearningFactors gain recovery) T), SAFETY := by
  exact learning_factor_family_quiet_flows theta hT hg hr
'''
    cases = [
        ('quiet_field',
         field.replace('VALUE', '0'), field.replace('VALUE', '1')),
        ('quietFlow_safe',
         safe.replace('ENERGY_SIGN', '0 < (quietFlow c hc theta hT).path 0 i .energy'),
         safe.replace('ENERGY_SIGN', '(quietFlow c hc theta hT).path 0 i .energy < 0')),
        ('quiet_no_jump',
         jump.replace('AVAILABILITY', 'IsEmpty'), jump.replace('AVAILABILITY', 'Nonempty')),
        ('safe_quiet_flow_exists',
         flow.replace('SAFETY', 'f.Safe'), flow.replace('SAFETY', '¬ f.Safe')),
        ('quiet_complete_exists',
         complete.replace('HORIZON', 'T'), complete.replace('HORIZON', '(T + 1)')),
        ('learning_factor_family_quiet_flows',
         family.replace('SAFETY', 'f.Safe'), family.replace('SAFETY', '¬ f.Safe')),
    ]
    source = (ROOT / 'KernelR/Family/Witnesses.lean').read_text()
    declared = set(re.findall(r'^(?:@\[[^\n]*\]\s*)?theorem\s+([\w.]+)', source, re.M))
    covered = {name for name, _, _ in cases}
    if declared != covered:
        raise SystemExit(f'Witnesses: coverage mismatch; missing={sorted(declared-covered)}, '
                         f'unknown={sorted(covered-declared)}')
    with tempfile.TemporaryDirectory(prefix='family-witnesses-negative-', dir=ROOT) as temporary:
        path = Path(temporary) / 'Check.lean'
        command = lean_check_command(temporary, root_module=MODULE)
        for name, good, bad in cases:
            for expected, source in [(True, good), (False, bad)]:
                path.write_text(PREFIX + source + SUFFIX)
                result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                        timeout=120)
                if (result.returncode == 0) != expected:
                    raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
                if not expected and 'error:' not in result.stdout:
                    raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')
                if not expected and re.search(
                        r'unknown (constant|identifier)|unexpected token|invalid syntax|'
                        r'object file .* does not exist|unknown module prefix', result.stdout, re.I):
                    raise SystemExit(f'{name}: nonsemantic rejection:\n{result.stdout}')
            print(f'{name}: valid witness accepted; altered conclusion rejected.', flush=True)
    print(f'All {len(cases)} paired quiet-family witness controls passed.', flush=True)


if __name__ == '__main__':
    main()
