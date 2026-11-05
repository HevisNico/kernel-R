#!/usr/bin/env python3
"""Paired interface controls for the parametric family's quiet witnesses.

Each valid application compiles before its altered conclusion is rejected.
Rejection of a proof mutation is a regression check, not by itself a formal
proof of the negated proposition. These are quiet witnesses, not evidence of
active learning or of the nominal protocol at changed constants.
"""
import argparse
import json
from pathlib import Path
import re
from family_control_batches import run_batches


ROOT = Path(__file__).resolve().parents[1]
MODULE = 'KernelR.Family.Witnesses'
PREFIX = f'import {MODULE}\nnamespace KernelR.Family\nopen KernelR.Hybrid\n'
SUFFIX = '\nend KernelR.Family\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', action='append', help='run exact theorem name (repeatable)')
    parser.add_argument('--inventory', action='store_true')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--timeout', type=int, default=120,
                        help='seconds allowed for each complete Lean batch')
    args = parser.parse_args()
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
    if args.inventory:
        print(json.dumps([name for name, _, _ in cases], indent=2))
        return
    if args.case:
        if set(args.case) - covered:
            parser.error('unknown cases: ' + ', '.join(sorted(set(args.case) - covered)))
        cases = [case for case in cases if case[0] in args.case]
    report = run_batches(cases, PREFIX, SUFFIX, root=ROOT,
                         root_module=MODULE, timeout=args.timeout)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(f'All {len(cases)} paired quiet-family witness controls passed.', flush=True)


if __name__ == '__main__':
    main()
