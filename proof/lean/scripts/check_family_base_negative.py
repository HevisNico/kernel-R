#!/usr/bin/env python3
"""Paired semantic controls for family constants, semantics and reserve barriers.

Every public theorem in the four owned modules is listed below. Each positive
application compiles before an altered conclusion with unchanged premises is
rejected. This checks the advertised interface, rather than asserting that a
compiler rejection alone proves the negation of the modified proposition.
"""
import argparse
import json
from pathlib import Path
import re
from family_control_batches import check_batches

ROOT = Path(__file__).resolve().parents[1]
MODULES = ['Constants', 'Model', 'Nominal', 'Energy']


def cases():
    out = []

    def add(module, name, good, before, after, covers=None):
        if good.count(before) != 1:
            raise AssertionError((name, before, good.count(before)))
        out.append(dict(module=module, name=name, good=good,
                        bad=good.replace(before, after, 1),
                        covers=[name] if covers is None else covers))

    for name, const in [('nominal_admissible', 'nominal'),
                        ('alternative_admissible', 'alternative')]:
        add('Constants', name, f'''example : 0 < {const}.pulseWidth := by
  exact {name}.pulseWidth_pos
''', f'0 < {const}.pulseWidth', f'{const}.pulseWidth < 0')
    for name, coord in [('Admissible.errorDose_pos', 'errorDose'),
                        ('Admissible.markDose_pos', 'markDose')]:
        add('Constants', name, f'''example {{c}} (h : Admissible c) : 0 < c.{coord} := by
  exact h.{coord}_pos
''', f'0 < c.{coord} :=', f'c.{coord} ≤ 0 :=')
    for name, coord, value, changed in [('nominal_errorDose', 'errorDose', '3/5', '4/5'),
                                       ('nominal_markDose', 'markDose', '1/10', '2/10')]:
        add('Constants', name, f'''example : nominal.{coord} = {value} := by
  exact {name}
''', f'= {value} :=', f'= {changed} :=')
    add('Constants', 'Admissible.withLearningFactors', '''example {c} (h : Admissible c)
    {gain recovery : ℝ} (hg : 0 < gain) (hr : 0 < recovery) :
    0 < (c.withLearningFactors gain recovery).gainFactor := by
  exact (h.withLearningFactors hg hr).gainFactor_pos
''', '0 < (c.withLearningFactors gain recovery).gainFactor :=',
        '(c.withLearningFactors gain recovery).gainFactor ≤ 0 :=')
    add('Constants', 'withLearningFactors_ne_nominal', '''example {gain recovery : ℝ}
    (h : gain ≠ 8) : nominal.withLearningFactors gain recovery ≠ nominal := by
  exact withLearningFactors_ne_nominal h
''', 'gain recovery ≠ nominal :=', 'gain recovery = nominal :=')
    add('Constants', 'alternative_doses', '''example :
    alternative.errorDose = 1/2 ∧ alternative.markDose = 1/8 := by
  exact alternative_doses
''', 'alternative.markDose = 1/8', 'alternative.markDose = 1/4')
    add('Constants', 'alternative_ne_nominal', '''example : alternative ≠ nominal := by
  exact alternative_ne_nominal
''', ': alternative ≠ nominal :=', ': alternative = nominal :=')

    add('Model', 'Jump.physical_continuous', '''example {n c route s u}
    (j : @Jump n c route s u) (i : Fin n) : u.x i .q = s.x i .q := by
  exact congrFun (congrFun j.physical_continuous i) .q
''', '= s.x i .q :=', '= s.x i .q + 1 :=')
    add('Model', 'Jump.time_unchanged', '''example {n c route s u}
    (j : @Jump n c route s u) : u.time = s.time := by
  exact j.time_unchanged
''', '= s.time :=', '= s.time + 1 :=')

    add('Nominal', 'pulse_nominal', '''example (origin t : ℝ) :
    pulse nominal origin t = Hybrid.pulse origin t := by
  exact pulse_nominal origin t
''', '= Hybrid.pulse origin t :=', '= Hybrid.pulse origin t + 1 :=')
    add('Nominal', 'current_nominal', '''example {n} (s : Snapshot n)
    (i : Fin n) (p : Port) (t : ℝ) :
    current nominal s i p t = Hybrid.current s i p t := by
  exact current_nominal s i p t
''', '= Hybrid.current s i p t :=', '= Hybrid.current s i p t + 1 :=')
    for name in ['errorAct', 'markAct']:
        add('Nominal', name + '_nominal', f'''example {{n}} (θ : Fin n → Parameters)
    (s : Snapshot n) (x : Values n) (i : Fin n) (p : Port) :
    {name} nominal θ s x i p = Hybrid.{name} θ s x i p := by
  exact {name}_nominal θ s x i p
''', f'= Hybrid.{name} θ s x i p :=', f'= Hybrid.{name} θ s x i p + 1 :=')
    add('Nominal', 'field_nominal', '''example {n} (θ : Fin n → Parameters)
    (s : Snapshot n) (x : Values n) (t : ℝ) (i : Fin n) (k : Coord) :
    field nominal θ s x t i k = Hybrid.field θ s x t i k := by
  exact field_nominal θ s x t i k
''', '= Hybrid.field θ s x t i k :=', '= Hybrid.field θ s x t i k + 1 :=')
    add('Nominal', 'beforeGuards_nominal', '''example {n} (s : Snapshot n) (x : Values n) :
    BeforeGuards nominal s x ↔ Hybrid.BeforeGuards s x := by
  exact beforeGuards_nominal s x
''', '↔ Hybrid.BeforeGuards s x :=', '↔ ¬ Hybrid.BeforeGuards s x :=')
    add('Nominal', 'Flow.toNative_path', '''example {n θ s u}
    (f : @Flow n nominal θ s u) (t : ℝ) (i : Fin n) :
    f.toNative.path t i .q = f.path t i .q := by
  exact congrFun (congrFun (congrFun f.toNative_path t) i) .q
''', '= f.path t i .q :=', '= f.path t i .q + 1 :=')
    add('Nominal', 'execution_exists_iff', '''example {n θ route s u} :
    Nonempty (@Execution n nominal θ route s u) ↔
      Nonempty (Hybrid.Execution θ route s u) := by
  exact execution_exists_iff
''', '↔\n      Nonempty (Hybrid.Execution θ route s u)',
        '↔\n      IsEmpty (Hybrid.Execution θ route s u)')
    add('Nominal', 'completeThrough_iff', '''example {n θ route s u}
    (e : @Execution n nominal θ route s u) (T : ℝ) :
    CompleteThrough e T ↔ Hybrid.CompleteThrough e.toNative T := by
  exact completeThrough_iff e T
''', '↔ Hybrid.CompleteThrough e.toNative T :=',
        '↔ Hybrid.CompleteThrough e.toNative (T + 1) :=')

    # Additional interface checks exercise both directions of the constructive
    # bridge, not only the existence equivalence or scalar field equalities.
    add('Nominal', 'Flow.ofNative-path', '''example {n θ s u}
    (f : @Hybrid.Flow n θ s u) (t : ℝ) (i : Fin n) :
    (Flow.ofNative f).path t i .q = f.path t i .q := by rfl
''', '= f.path t i .q :=', '= f.path t i .q + 1 :=', covers=[])
    for direction, source, conversion in [
            ('toNative', '@Jump n nominal route s u', 'j.toNative'),
            ('ofNative', '@Hybrid.Jump n route s u', '(Jump.ofNative j)')]:
        add('Nominal', 'Jump.' + direction + '-coordinates', f'''example {{n route s u}}
    (j : {source}) (i : Fin n) : u.x i .q = s.x i .q := by
  exact congrFun (congrFun {conversion}.physical_continuous i) .q
''', '= s.x i .q :=', '= s.x i .q + 1 :=', covers=[])

    for bound in ['lower', 'upper']:
        below = bound == 'lower'
        initial = 'lower ≤ s.x i .energy' if below else 's.x i .energy ≤ upper'
        constraint = ('work C θ s (f.path v) i v ≤ C.energyRate * (C.energyTarget - lower)'
                      if below else 'C.energyRate * (C.energyTarget - upper) ≤ work C θ s (f.path v) i v')
        conclusion = 'lower ≤ f.path t i .energy' if below else 'f.path t i .energy ≤ upper'
        false = 'lower + 1 ≤ f.path t i .energy' if below else 'f.path t i .energy ≤ upper - 1'
        add('Energy', 'Flow.energy_' + bound, f'''example {{n C θ s u}}
    (f : @Flow n C θ s u) (rate : 0 ≤ C.energyRate) (i : Fin n) ({bound} : ℝ)
    (initial : {initial})
    (workBound : ∀ v ∈ Icc s.time u.time, {constraint})
    {{t : ℝ}} (ht : t ∈ Icc s.time u.time) : {conclusion} := by
  exact f.energy_{bound} rate i {bound} initial workBound ht
''', f': {conclusion} :=', f': {false} :=')
    add('Energy', 'Flow.safe_of_work_ceiling', '''example {n C θ s u}
    (f : @Flow n C θ s u) (signs : FlowSigns C) (rest : 0 ≤ C.auxRest)
    (rates : RatesNonnegative θ) (input : ∀ i p, 0 ≤ (θ i).inputGain p)
    (initialAux : ∀ i p, 0 ≤ s.x i (.m p))
    (initialRecovery : ∀ i, 0 ≤ s.x i .b) (lower : ℝ) (positive : 0 < lower)
    (initialEnergy : ∀ i, lower ≤ s.x i .energy)
    (ceiling : ∀ v ∈ Icc s.time u.time, ∀ i,
      work C θ s (f.path v) i v ≤ C.energyRate * (C.energyTarget - lower))
    {t : ℝ} (ht : t ∈ Icc s.time u.time) (i : Fin n) :
    0 < f.path t i .energy := by
  exact (f.safe_of_work_ceiling signs rest rates input initialAux initialRecovery
    lower positive initialEnergy ceiling t ht i).1
''', '0 < f.path t i .energy :=', 'f.path t i .energy < 0 :=')
    return out


def check_coverage(controls):
    for module in MODULES:
        source = (ROOT / f'KernelR/Family/{module}.lean').read_text()
        declared = set(re.findall(r'^(?:@\[[^\n]*\]\s*)?theorem\s+([\w.]+)', source, re.M))
        covered = {name for case in controls if case['module'] == module
                   for name in case['covers']}
        if declared != covered:
            raise SystemExit(f'{module}: coverage mismatch; missing={sorted(declared-covered)}, '
                             f'unknown={sorted(covered-declared)}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', action='append', help='run exact case name (repeatable)')
    parser.add_argument('--inventory', action='store_true')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--timeout', type=int, default=120,
                        help='seconds allowed for each complete Lean batch')
    args = parser.parse_args()
    controls = cases()
    check_coverage(controls)
    if args.inventory:
        print(json.dumps([{k: c[k] for k in ['module', 'name', 'covers']}
                          for c in controls], indent=2))
        return
    if args.case:
        names = {c['name'] for c in controls}
        if set(args.case) - names:
            parser.error('unknown cases: ' + ', '.join(sorted(set(args.case) - names)))
        controls = [c for c in controls if c['name'] in args.case]
    report = check_batches(ROOT, controls,
                           imports=['KernelR.Family.Nominal', 'KernelR.Family.Energy'],
                           root_module='KernelR.Family.Energy', timeout=args.timeout)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(f'All {len(controls)} paired family base controls passed.', flush=True)


if __name__ == '__main__':
    main()
