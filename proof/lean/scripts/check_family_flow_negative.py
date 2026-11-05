#!/usr/bin/env python3
"""Paired semantic controls for the parametric flow/barrier interface.

Each valid application is compiled before a stronger, false conclusion with the
same premises is rejected. Rejections caused by parser errors or missing names
are refused. The Family audit separately checks permitted axiom dependencies.
"""
from pathlib import Path
import re
import json
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
MODULE = 'KernelR.Family.FlowUniqueness'
PREFIX = f'''import {MODULE}
open KernelR.Hybrid KernelR.Family Set
'''


def cases():
    out = []

    def add(name, good, before, after):
        if good.count(before) != 1:
            raise AssertionError((name, before, good.count(before)))
        out.append((name, good, good.replace(before, after, 1)))

    for scope in ['Flow', 'Execution']:
        flow = scope == 'Flow'
        args = '''{n C θ s u} (e : @KernelR.Family.Flow n C θ s u)''' if flow else '''{n C θ route s u} (e : @KernelR.Family.Execution n C θ route s u)'''
        add(f'{scope}.gain_cap', f'''example {args} (i : Fin n) (p : Port)
    (initial : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) ≤ Real.log ((θ i).cap p) := by
  exact e.gain_cap i p initial
''', 'u.x i (.z p) ≤ Real.log ((θ i).cap p)', 'u.x i (.z p) ≤ Real.log ((θ i).cap p) - 1')
        add(f'{scope}.recovery_cap', f'''example {args} (i : Fin n)
    (initial : s.x i .b ≤ C.recoveryCap) :
    u.x i .b ≤ C.recoveryCap := by
  exact e.recovery_cap i initial
''', 'u.x i .b ≤ C.recoveryCap', 'u.x i .b ≤ C.recoveryCap - 1')

    add('Admissible.flowSigns', '''example {C} (h : Admissible C) : 0 ≤ C.a := by
  exact h.flowSigns.a_nonneg
''', ': 0 ≤ C.a :=', ': C.a ≤ 0 :=')
    add('Flow.coordinate_nonnegative', '''example {n C θ s u}
    (f : @KernelR.Family.Flow n C θ s u) (i : Fin n) (k : Coord)
    (initial : 0 ≤ s.x i k)
    (inward : ∀ t ∈ Icc s.time u.time, f.path t i k ≤ 0 →
      0 ≤ KernelR.Family.field C θ s (f.path t) t i k)
    {t} (ht : t ∈ Icc s.time u.time) : 0 ≤ f.path t i k := by
  exact f.coordinate_nonnegative i k initial inward ht
''', ': 0 ≤ f.path t i k :=', ': 0 < f.path t i k :=')
    add('pulse_nonnegative', '''example {C} (ha : 0 ≤ C.a) (origin t : ℝ) :
    0 ≤ KernelR.Family.pulse C origin t := by
  exact KernelR.Family.pulse_nonnegative ha origin t
''', '0 ≤ KernelR.Family.pulse C origin t :=', '0 < KernelR.Family.pulse C origin t :=')
    add('current_nonnegative', '''example {n C} (ha : 0 ≤ C.a) (s : Snapshot n)
    (i : Fin n) (p : Port) (t : ℝ) : 0 ≤ KernelR.Family.current C s i p t := by
  exact KernelR.Family.current_nonnegative ha s i p t
''', ': 0 ≤ KernelR.Family.current C s i p t :=', ': 0 < KernelR.Family.current C s i p t :=')
    add('Flow.aux_nonnegative', '''example {n C θ s u} (f : @KernelR.Family.Flow n C θ s u)
    (signs : FlowSigns C) (rest : 0 ≤ C.auxRest) (rates : RatesNonnegative θ)
    (i : Fin n) (p : Port) (input : 0 ≤ (θ i).inputGain p)
    (initial : 0 ≤ s.x i (.m p)) {t} (ht : t ∈ Icc s.time u.time) :
    0 ≤ f.path t i (.m p) := by
  exact f.aux_nonnegative signs rest rates i p input initial ht
''', '0 ≤ f.path t i (.m p) :=', '0 < f.path t i (.m p) :=')
    base = '''example {n C θ s u} (f : @KernelR.Family.Flow n C θ s u)
    (factor : 0 ≤ C.recoveryFactor) (rates : RatesNonnegative θ)
    (aux : ∀ t ∈ Icc s.time u.time, ∀ i p, 0 ≤ f.path t i (.m p))
    (i : Fin n) {t} (ht : t ∈ Icc s.time u.time)'''
    add('Flow.recovery_nondecreasing', base + ''' :
    s.x i .b ≤ f.path t i .b := by
  exact f.recovery_nondecreasing factor rates aux i ht
''', 's.x i .b ≤ f.path t i .b :=', 's.x i .b < f.path t i .b :=')
    add('Flow.recovery_nonnegative', base + ''' (initial : 0 ≤ s.x i .b) :
    0 ≤ f.path t i .b := by
  exact f.recovery_nonnegative factor rates aux i initial ht
''', '0 ≤ f.path t i .b :=', '0 < f.path t i .b :=')
    add('Flow.safe_of_initial_and_energy', '''example {n C θ s u}
    (f : @KernelR.Family.Flow n C θ s u)
    (signs : FlowSigns C) (rest : 0 ≤ C.auxRest) (rates : RatesNonnegative θ)
    (input : ∀ i p, 0 ≤ (θ i).inputGain p)
    (initialAux : ∀ i p, 0 ≤ s.x i (.m p))
    (initialRecovery : ∀ i, 0 ≤ s.x i .b)
    (energy : ∀ t ∈ Icc s.time u.time, ∀ i, 0 < f.path t i .energy)
    (i : Fin n) {t} (ht : t ∈ Icc s.time u.time) : 0 ≤ f.path t i .b := by
  exact (f.safe_of_initial_and_energy signs rest rates input initialAux initialRecovery energy t ht i).2.1
''', ': 0 ≤ f.path t i .b :=', ': 0 < f.path t i .b :=')
    add('Flow.coordinate_le_of_field_order', '''example {n C θ s u v}
    (f : @KernelR.Family.Flow n C θ s u) (g : KernelR.Family.Flow C θ s v)
    (i : Fin n) (k : Coord) {t}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time)
    (order : ∀ a ∈ Icc s.time t, g.path a i k ≤ f.path a i k →
      KernelR.Family.field C θ s (f.path a) a i k ≤
        KernelR.Family.field C θ s (g.path a) a i k) :
    f.path t i k ≤ g.path t i k := by
  exact f.coordinate_le_of_field_order g i k hf hg order
''', 'f.path t i k ≤ g.path t i k :=', 'f.path t i k < g.path t i k :=')

    common = '''example {n C θ s u v}
    (f : @KernelR.Family.Flow n C θ s u) (g : KernelR.Family.Flow C θ s v)
    (signs : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) (i : Fin n) (p : Port) {t}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time)'''
    for name, coord in [('aux_path_unique', '(.m p)'), ('gain_path_unique', '(.z p)'),
                        ('recovery_path_unique', '.b'), ('charge_path_unique', '.q'),
                        ('energy_path_unique', '.energy')]:
        if name == 'aux_path_unique':
            proof = 'f.aux_path_unique g signs rates i p hf hg'
        elif name == 'gain_path_unique':
            proof = 'f.gain_path_unique g signs rates safeF safeG i p hf hg'
        else:
            proof = f'f.{name} g signs rates safeF safeG i hf hg'
        add('Flow.' + name, common + f''' :
    f.path t i {coord} = g.path t i {coord} := by
  exact {proof}
''', f'= g.path t i {coord} :=', f'= g.path t i {coord} + 1 :=')
    add('Flow.path_unique', common + ''' : f.path t = g.path t := by
  exact f.path_unique g signs rates safeF safeG hf hg
''', ': f.path t = g.path t :=', ': f.path t ≠ g.path t :=')
    add('Flow.final_observational_unique', '''example {n C θ s u v}
    (f : @KernelR.Family.Flow n C θ s u) (g : KernelR.Family.Flow C θ s v)
    (signs : FlowSigns C) (rates : RatesNonnegative θ)
    (safeF : f.Safe) (safeG : g.Safe) (ht : u.time = v.time) (i : Fin n) :
    u.x i .q = v.x i .q := by
  exact congrFun (congrFun (f.final_observational_unique g signs rates safeF safeG ht).values i) .q
''', '= v.x i .q :=', '= v.x i .q + 1 :=')
    return out


def main():
    controls = cases()
    public = set(re.findall(r'^theorem\s+([^\s{(]+)',
                            (ROOT / 'KernelR/Family/FlowUniqueness.lean').read_text(), re.M))
    covered = {name for name, _, _ in controls}
    if public != covered:
        raise SystemExit(f'Flow coverage mismatch: missing={sorted(public-covered)}, '
                         f'stale={sorted(covered-public)}')
    with tempfile.TemporaryDirectory(prefix='family-flow-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp, root_module=MODULE)
        # Two compiler processes retain per-result pairing without paying the
        # Mathlib import/setup cost forty times. Every negative block must have
        # its own semantic diagnostic; a failure elsewhere cannot satisfy it.
        path.write_text(PREFIX + '\n'.join(good for _, good, _ in controls))
        positive = subprocess.run([*command, '--json', str(path)], cwd=ROOT, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  timeout=300)
        if positive.returncode != 0:
            raise SystemExit(f'Valid controls failed:\n{positive.stdout}')
        blocks = []
        text = PREFIX
        for name, _, bad in controls:
            first = len(text.splitlines()) + 1
            text += bad + '\n'
            blocks.append((name, first, len(text.splitlines())))
        path.write_text(text)
        negative = subprocess.run([*command, '--json', str(path)], cwd=ROOT, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  timeout=300)
        messages = []
        for line in negative.stdout.splitlines():
            try:
                message = json.loads(line)
            except json.JSONDecodeError:
                continue
            if message.get('severity') == 'error':
                messages.append(message)
        if negative.returncode == 0 or not messages:
            raise SystemExit(f'Altered controls were not rejected with Lean errors:\n{negative.stdout}')
        for message in messages:
            data = str(message.get('data', ''))
            if re.search(r'unknown (constant|identifier)|unexpected token|invalid syntax', data, re.I):
                raise SystemExit(f'Nonsemantic rejection:\n{negative.stdout}')
            line = message.get('pos', {}).get('line', -1)
            if not any(first <= line <= last for _, first, last in blocks):
                raise SystemExit(f'Diagnostic outside a paired block:\n{negative.stdout}')
        for name, first, last in blocks:
            if not any(first <= m.get('pos', {}).get('line', -1) <= last for m in messages):
                raise SystemExit(f'{name}: no semantic rejection for its altered claim:\n{negative.stdout}')
            print(f'{name}: valid conclusion accepted; false strengthening rejected.', flush=True)
    print(f'{len(controls)} paired parametric flow controls passed.', flush=True)


if __name__ == '__main__':
    main()
