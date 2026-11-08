#!/usr/bin/env python3
"""Reject altered physical return, memory-gate and residual-charge contracts."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridPulseSection
import KernelR.HybridPulseRoot
open KernelR.Hybrid
'''


def cases():
    slow = '''example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .slow) (hs : s.x i .q = 1/4)
    (hu : u.x i .q = 1/10) (hb : s.x i .b ≤ 11/10) : {delay} < u.time-s.time := by
  have h := e.slow_minimum_duration i hm hs hu hb
  linarith
'''
    dose = '''example {{n θ route s u i}} {{e : @Execution n θ route s u}}
    (pulse : LearnedPulse e i) (p : Port) : e.ledger.{kind} i p = {dose} := by
  have h := pulse.{kind}_zero p
  linarith
'''
    deadline = '''example {{n θ route s u i}} {{e : @Execution n θ route s u}}
    (ret : ReadyReturn e i) : ret.afterReturn.time < s.time+{bound} := by
  have h := ret.date
  linarith
'''
    equation = '''example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (tr : MainTrigger e i) (cycle : SensorCycle e i p) (hr : s.raw i p = some s.time)
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hn : ∀ q, NoArrivalAt e i q) :
    readyPulse {initial} (Real.exp (s.x i (.z p))) s.time tr.beforeFire.time = 1 := by
  exact tr.firing_equation cycle hr ho hn
'''
    reference = '''example {{initial amplitude start first rest : ℝ}}
    (hi : 1/10 ≤ initial) (ha : 9/5 ≤ amplitude)
    (hf : first ∈ Set.Icc start (start+9/10)) (hr : rest ∈ Set.Icc start (start+9/10))
    (hqf : readyPulse initial amplitude start first = 1)
    (hqr : readyPulse (1/10) amplitude start rest = 1) : {ordered} := by
  exact first_firing_le_rest_reference hi ha hf hr hqf hqr
'''
    prepared = '''example {{n θ ε route born s u i}} {{e : @Execution n θ route s u}}
    (tr : MainTrigger e i) (past : Execution θ route born s) (hborn : BirthState born)
    (hb : PhysicalBox θ ε) (hb₀ : {recovery} ≤ s.x i .b)
    (p : Port) (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hn : ∀ q, NoArrivalAt e i q) (ht : s.time+15/2 ≤ u.time) : Nonempty (ReadyReturn e i) := by
  exact tr.ready_return past hborn hb hb₀ p hr ho hn ht
'''
    return [
        ('SLOW minimum uses the actual recovery cap', slow.format(delay='4/5'), slow.format(delay='1')),
        ('learned ERROR gate is protected', dose.format(kind='error', dose='0'), dose.format(kind='error', dose='3/5')),
        ('MARK ends before main firing', dose.format(kind='mark', dose='0'), dose.format(kind='mark', dose='1/10')),
        ('physical READY return deadline', deadline.format(bound='6990787/1000000'), deadline.format(bound='69/10')),
        ('first firing retains initial charge', equation.format(initial='(s.x i .q)'), equation.format(initial='(1/10)')),
        ('positive residual advances the first firing', reference.format(ordered='first ≤ rest'), reference.format(ordered='rest ≤ first')),
        ('prepared recovery is needed for the return bound', prepared.format(recovery='17999/100000'), prepared.format(recovery='7999/100000')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-return-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp)

        def check(source, expected, name):
            path.write_text(PREFIX + source)
            result = subprocess.run([*command, str(path)], cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
            if (result.returncode == 0) != expected:
                raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
            if not expected and 'error:' not in result.stdout:
                raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')

        check('\n'.join(good for _, good, _ in controls), True, 'valid return controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
