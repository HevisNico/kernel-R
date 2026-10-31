#!/usr/bin/env python3
"""Check current physical bounds and positive learning exposure without a birth-history premise."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridProtectedPulse
import KernelR.HybridPhysicalInvariant
import KernelR.HybridSilentReturn
open KernelR.Hybrid
'''


def cases():
    reserve = """example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s) (i : Fin n) : {value} ≤ u.x i .energy := by
  have h := (e.physical_invariant hb hs).reserve i
  linarith
"""
    cap = """example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s) (i : Fin n) (p : Port) : {claim} := by
  exact (e.physical_invariant hb hs).gain_cap i p
"""
    silent = """example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : ReadyCoordinates s i)
    (hz : s.x i (.z p) ≤ Real.log (6/5) + 1/1000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hn : ∀ q, NoArrivalAt e i q) (ht : s.time + 15/2 ≤ u.time) : e.ledger.error i p = {value} := by
  obtain ⟨pulse⟩ := e.silent_pulse_of_invariant hb hf hv i p hs hz hr ho hn ht
  have h := pulse.error_dose
  linarith
"""
    protected = """example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : MarkEntry s i)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hn : ∀ q, NoArrivalAt e i q) (ht : s.time + 15/2 ≤ u.time) : {claim} := by
  obtain ⟨pulse⟩ := e.protected_pulse_of_invariant hb hf hv i p hs hr ho hn ht
  have h := pulse.{field}
  linarith
"""
    strong = """example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : ReadyCoordinates s i)
    (hb₀ : 7999/100000 ≤ s.x i .b ∧ s.x i .b ≤ 8001/100000)
    (hz : 9/5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12/5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hn : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 15/2 ≤ u.time ∧ u.time ≤ s.time + 17/2) : (e.emissionTimes i).length = {value} := by
  obtain ⟨pulse⟩ := e.first_strong_low_recovery_of_valid hb hi hv i p hs hb₀ hz hr ho hn ht
  rw [pulse.emissions]
  norm_num
"""
    return [
        ('current physical bounds preserve reserve', reserve.format(value='50'), reserve.format(value='60')),
        ('cap contact is retained in the invariant', cap.format(claim='u.x i (.z p) ≤ Real.log ((θ i).cap p)'), cap.format(claim='u.x i (.z p) < Real.log ((θ i).cap p)')),
        ('current reserve opens silent ERROR exposure', silent.format(value='3/5'), silent.format(value='0')),
        ('current reserve opens protected MARK exposure', protected.format(claim='e.ledger.mark i p = 1/10',field='mark_dose'), protected.format(claim='e.ledger.mark i p = 0',field='mark_dose')),
        ('protected recovery increases by one dose', protected.format(claim='u.x i .b = s.x i .b + 1/10',field='recovery_gain'), protected.format(claim='u.x i .b = s.x i .b + 1/5',field='recovery_gain')),
        ('current low-recovery coordinates derive first output', strong.format(value='1'), strong.format(value='0')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-invariant-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid invariant controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
