#!/usr/bin/env python3
"""Check prepared cases from current physical invariants, retaining birth corollaries."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridCellSources
import KernelR.HybridCellPreparedTrain
open KernelR.Hybrid
'''


def cases():
    pulse_header = """example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : PreparedSection s i)
    (hz : 9/5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12/5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hn : ∀ q, NoArrivalAt e i q) (ht : s.time + 15/2 ≤ u.time) : {claim} := by
"""
    pulse = pulse_header + """  exact e.learned_mid_pulse_of_valid hb hi hv i p hs hz hr ho hn ht
"""
    gain = pulse_header + """  obtain ⟨pulse⟩ := e.learned_mid_pulse_of_valid hb hi hv i p hs hz hr ho hn ht
  have h := pulse.gain_preserved p
  linarith
"""
    train = """example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (i : Fin n) (p : Port) (times : List ℝ) (hs : PreparedSection s i)
    (hz : 9/5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12/5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hcal : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (hspace : (s.time :: times).Pairwise (fun t v => t + 15/2 ≤ v))
    (hquiet : ∀ t ∈ s.time :: times, t + 15/2 ≤ u.time) :
    Nonempty (PreparedTrain e i (times.length + {count})) := by
  exact prepared_cell_train_of_valid hb i p times e hi hv hs hz hr ho hcal hspace hquiet
"""
    emission = """example {{n θ route s u i}} {{e : @Execution n θ route s u}}
    (tr : MainTrigger e i) (hv : RawValid s) (p : Port)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hn : ∀ q, NoArrivalAt e i q) : e.emissionTimes i = {value} := by
  exact tr.only_emission_of_valid hv p hr ho hn
"""
    return [
        ('local invariants derive a learned input case', pulse.format(claim='Nonempty (LearnedPulse e i)'), pulse.format(claim='Nonempty (ProtectedPulse e i p)')),
        ('local prepared case preserves receiving gain', gain.format(claim='u.x i (.z p) = s.x i (.z p)'), gain.format(claim='u.x i (.z p) = s.x i (.z p) + 3/5')),
        ('local invariants count a variable-gap cell train', train.format(count='1'), train.format(count='2')),
        ('raw validity suffices for the single-emission tail', emission.format(value='[tr.beforeFire.time]'), emission.format(value='[]')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-local-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid local controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
