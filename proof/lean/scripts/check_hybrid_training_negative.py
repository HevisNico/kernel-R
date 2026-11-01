#!/usr/bin/env python3
"""Reject unsupported training input bounds, silent resets and early returns."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridSilentReturn
import KernelR.HybridMidGainInput
open KernelR.Hybrid
'''


def cases():
    response = '''example {{t : ℝ}} (ht : 0 ≤ t) : response t ≤ {bound} := by
  have h := response_uniform_upper ht
  linarith
'''
    overlap = '''example {{z : ℝ}} (hz : z ≤ Real.log (6/5)+1/1000+11/125) :
    Real.exp z ≤ {gain} := by
  have h := fast_nominal_raw_gain_upper hz
  linarith
'''
    dose = '''example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (pulse : SilentPulse e i p) : e.ledger.error i p = {dose} := by
  have h := pulse.error_dose
  linarith
'''
    charge = '''example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (pulse : SilentPulse e i p) : {charge} := by
  exact pulse.coordinates.charge.2
'''
    mid = '''example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port) (hm : s.main i = .ready)
    (hq : 1/10-1/100000 ≤ s.x i .q ∧ s.x i .q ≤ 7/50)
    (hz : 9/5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ {gain})
    (ha : s.aux i p = .ready) (hr : s.raw i p = some s.time) (hx : RestBand (s.x i (.m p)))
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hn : ∀ q, NoArrivalAt e i q)
    (ht : s.time+419/300 ≤ u.time) : Nonempty (MainTrigger e i) := by
  exact e.mid_gain_input_trigger hb hi i p hm hq hz ha hr hx ho hn ht
'''
    recovery = '''example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hm : e.AllStates (fun v => v.main i = .ready))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hn : ∀ q, NoArrivalAt e i q) (ht : s.time+{gap} ≤ u.time) : u.x i .q ≤ 7/50 := by
  exact (e.silent_charge_return hb hi i p hm hr ho hn ht).1
'''
    return [
        ('uniform real response bound', response.format(bound='16/25'), response.format(bound='1/2')),
        ('raw ERROR overlap is retained', overlap.format(gain='4/3'), overlap.format(gain='6/5')),
        ('nominal silent input receives ERROR', dose.format(dose='3/5'), dose.format(dose='0')),
        ('silent relaxation is not a state reset', charge.format(charge='u.x i .q ≤ 7/50'), charge.format(charge='u.x i .q = 1/10')),
        ('first-firing lower bracket needs the gain bound', mid.format(gain='12/5'), mid.format(gain='3')),
        ('silent recovery needs the input gap', recovery.format(gap='15/2'), recovery.format(gap='2')),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-training-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid training controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
