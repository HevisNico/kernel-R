#!/usr/bin/env python3
"""Check actual sensor-phase extraction and reject changed physical contracts."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridSensor
import KernelR.HybridEnvelope
import KernelR.HybridInputs
open KernelR.Hybrid
'''


def main():
    trigger = '''example {{n θ ε route s u}} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hs : s.aux i p = .ready) (hr : s.raw i p = {raw})
    (hx : 1/40-1/100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1/40+1/100000)
    (ht : s.time + 419/300 ≤ u.time) : Nonempty (SensorCycle e i p) := by
  exact e.sensor_cycle hb hi i p hs hr hx ht
'''
    late = '''example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (cycle : SensorCycle e i p) : s.time + {delay} < cycle.phases.silentPhase.afterExit.time := by
  have h := cycle.error_starts_late
  linarith
'''
    finish = '''example {{n θ route s u i p}} {{e : @Execution n θ route s u}}
    (cycle : SensorCycle e i p) : cycle.phases.errorPhase.afterExit.time < s.time + {deadline} := by
  have h := cycle.ready_deadline
  linarith
'''
    duration = '''example {{n θ ε}} (hb : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    auxCycleDuration (θ i) p ≤ {bound} := by
  have h := hb.aux_cycle_duration_upper i p
  linarith
'''
    envelope = '''example {{n θ ε s u}} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (hm : s.main i = .ready)
    (hc : ∀ p, s.x i (.z p) ≤ Real.log ((θ i).cap p))
    (t : ℝ) (ht : t ∈ Set.Icc s.time u.time) :
    f.path t i .q ≤ readyPulse (s.x i .q) (rawAmplitude s i {gains}) s.time t := by
  exact (f.ready_physical_envelope hb i hm hc t ht).2
'''
    clipping = '''example {{n θ ε s u}} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hm : s.aux i p = .error) :
    u.x i (.z p) - s.x i (.z p) ≤ {factor} * (s.x i (.m p) - u.x i (.m p)) := by
  have h := f.error_gain_budget hb i p hm
  linarith
'''
    expired = '''example {{n θ route s u}} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ) (hs : RawValid s) (hr : s.raw i p = some origin)
    (hn : NoArrivalAt e i p) (ht : origin + 1 < u.time) : u.raw i p = {raw} := by
  exact e.raw_expired_of_no_arrival i p origin hs hr hn ht
'''
    provenance = '''example {{n θ route s u}} (e : @Execution n θ route s u)
    (d : Delivery n) (hd : d ∈ e.deliveries) : {origin} := by
  exact e.delivery_provenance d hd
'''
    cases = [
        ('sensor cycle requires a received pulse', trigger.format(raw='some s.time'), trigger.format(raw='none')),
        ('late ERROR starts', late.format(delay='99/100'), late.format(delay='1')),
        ('sensor completion deadline', finish.format(deadline='419/300'), finish.format(deadline='5/4')),
        ('independent physical cycle rates', duration.format(bound='41/30'), duration.format(bound='5/4')),
        ('variable gain cannot be silently frozen', envelope.format(gains='(θ i).cap'),
         envelope.format(gains='(fun p => Real.exp (s.x i (.z p)))')),
        ('charge-limited clipped ERROR', clipping.format(factor='8'), clipping.format(factor='7')),
        ('expired raw current without a new arrival', expired.format(raw='none'), expired.format(raw='some origin')),
        ('delivered token provenance',
         provenance.format(origin='d ∈ s.pending ∨ ∃ ev ∈ e.ledger.emissions, d ∈ route ev.1 ev.2'),
         provenance.format(origin='d ∈ s.pending')),
    ]
    with tempfile.TemporaryDirectory(prefix='hybrid-phase-negative-', dir=ROOT) as tmp:
        path = Path(tmp) / 'Check.lean'
        command = lean_check_command(tmp)
        for name, good, bad in cases:
            for expected, source in [(True, good), (False, bad)]:
                path.write_text(PREFIX + source)
                result = subprocess.run([*command, str(path)], cwd=ROOT,
                                        text=True, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, timeout=120)
                if (result.returncode == 0) != expected:
                    raise SystemExit(f'{name}: unexpected result:\n{result.stdout}')
                if not expected and 'error:' not in result.stdout:
                    raise SystemExit(f'{name}: failed without a Lean diagnostic:\n{result.stdout}')
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
