#!/usr/bin/env python3
"""Paired variable-gap mixed MARK/ERROR response and actual next-source controls."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridCadenceMixedJitterNextSource
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    state = """example {θ s p H later}
    (r : CadenceMixedJitterNextSource θ s p H later) """
    factory = """example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1)
    (p : Port) (later : List (Delivery 1))
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0=.slow)
    (hq : 61/500≤s.x 0 .q ∧ s.x 0 .q≤7/50)
    (hB : 27999/100000≤s.x 0 .b ∧ s.x 0 .b≤28001/100000)
    (ha : ∀ q,s.aux 0 q=.ready ∧ RestBand (s.x 0 (.m q)))
    (hz : Real.log (3/10)+9/5-1/100000≤s.x 0 (.z p) ∧
      s.x 0 (.z p)≤Real.log (3/10)+9/5+1/100000)
    (hr : s.raw 0 p=some s.time) (ho : ∀ q,q≠p → s.raw 0 q=none)
    (hqueue : s.pending=⟨0,p,s.time+19/5⟩::later)
    (hLater : ∀ d∈later,s.time+19/5<d.due) :
    ∃ r : CadenceMixedJitterNextSource θ s p (s.time+19/5) later,
      r.final.time=s.time+@v@ ∧ CompleteThrough r.execution (s.time+19/5) ∧
      r.final.pending=later ∧
      (16/5≤Real.exp (r.final.x 0 (.z p)) ∧ Real.exp (r.final.x 0 (.z p))≤7/2) := by
  obtain ⟨r⟩ := cadence_mixed_jitter_next_source_exists hb s p (s.time+19/5) later
    hf hv hm hq hB ha hz hr ho hqueue (by linarith) hLater
  exact ⟨r,r.date,r.complete,r.pending,r.high_gain⟩
"""
    return [
        pair('the real mixed return serves the exact lower gap3.8 with a high-gain source and full queue',
             factory, '19/5', '4'),
        pair('the charge is the carried ERROR-end relaxation rather than an exact-rest reset', state+
             ': r.final.x 0 .q=@v@ := by exact congrFun (congrFun r.values 0) .q\n',
             '(quietAt r.mixed.errorEnd.final H).x 0 .q', '1/10'),
        pair('the actual positive residual retains its high-input cap', state+
             ': r.final.x 0 .q≤@v@ := by exact r.coordinates.charge.2\n', '8/25', '1/10'),
        pair('the next pulse RAW origin is the actual H instead of the previous input', state+
             ': r.final.raw 0 p=@v@ := by exact r.raw_active\n', 'some H', 'some s.time'),
        pair('the active own log-gain receives the real mixed ERROR dose', state+
             ': r.final.x 0 (.z p)=s.x 0 (.z p)+@v@ := by exact r.gain_target\n', '3/5', '0'),
        pair('other own gains are retained without collateral learning', state+
             '(q : Port) (hq : q≠p) : r.final.x 0 (.z q)=s.x 0 (.z q)@v@ := by exact r.gain_other q hq\n', '', '+3/5'),
        pair('the own recovery gains one finite protected MARK dose', state+
             ': r.final.x 0 .b=s.x 0 .b+@v@ := by exact r.recovery_gain\n', '1/10', '1/5'),
        pair('the actual ERROR ledger retains the full mixed dose', state+
             ': r.execution.ledger.error 0 p=@v@ := by exact r.error_target\n', '3/5', '0'),
        pair('the actual MARK ledger is not lost during the ERROR-end cut', state+
             ': r.execution.ledger.mark 0 p=@v@ := by exact r.mark_target\n', '1/10', '0'),
        pair('the mixed input adds no fictitious FIRE', state+
             ': r.execution.ledger.emissions=@v@ := by exact r.emissions\n', '[]', '[(0,H)]'),
        pair('the energy keeps the actual ERROR-end forced solution and quiet continuation', state+
             ': r.final.x 0 .energy=@v@ := by exact congrFun (congrFun r.values 0) .energy\n',
             '(quietAt r.mixed.errorEnd.final H).x 0 .energy', '100'),
        pair('the next actual delivery remains at H rather than a nominal four-unit date', state+
             ': r.execution.deliveries=[⟨0,p,@v@⟩] := by exact r.deliveries\n', 'H', 's.time+4'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-mixed-jitter-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid mixed-jitter controls')
        print(f'All {len(controls)} positive mixed-jitter contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: valid conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired mixed-jitter controls passed.', flush=True)


if __name__ == '__main__':
    main()
