#!/usr/bin/env python3
"""A real protected MARK return supports an actual next input at any gap at least3.8."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridCadenceMarkOnlyJitterNextSource
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    state = """example {θ s p H later}
    (r : CadenceMarkOnlyJitterNextSource θ s p H later) """
    factory = """example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1)
    (p : Port) (later : List (Delivery 1))
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0=.slow)
    (hq : 37/250≤s.x 0 .q ∧ s.x 0 .q≤1/4)
    (hbown : 17999/100000≤s.x 0 .b ∧ s.x 0 .b≤18001/100000)
    (ha : ∀ q,s.aux 0 q=.ready ∧ RestBand (s.x 0 (.m q)))
    (hr : s.raw 0 p=some s.time) (ho : ∀ q,q≠p → s.raw 0 q=none)
    (hqueue : s.pending=⟨0,p,s.time+19/5⟩::later)
    (hLater : ∀ d∈later,s.time+19/5<d.due) :
    ∃ r : CadenceMarkOnlyJitterNextSource θ s p (s.time+19/5) later,
      r.final.time=s.time+@v@ := by
  obtain ⟨r⟩ := cadence_mark_only_jitter_next_source_exists hb s p (s.time+19/5) later
    hf hv hm hq hbown ha hr ho hqueue (by linarith) hLater
  exact ⟨r,r.date⟩
"""
    return [
        pair('the factory accepts the exact lower gap3.8 without a nominal four-gap premise',
             factory, '19/5', '4'),
        pair('actual next-source origin is H rather than the previous pulse date', state+
             ': r.final.raw 0 p=@v@ := by exact r.raw_active\n', 'some H', 'some s.time'),
        pair('the actual arrival removes precisely the head source occurrence', state+
             ': r.final.pending=@v@ := by exact r.pending\n', 'later', 's.pending'),
        pair('the protected input retains each own gain without an ERROR dose', state+
             '(q : Port) : r.final.x 0 (.z q)=s.x 0 (.z q)@v@ := by exact r.gains 0 q\n', '', '+3/5'),
        pair('the own recovery increment is one finite MARK dose', state+
             ': r.final.x 0 .b=s.x 0 .b+@v@ := by exact r.recovery_gain\n', '1/10', '1/5'),
        pair('the receiving port has the actual full MARK ledger', state+
             ': r.execution.ledger.mark 0 p=@v@ := by exact r.mark_target\n', '1/10', '0'),
        pair('no hidden ERROR is added while the protected sensor finishes', state+
             '(q : Port) : r.execution.ledger.error 0 q=@v@ := by exact r.error_zero q\n', '0', '3/5'),
        pair('the actual MARK-only input does not emit a pulse', state+
             ': r.execution.ledger.emissions=@v@ := by exact r.emissions\n', '[]', '[(0,H)]'),
        pair('the real next delivery uses H instead of the old nominal endpoint', state+
             ': r.execution.deliveries=[⟨0,p,@v@⟩] := by exact r.deliveries\n', 'H', 's.time+4'),
        pair('the energy endpoint keeps the real returnState quiet solution at H', state+
             ': r.final.x 0 .energy=@v@ := by exact congrFun (congrFun r.values 0) .energy\n',
             '(quietAt r.response.returnState H).x 0 .energy', '100'),
        pair('queue framing retains the complete real MARK ledger', state+
             ': r.framed.ledger=@v@ := by exact r.framed_ledger\n', 'r.offline.ledger', 'Ledger.zero'),
        pair('terminal saturation is at the real next-source horizon', state+
             ': CompleteThrough r.execution @v@ := by exact r.complete\n', 'H', 'H+1'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-mark-only-jitter-next-source-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid MARK-only jitter controls')
        print(f'All {len(controls)} positive MARK-only jitter contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: valid conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired MARK-only jitter controls passed.', flush=True)


if __name__ == '__main__':
    main()
