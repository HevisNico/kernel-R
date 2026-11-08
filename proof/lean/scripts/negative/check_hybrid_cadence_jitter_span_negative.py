#!/usr/bin/env python3
"""Paired exact-rest strong-to-mixed physical bounds at variable wire gaps."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = '''import KernelR.HybridCadenceSecondStrongJitterSpan
open KernelR.Hybrid
noncomputable section
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    scalar = '''example {B S latency time : ℝ}
    (hB : 27999/100000≤B ∧ B≤28001/100000)
    (hlat : 13/20<latency ∧ latency<33/50)
    (ht : S+latency+1≤time) (hu : time≤S+21/5) '''
    span = '''example {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
    {fire : FirstLearnedFire θ (fun _ _=>[]) s 0 p}
    {fast : PortFastCompletion θ (fun _ _=>[]) fire.final p} {T : ℝ}
    (r : CadenceSecondStrongJitterSpan fast T) '''
    factory = '''example {θ ε} {s : Snapshot 1} {p : Port}
    (fire : FirstLearnedFire θ (fun _ _=>[]) s 0 p) (hb : PhysicalBox θ ε)
    (fast : PortFastCompletion θ (fun _ _=>[]) fire.final p) (T : ℝ)
    (hgap : s.time+19/5≤T ∧ T≤s.time+21/5) (hq : s.x 0 .q=1/10)
    (hz : Real.log (3/10)+9/5-1/100000≤s.x 0 (.z p) ∧
      s.x 0 (.z p)≤Real.log (3/10)+9/5+1/100000)
    (hB : 27999/100000≤s.x 0 .b ∧ s.x 0 .b≤28001/100000)
    (hp : ∀ d∈s.pending,T≤d.due) :
    ∃ r : CadenceSecondStrongJitterSpan fast T,
      r.final.time=T ∧ @v@≤r.final.x 0 .q ∧ r.final.x 0 .q≤7/50 := by
  obtain ⟨r⟩ := fire.cadence_second_strong_jitter_span_exists hb fast T hgap hq hz hB hp
  exact ⟨r,r.date,r.charge⟩
'''
    return [
        pair('the variable-gap factory constructs the real SLOW endpoint in the existing mixed domain',
             factory, '61/500', '1/4'),
        pair('the actual own latency preserves the mixed lower charge through gap4.2', scalar +
             ': @v@<(1/4:ℝ)*Real.exp (-B*(time-(S+latency+1))) := by exact (cadence_second_strong_jitter_charge_bounds hB hlat ht hu).1\n',
             '61/500', '1/8'),
        pair('the protected SLOW charge cannot exceed its true FAST exit value', scalar +
             ': (1/4:ℝ)*Real.exp (-B*(time-(S+latency+1)))≤@v@ := by exact (cadence_second_strong_jitter_charge_bounds hB hlat ht hu).2\n',
             '1/4', '7/50'),
        pair('variable receipt time is retained instead of forced back to exactly four', span +
             ': r.final.time=@v@ := by exact r.date\n', 'T', 's.time+4'),
        pair('the variable endpoint keeps the actual SLOW mode', span +
             ': r.final.main 0=.@v@ := by exact r.main_slow\n', 'slow', 'ready'),
        pair('the actual mixed-entry charge retains its verified lower band', span +
             ': @v@≤r.final.x 0 .q := by exact r.charge.1\n', '61/500', '1/4'),
        pair('the actual mixed-entry charge retains its verified upper band', span +
             ': r.final.x 0 .q≤@v@ := by exact r.charge.2\n', '7/50', '61/500'),
        pair('the SLOW extension performs no fictitious new FIRE', span +
             ': r.execution.ledger.emissions=@v@ := by exact r.emissions\n', '[]', '[(0,T)]'),
        pair('the due source is left for its real subsequent arrival', span +
             ': r.execution.deliveries=@v@ := by exact r.deliveries\n', '[]', '[⟨0,p,T⟩]'),
        pair('the exact future queue remains available for suffix framing', span +
             ': r.final.pending=@v@ := by exact r.pending\n', 'fast.final.pending', '[]'),
        pair('the actual input RAW is expired at the mixed-entry section', span +
             '(q : Port) : r.final.raw 0 q=@v@ := by exact r.raw_none 0 q\n', 'none', 'some s.time'),
        pair('the variable-gap energy is the same protected-flow solution at T', span +
             ': r.final.x 0 .energy=@v@ := by exact r.energy_clock\n',
             'protectedMainValues θ fast.final 0 p .slow .ready none T 0 .energy', '100'),
        pair('the variable extension preserves every own acquired gain', span +
             '(q : Port) : r.final.x 0 (.z q)=fast.final.x 0 (.z q)@v@ := by exact r.gains 0 q\n', '', '+3/5'),
        pair('the variable extension preserves the own acquired recovery', span +
             ': r.final.x 0 .b=fast.final.x 0 .b@v@ := by exact r.recovery 0\n', '', '+1/10'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-jitter-span-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid jitter-span controls')
        print(f'All {len(controls)} positive jitter-span contracts accepted.', flush=True)
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: valid conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired jitter-span controls passed.', flush=True)


if __name__ == '__main__':
    main()
