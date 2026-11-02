#!/usr/bin/env python3
"""Paired contracts for a cadence FIRE with genuine carried READY charge."""
from pathlib import Path
import subprocess
import tempfile

from lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import KernelR.HybridCadenceFirstStrongFireExistence
open KernelR.Hybrid
'''


def pair(label, template, good, bad):
    assert '@v@' in template
    assert good != bad
    return label, template.replace('@v@', good), template.replace('@v@', bad)


def cases():
    fire = '''example {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
    (f : FirstLearnedFire θ (fun _ _ => []) s 0 p) '''
    ready = '''(hs : CadenceReadyCoordinates s 0 (3/10))
    (hg : Real.exp (s.x 0 (.z p)) ≤ 19/10) '''
    isolated = '''(hs : CadenceReadyCoordinates s 0 (3/10))
    (ho : ∀ q, q ≠ p → s.raw 0 q=none)
    (hp : ∀ d∈s.pending, s.time+4≤d.due) '''
    fast = fire + '''(b : PortFastCompletion θ (fun _ _ => []) f.final p) '''
    factory = '''example {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (3/10))
    (hg : 9/5≤Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p))≤19/10)
    (hr : s.raw 0 p=some s.time) (ho : ∀ q,q≠p→s.raw 0 q=none)
    (hp : ∀ d∈s.pending,s.time+4≤d.due) :
    ∃ f : FirstLearnedFire θ (fun _ _ => []) s 0 p,
      s.time+2/5<f.final.time ∧ f.final.time<s.time+9/10 ∧
      (f.execution.emissionTimes 0).length=@v@ ∧
      Nonempty (PortFastCompletion θ (fun _ _ => []) f.final p) := by
  obtain ⟨f⟩ := cadence_first_strong_fire_exists hb s p hf hv hs hg hr ho hp
  have hw := f.cadence_residual_window hs hg.2
  exact ⟨f,hw.1,hw.2,f.cadence_residual_emission_count,
    f.cadence_residual_fast_completion_exists hb hs hg.2 ho hp⟩
'''
    return [
        pair('scalar carried-charge envelope stays strictly below threshold through four tenths',
             '''example {q G S T : ℝ} (hq : q≤3/10) (hG : G≤19/10)
    (hl : S≤T) (hu : T≤S+2/5) : readyPulse q G S T≤@v@ := by
  exact (readyPulse_cadence_residual_four_tenths_margin hq hG hl hu).1
''', '499/500', '9/10'),
        pair('scalar response root retains carried charge and crosses after four tenths',
             '''example {q G S T : ℝ} (hq : q≤3/10) (hG : G≤19/10)
    (hl : S≤T) (hr : readyPulse q G S T=1) : S+@v@<T := by
  exact readyPulse_cadence_residual_root_after_four_tenths hq hG hl hr
''', '2/5', '1/2'),
        pair('constructive factory needs no reaching execution and produces one real output',
             factory, '1', '0'),
        pair('physical first FIRE lies in the true residual response window', fire + ready +
             ': s.time+@v@<f.final.time ∧ f.final.time<s.time+9/10 := by exact f.cadence_residual_window hs hg\n',
             '2/5', '1/2'),
        pair('actual threshold equation uses the carried source charge', fire +
             ': readyPulse @v@ (Real.exp (s.x 0 (.z p))) s.time (s.time+f.latency)=1 := by exact f.response_root\n',
             '(s.x 0 .q)', '(1/10)'),
        pair('main threshold reaches one before the actual FAST departure', fire +
             ': f.final.x 0 .q=@v@ := by exact f.charge\n', '1', '1/10'),
        pair('actual FIRE retains FAST mode rather than resetting READY', fire +
             ': f.final.main 0=.@v@ := by exact f.main_fast\n', 'fast', 'ready'),
        pair('active sensor remains genuinely SILENT at FIRE', fire +
             ': f.final.aux 0 p=.@v@ := by exact f.aux_silent\n', 'silent', 'error'),
        pair('first strong FIRE contributes exactly one emitted event', fire +
             ': (f.execution.emissionTimes 0).length=@v@ := by exact f.cadence_residual_emission_count\n', '1', '2'),
        pair('own gains remain unchanged before ERROR can be exposed', fire +
             '(q : Port) : f.final.x 0 (.z q)=s.x 0 (.z q)@v@ := by exact f.gain_preserved 0 q\n',
             '', '+3/5'),
        pair('own prepared recovery is retained through the first FIRE', fire +
             ': f.final.x 0 .b=s.x 0 .b@v@ := by exact f.recovery_preserved 0\n', '', '+1/10'),
        pair('first strong FIRE retains every later own source', fire +
             ': f.final.pending=@v@ := by simpa only [List.append_nil] using f.pending\n', 's.pending', '[]'),
        pair('fresh RAW still has its actual source origin at FIRE', fire +
             ': f.final.raw 0 p=@v@ := by exact f.raw_active\n', 'some s.time', 'none'),
        pair('first strong threshold path introduces no ERROR dose', fire +
             '(q : Port) : f.execution.ledger.error 0 q=@v@ := by exact f.cadence_residual_error_zero q\n', '0', '3/5'),
        pair('first strong threshold path introduces no protected MARK dose', fire + isolated +
             '(q : Port) : f.execution.ledger.mark 0 q=@v@ := by exact f.cadence_residual_mark_zero hs ho q\n',
             '0', '1/10'),
        pair('FIRE endpoint is saturated at its own actual clock', fire + isolated +
             ': CompleteThrough f.execution @v@ := by exact f.cadence_residual_complete hs ho hp\n',
             'f.final.time', '(s.time+9/10)'),
        pair('FAST exit is one time unit after the actual firing', fast +
             ': b.final.time=@v@+1 := by exact b.date\n', 'f.final.time', 's.time'),
        pair('FAST exit retains the actual SLOW phase', fast +
             ': b.final.main 0=.@v@ := by exact b.main_slow\n', 'slow', 'ready'),
        pair('FAST exit charge is its genuine one-quarter guard', fast +
             ': b.final.x 0 .q=@v@ := by exact b.charge\n', '1/4', '1/10'),
        pair('FAST completion physically expires the source RAW', fast +
             '(q : Port) : b.final.raw 0 q=@v@ := by exact b.raw_none 0 q\n', 'none', 'some s.time'),
        pair('FAST completion retains its exact later source queue', fast +
             ': b.final.pending=@v@ := by exact b.pending\n', 'f.final.pending', '[]'),
        pair('FAST completion keeps the same own acquired gain', fast +
             '(q : Port) : b.final.x 0 (.z q)=f.final.x 0 (.z q)@v@ := by exact b.gains 0 q\n',
             '', '+3/5'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-cadence-first-strong-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid cadence first strong controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)
        print(f'{len(controls)} paired cadence first strong controls passed.', flush=True)


if __name__ == '__main__':
    main()
