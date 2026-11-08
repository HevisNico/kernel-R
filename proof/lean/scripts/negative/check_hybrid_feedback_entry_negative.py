#!/usr/bin/env python3
"""Check actual reciprocal weak sources, residual first FIRE and closed products."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = ('import KernelR.HybridFeedbackFirstFire\n'
          'import KernelR.HybridIntervalClosedExecutionProduct\nopen KernelR.Hybrid\n')


def cases():
    weak = 'example {θ route start} (w : FeedbackWeakEntry θ route start) '
    fire = '''example {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    (f : FeedbackFirstFire w) '''
    factory = '''example {θ ε route} (hb : @PhysicalBox 2 θ ε)
    (start : Snapshot 2) (hf : PhysicalInvariant θ start) (hv : RawValid start)
    (hs : ∀ i, PreparedSection start i) (hq : ∀ i, start.x i .q=1/10)
    (hr : ∀ i p, start.raw i p=none) (ht : start.time=3199/10)
    (hp : start.pending=sourceTrain 1 2 320 8 16++sourceTrain 1 2 480 8 16)
    (hz : start.x 1 (.z 2)≤Real.log (3/10)+1/100000) :
    ∃ w : FeedbackWeakEntry θ route start, w.final.time=@v@ := by
  obtain ⟨w⟩ := feedback_weak_entry_exists (route := route) hb start hf hv hs hq hr ht hp hz
  exact ⟨w,w.date⟩
'''
    first_factory = '''example {θ ε forward backward start}
    (w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start)
    (hb : @PhysicalBox 2 θ ε)
    (hz : Real.log (3/10)-1/100000≤start.x 1 (.z 2) ∧
      start.x 1 (.z 2)≤Real.log (3/10)+1/100000) :
    ∃ f : FeedbackFirstFire w, f.final.pending.length=@v@ := by
  obtain ⟨f⟩ := w.first_fire_exists hb hz
  exact ⟨f,f.pending_length⟩
'''
    left_product = '''example {θA θB : Fin 1 → Parameters} {routeB : Router 1}
    {sA uA sB uB : Snapshot 1} (a : Execution θA (fun _ _ => []) sA uA)
    (b : Execution θB routeB sB uB) (hs : sA.time=sB.time) (hu : uA.time=uB.time)
    (hdA : a.deliveries=[]) (heB : b.ledger.emissions=[]) (hdB : b.deliveries=[])
    (Q : List (Delivery 2)) (hq : ∀ d∈Q, uA.time≤d.due) (route : Router 2)
    (hc : ∀ t, sA.time≤t → t≤uA.time → route 0 t=[]) :
    ∃ e : Execution (extendParameters θA (θB 0)) route (sA.product sB Q) (uA.product uB Q),
      e.ledger.emissions=@v@ ∧ e.deliveries=[] := by
  exact a.product_left_closed_on b hs hu hdA heB hdB Q hq route hc
'''
    right_product = '''example {θA θB : Fin 1 → Parameters} {routeA : Router 1}
    {sA uA sB uB : Snapshot 1} (a : Execution θA routeA sA uA)
    (b : Execution θB (fun _ _ => []) sB uB) (hs : sA.time=sB.time) (hu : uA.time=uB.time)
    (heA : a.ledger.emissions=[]) (hdA : a.deliveries=[]) (hdB : b.deliveries=[])
    (Q : List (Delivery 2)) (hq : ∀ d∈Q, uA.time≤d.due) (route : Router 2)
    (hc : ∀ t, sB.time≤t → t≤uB.time → route 1 t=[]) :
    ∃ e : Execution (extendParameters θA (θB 0)) route (sA.product sB Q) (uA.product uB Q),
      e.ledger.emissions=@v@ ∧ e.deliveries=[] := by
  exact a.product_right_closed_on b hs hu heA hdA hdB Q hq route hc
'''
    staged = '''example {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {v : SecondWiredArrival s}
    {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
    {t : ThirdWiredArrival u} {x : FirstCoupledPreparedPair t} (z : FirstCoupledTeaching x)
    {w : FeedbackWeakEntry (extendParameters θ fresh) (reciprocalEntryRouter forward backward) z.final}
    (a : FeedbackFirstFire w) {ε} (hb : PhysicalBox θ ε) '''

    def pair(label, template, good, bad):
        assert '@v@' in template
        return label, template.replace('@v@', good), template.replace('@v@', bad)

    return [
        pair('current319.9 state constructs fresh B344 without a reaching trace', factory, '344', '352'),
        pair('real weak prefix terminates at344', weak + ': w.final.time=@v@ := by exact w.date\n', '344', '336'),
        pair('four actual external B arrivals are retained', weak +
             ': w.execution.deliveries=sourceTrain 1 2 320 8 @v@ := by exact w.deliveries\n', '4', '3'),
        pair('weak prefix has no actual FIRE', weak +
             ': w.execution.ledger.emissions=@v@ := by exact w.emissions\n', '[]', '[(1,344)]'),
        pair('only twelve first-train sources remain', weak +
             ': w.final.pending=sourceTrain 1 2 352 8 @v@++sourceTrain 1 2 480 8 16 := by exact w.pending\n', '12', '13'),
        pair('future source queue contains28 actual occurrences', weak +
             ': w.final.pending.length=@v@ := by exact w.pending_length\n', '28', '27'),
        pair('B344 RAW is fresh on port2', weak +
             ': w.final.raw 1 @v@=some w.final.time := by exact w.raw_active\n', '2', '1'),
        pair('B retains at least resting charge rather than a supplied reset', weak +
             ': 1/10 @v@ w.final.x 1 .q := by exact w.b_charge\n', '≤', '='),
        pair('A stays exactly at its resting charge', weak +
             ': w.final.x 0 .q=@v@ := by exact w.a_charge\n', '1/10', '1/4'),
        pair('B2 receives three real ERROR doses', weak +
             ': w.final.x 1 (.z 2)=start.x 1 (.z 2)+@v@ := by exact w.gain_target\n', '9/5', '6/5'),
        pair('ERROR ledger derives1.8', weak +
             ': w.execution.ledger.error 1 2=@v@ := by exact w.error_target\n', '9/5', '0'),
        pair('other-port ERROR ledger remains zero', weak +
             ': w.execution.ledger.error 0 2=@v@ := by exact w.error_other 0 2 (Or.inl (by decide))\n', '0', '9/5'),
        pair('prepared weak inputs add no MARK', weak +
             '(i : Fin 2) (p : Port) : w.execution.ledger.mark i p=@v@ := by exact w.mark_zero i p\n', '0', '1/10'),
        pair('own recoveries are preserved', weak +
             '(i : Fin 2) : w.final.x i .b=start.x i .b@v@ := by exact w.recovery i\n', '', '+1/10'),
        pair('saturation includes the actual344 delivery', weak +
             ': CompleteThrough w.execution @v@ := by exact w.complete\n', '344', '352'),
        pair('residual learned factory issues exactly one new token', first_factory, '29', '28'),
        pair('first B FIRE emits on its own cell', fire +
             ': f.execution.ledger.emissions=[(@v@,f.final.time)] := by exact f.emissions\n', '1', '0'),
        pair('first FIRE does not preload a receipt', fire +
             ': f.execution.deliveries=@v@ := by exact f.deliveries\n', '[]', '[⟨0,2,f.final.time⟩]'),
        pair('reverse route targets Aport2', fire +
             ': reciprocalEntryRouter forward backward 1 f.final.time=[⟨0,@v@,f.final.time+backward f.final.time⟩] := by exact f.protocol_route\n', '2', '1'),
        pair('wire jitter is evaluated at its actual issuing FIRE', fire +
             ': f.final.pending=w.final.pending++[⟨0,2,f.final.time+backward @v@⟩] := by exact f.pending\n', 'f.final.time', 'w.final.time'),
        pair('the real first B latency is bounded by its own resting reference', fire +
             ': f.firing.latency≤restLatency (Real.exp (w.final.x 1 (.z @v@))) := by exact f.first_le_rest\n', '2', '1'),
        pair('first FIRE retains the carried gain', fire +
             ': f.final.x 1 (.z 2)=w.final.x 1 (.z 2)@v@ := by exact f.gains 1 2\n', '', '+3/5'),
        pair('A remains prepared while B really fires', fire +
             ': f.final.main 0=.@v@ := by exact f.a_prepared.ready\n', 'ready', 'fast'),
        pair('first B FIRE and its issued wire are saturated before receipt', fire +
             '(hd : ∀ time, (3/10:ℝ)≤backward time ∧ backward time≤2/5) : CompleteThrough f.execution (f.final.time@v@) := by exact f.complete hd\n', '', '+1'),
        pair('left product uses only interval closure and retains real FIRE outputs', left_product,
             'a.ledger.emissions.map (fun event => (0,event.2))', '[]'),
        pair('right product uses only interval closure and retains real FIRE outputs', right_product,
             'b.ledger.emissions.map (fun event => (1,event.2))', '[]'),
        pair('original-birth staged trace still has cumulative A28', staged +
             ': ((z.feedback_first_fire_staged a).before.emissionTimes 0++(z.feedback_first_fire_staged a).after.emissionTimes 0).length=@v@ := by exact (z.feedback_first_fire_counts hb a).1\n', '28', '27'),
        pair('original-birth staged trace now has cumulative B15', staged +
             ': ((z.feedback_first_fire_staged a).after.emissionTimes 1).length=@v@ := by exact (z.feedback_first_fire_counts hb a).2\n', '15', '14'),
        pair('B2 learning keeps its independent newborn coordinates', staged +
             ': w.final.x 1 (.z 2)=@v@+9/5 := by exact z.feedback_weak_b_gain_own w\n', 'newborn.x (.z 2)', 'born.x 0 (.z 2)'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-feedback-entry-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid feedback-entry controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
