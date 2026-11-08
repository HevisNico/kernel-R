#!/usr/bin/env python3
"""Paired contracts for actual reverse receipt and its original-birth section352."""
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_check import lean_check_command

ROOT = Path(__file__).resolve().parents[2]
PREFIX = ('import KernelR.HybridBirthFirstReverseInterleavedPair\n'
          'import KernelR.HybridFirstReverseInterleavedMemory\n'
          'open KernelR.Hybrid\n')


def cases():
    receipt = """example {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} (r : FirstReverseWiredArrival f) """
    interleaved = """example {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    (p : FirstReverseInterleavedPair r) """
    analytic = interleaved + """{ε} (hb : PhysicalBox θ ε)
    (hz : r.final.x 0 (.z 2) ≤ Real.log (3/10)+1/100000) """
    fast = 'example {θ route s q} (c : PortFastCompletion θ route s q) '
    receiver = """example {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    (a : FirstReverseReceiverWeak r) """
    receipt_factory = """example {θ ε forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    (f : FeedbackFirstFire w) (hb : PhysicalBox θ ε)
    (hg : Real.exp (w.final.x 1 (.z 2)) ≤ 2)
    (hd : ∀ t, (3/10:ℝ) ≤ backward t ∧ backward t ≤ 2/5) :
    ∃ r : FirstReverseWiredArrival f, r.final.pending.length=@v@ := by
  obtain ⟨r⟩ := first_reverse_wired_arrival_exists f hb hg hd
  exact ⟨r,r.pending_length⟩
"""
    fast_factory = """example {θ ε forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    (f : FeedbackFirstFire w) (hb : PhysicalBox θ ε)
    (hg : Real.exp (w.final.x 1 (.z 2)) ≤ 2) :
    ∃ c : PortFastCompletion f.parametersB (fun _ _ => []) f.localB 2,
      c.final.time=f.final.time+@v@ := by
  obtain ⟨c⟩ := f.sender_fast_end_exists hb hg
  exact ⟨c,by rw [c.date,f.localB_clock]⟩
"""
    pair_factory = receipt + """{ε} (hb : PhysicalBox θ ε)
    (hz : r.final.x 0 (.z 2) ≤ Real.log (3/10)+1/100000) :
    ∃ p : FirstReverseInterleavedPair r, p.final.pending.length=@v@ := by
  obtain ⟨p⟩ := first_reverse_interleaved_pair_exists r hb hz
  exact ⟨p,p.pending_length⟩
"""
    staged = """example {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {v : SecondWiredArrival s}
    {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
    {t : ThirdWiredArrival u} {x : FirstCoupledPreparedPair t} (z : FirstCoupledTeaching x)
    {w : FeedbackWeakEntry (extendParameters θ fresh) (reciprocalEntryRouter forward backward) z.final}
    {a : FeedbackFirstFire w} {q : FirstReverseWiredArrival a}
    (p : FirstReverseInterleavedPair q) {ε} (hborn : BirthState born)
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) """
    birth_factory = 'example {θ born fresh ε}\n    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)\n    (ha : ∀ p, born.aux 0 p = .ready)\n    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)\n    (newborn : Newborn) (forward backward : ℝ → ℝ)\n    (hd : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5)\n    (hback : ∀ time, (3 / 10 : ℝ) ≤ backward time ∧ backward time ≤ 2 / 5) :\n    ∃ c : ConstructedBirthPreparation θ born,\n      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,\n        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ v : SecondWiredArrival s,\n          ∃ f : FirstReceiverFire v, ∃ g : FirstReceiverFastEnd f, ∃ u : FirstPostReceiverPair g,\n            ∃ t : ThirdWiredArrival u, ∃ x : FirstCoupledPreparedPair t, ∃ z : FirstCoupledTeaching x,\n              ∃ w : FeedbackWeakEntry (extendParameters θ fresh)\n                  (reciprocalEntryRouter forward backward) z.final,\n                ∃ a : FeedbackFirstFire w, ∃ q : FirstReverseWiredArrival a,\n                  ∃ p : FirstReverseInterleavedPair q,\n                    CompleteThrough (z.first_reverse_interleaved_staged p).after @v@ ∧\n                      p.final.pending.length = 27 ∧\n                      ((z.first_reverse_interleaved_staged p).before.emissionTimes 0 ++\n                        (z.first_reverse_interleaved_staged p).after.emissionTimes 0).length = 28 ∧\n                      ((z.first_reverse_interleaved_staged p).after.emissionTimes 1).length = 15 ∧\n                      p.final.x 0 (.z 2) = born.x 0 (.z 2) + 3 / 5 ∧\n                      p.final.x 1 (.z 2) = newborn.x (.z 2) + 9 / 5 := by\n  exact birth_protocol_first_reverse_interleaved_pair_exists hborn hb ha hqueue newborn forward backward hd hback\n'

    def pair(label, template, good, bad):
        assert '@v@' in template
        assert good != bad
        return label, template.replace('@v@', good), template.replace('@v@', bad)

    return [
        pair('actual FIRE constructs its reverse receipt without a reaching trace', receipt_factory, '28', '29'),
        pair('actual sender section constructs FAST exit one unit later', fast_factory, '1', '2'),
        pair('actual receipt constructs source352 and its exact remaining queue', pair_factory, '27', '28'),
        pair('original birth factory reaches352 without a continuation premise', birth_factory, '352', '360'),
        pair('receipt occurs at its actual issuing FIRE plus sampled reverse delay', receipt +
             ': r.final.time=f.final.time+backward @v@ := by exact r.date\n', 'f.final.time', 'w.final.time'),
        pair('receipt consumes the issued wire and retains the original external queue', receipt +
             ': r.final.pending=@v@ := by exact r.pending\n', 'w.final.pending', 'f.final.pending'),
        pair('receipt retains28 future source occurrences', receipt +
             ': r.final.pending.length=@v@ := by exact r.pending_length\n', '28', '27'),
        pair('receiving RAW uses its own real receipt origin', receipt +
             ': r.final.raw 0 2=some @v@ := by exact r.raw_active\n', 'r.final.time', 'f.final.time'),
        pair('actual delivery is the token issued by the real B FIRE', receipt +
             ': r.execution.deliveries=@v@ := by exact r.deliveries\n', '[f.reverseToken]', '[]'),
        pair('transport to receipt adds no FIRE', receipt +
             ': r.execution.ledger.emissions=@v@ := by exact r.emissions\n', '[]', '[(0,r.final.time)]'),
        pair('receipt is saturated at its real delivery clock', receipt +
             ': CompleteThrough r.execution (r.final.time@v@) := by exact r.complete\n', '', '+1'),
        pair('sender mode is retained from the actual maximal cut', receipt +
             ': r.final.main 1=@v@ := by exact r.b_main\n', 'r.cutH.state.main 0', '.ready'),
        pair('sender energy is its actual cut energy without a reset', receipt +
             ': r.final.x 1 .energy=@v@ := by exact congrFun r.b_values .energy\n', 'r.cutH.state.x 0 .energy', '100'),
        pair('quiet receiving A retains its exact resting charge', receipt +
             ': r.final.x 0 .q=@v@ := by exact r.a_charge\n', '1/10', '1/4'),
        pair('receipt transport preserves every own log-gain', receipt +
             '(i : Fin 2) (p : Port) : r.final.x i (.z p)=f.final.x i (.z p)@v@ := by exact r.gains i p\n', '', '+3/5'),
        pair('receipt transport has zero ERROR', receipt +
             '(i : Fin 2) (p : Port) : r.execution.ledger.error i p=@v@ := by exact r.error_zero i p\n', '0', '3/5'),
        pair('receipt transport has zero recovery dose', receipt +
             '(i : Fin 2) : r.execution.ledger.recovery i=@v@ := by exact r.recovery_zero i\n', '0', '1/10'),
        pair('sender RAW retains344 and expires at345 even at a coincident cut', receipt +
             ': r.final.raw 1 2=(if r.final.time<@v@ then some 344 else none) := by exact r.sender_raw_origin\n', '345', '344'),
        pair('real FAST exit has charge one quarter', fast +
             ': c.final.x 0 .q=@v@ := by exact c.charge\n', '1/4', '1/10'),
        pair('FAST completion removes expired RAW', fast +
             ': c.final.raw 0 q=@v@ := by exact c.raw_none 0 q\n', 'none', 'some s.time'),
        pair('A keeps its previously acquired port0 memory through the weak response', interleaved +
             ': p.final.x 0 (.z 0)=r.final.x 0 (.z 0)@v@ := by exact p.a_gain_other 0 (by decide)\n', '', '+3/5'),
        pair('FAST continuation introduces no additional emission', fast +
             ': c.execution.ledger.emissions=@v@ := by exact c.emissions\n', '[]', '[(0,s.time)]'),
        pair('interleaved pair reaches the real352 boundary', interleaved +
             ': p.final.time=@v@ := by exact p.date\n', '352', '360'),
        pair('real source352 leaves27 source occurrences', interleaved +
             ': p.final.pending.length=@v@ := by exact p.pending_length\n', '27', '28'),
        pair('future queue starts at360 and keeps the second B train', interleaved +
             ': p.final.pending=sourceTrain 1 2 360 8 @v@++sourceTrain 1 2 480 8 16 := by exact p.pending\n', '11', '12'),
        pair('interleaved path really delivers the external B352 occurrence', interleaved +
             ': p.execution.deliveries=[⟨1,2,@v@⟩] := by exact p.deliveries\n', '352', '360'),
        pair('B352 RAW is fresh at its own source clock', interleaved +
             ': p.final.raw 1 2=some @v@ := by exact p.raw_active\n', '352', 'r.final.time'),
        pair('receiver energy comes from its retained actual weak path', interleaved +
             ': p.final.x 0 .energy=@v@ := by exact congrFun p.a_values .energy\n', 'p.receiver.cut352.state.x 0 .energy', '100'),
        pair('A retains carried charge at least rest without an imposed reset', interleaved +
             ': 1/10 @v@ p.final.x 0 .q := by exact p.a_charge_lower\n', '≤', '='),
        pair('actual first reverse weak response learns ERROR0.6', analytic +
             ': p.execution.ledger.error 0 2=@v@ := by exact p.a_error_dose hb hz\n', '3/5', '0'),
        pair('B gains remain stable and its ERROR ledger is zero', interleaved +
             ': p.execution.ledger.error 1 2=@v@ := by exact p.b_error_zero 2\n', '0', '3/5'),
        pair('neither cell acquires a recovery dose through the interleaving', interleaved +
             '(i : Fin 2) : p.execution.ledger.recovery i=@v@ := by exact p.recovery_zero i\n', '0', '1/10'),
        pair('A old input RAW has actually expired by352', interleaved +
             ': p.final.raw 0 2=@v@ := by exact p.a_raw_none 2\n', 'none', 'some r.final.time'),
        pair('retained receiver continuation never injects the global next source', receiver +
             ': a.continuation.deliveries=@v@ := by exact a.continuation_deliveries\n', '[]', '[⟨0,2,352⟩]'),
        pair('retained weak continuation adds no output', receiver +
             ': a.continuation.ledger.emissions=@v@ := by exact a.continuation_emissions\n', '[]', '[(0,352)]'),
        pair('weak endpoint remains on its original source-relative clock', receiver +
             ': a.weak.final.time=r.receiverLocal.time+@v@ := by exact a.weak.date\n', '15/2', '8'),
        pair('original staged prefix retains cumulative A28', staged +
             ': ((z.first_reverse_interleaved_staged p).before.emissionTimes 0++(z.first_reverse_interleaved_staged p).after.emissionTimes 0).length=@v@ := by exact (z.first_reverse_interleaved_counts hb.extend_old p).1\n', '28', '29'),
        pair('original staged prefix retains cumulative B15', staged +
             ': ((z.first_reverse_interleaved_staged p).after.emissionTimes 1).length=@v@ := by exact (z.first_reverse_interleaved_counts hb.extend_old p).2\n', '15', '16'),
        pair('A learns from its own original birth coordinates', staged +
             ': p.final.x 0 (.z 2)=@v@+3/5 := by exact z.first_reverse_interleaved_a_gain_own hborn hb p\n', 'born.x 0 (.z 2)', 'newborn.x (.z 2)'),
        pair('B keeps its own independently born port2 memory', staged +
             ': p.final.x 1 (.z 2)=@v@+9/5 := by exact z.first_reverse_interleaved_b_gain_own p\n', 'newborn.x (.z 2)', 'born.x 0 (.z 2)'),
    ]


def main():
    controls = cases()
    with tempfile.TemporaryDirectory(prefix='hybrid-reverse-receipt-negative-', dir=ROOT) as tmp:
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

        check('\n'.join(good for _, good, _ in controls), True, 'valid reverse-receipt controls')
        for name, _, bad in controls:
            check(bad, False, name)
            print(f'{name}: physical conclusion accepted; altered claim rejected.', flush=True)


if __name__ == '__main__':
    main()
