import KernelR.HybridBirthFirstReverseArrival
import KernelR.HybridFirstReverseInterleavedPair

/-! Connect the constructed reciprocal response and next source352 to the
original birth trace, retaining both cells' own acquired memories. -/
namespace KernelR.Hybrid
namespace FirstReverseInterleavedPair
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
  {a : FeedbackFirstFire w} {r : FirstReverseWiredArrival a}
  (p : FirstReverseInterleavedPair r)

theorem emission_times (i : Fin 2) : p.execution.emissionTimes i = [] := by
  simp [Execution.emissionTimes,p.emissions]

end FirstReverseInterleavedPair

namespace FirstCoupledTeaching
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {v : SecondWiredArrival s}
  {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
  {t : ThirdWiredArrival u} {x : FirstCoupledPreparedPair t} (z : FirstCoupledTeaching x)

theorem first_reverse_wire_a_low_bound {ε} (hborn : BirthState born) (hb : PhysicalBox θ ε)
    {w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final}
    {a : FeedbackFirstFire w} (r : FirstReverseWiredArrival a) :
    r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
  rw [z.first_reverse_wire_a_gain_own hb r 2 (by decide)]
  have h := ((hborn.2.2 0).2.2.2.2 (2 : Port)).1.2
  simpa only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] using h

noncomputable def first_reverse_interleaved_staged
    {w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final}
    {a : FeedbackFirstFire w} {r : FirstReverseWiredArrival a}
    (p : FirstReverseInterleavedPair r) :
    StagedExecution θ fresh (fun _ _ => []) (reciprocalEntryRouter forward backward) born p.final :=
  { z.first_reverse_wire_staged r with
    after := (z.first_reverse_wire_staged r).after.append p.execution }

theorem first_reverse_interleaved_counts {ε} (hb : PhysicalBox θ ε)
    {w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final}
    {a : FeedbackFirstFire w} {r : FirstReverseWiredArrival a}
    (p : FirstReverseInterleavedPair r) :
    ((z.first_reverse_interleaved_staged p).before.emissionTimes 0 ++
      (z.first_reverse_interleaved_staged p).after.emissionTimes 0).length = 28 ∧
      ((z.first_reverse_interleaved_staged p).after.emissionTimes 1).length = 15 := by
  simpa only [first_reverse_interleaved_staged,Execution.emissionTimes_append,
    p.emission_times,List.append_nil] using z.first_reverse_wire_counts hb r

theorem first_reverse_interleaved_a_gain_own {ε} (hborn : BirthState born)
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    {w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final}
    {a : FeedbackFirstFire w} {r : FirstReverseWiredArrival a}
    (p : FirstReverseInterleavedPair r) :
    p.final.x 0 (.z 2) = born.x 0 (.z 2) + 3 / 5 := by
  rw [p.a_gain_target hb (z.first_reverse_wire_a_low_bound hborn hb.extend_old r),
    z.first_reverse_wire_a_gain_own hb.extend_old r 2 (by decide)]

theorem first_reverse_interleaved_b_gain_own
    {w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final}
    {a : FeedbackFirstFire w} {r : FirstReverseWiredArrival a}
    (p : FirstReverseInterleavedPair r) :
    p.final.x 1 (.z 2) = newborn.x (.z 2) + 9 / 5 := by
  rw [p.b_gains]
  exact z.feedback_weak_b_gain_own w

end FirstCoupledTeaching

/-- Build the original birth-to352 execution: A's first weak reverse-wire
response is actual, and B's next queued source is actually delivered. -/
theorem birth_protocol_first_reverse_interleaved_pair_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hd : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5)
    (hback : ∀ time, (3 / 10 : ℝ) ≤ backward time ∧ backward time ≤ 2 / 5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ v : SecondWiredArrival s,
          ∃ f : FirstReceiverFire v, ∃ g : FirstReceiverFastEnd f, ∃ u : FirstPostReceiverPair g,
            ∃ t : ThirdWiredArrival u, ∃ x : FirstCoupledPreparedPair t, ∃ z : FirstCoupledTeaching x,
              ∃ w : FeedbackWeakEntry (extendParameters θ fresh)
                  (reciprocalEntryRouter forward backward) z.final,
                ∃ a : FeedbackFirstFire w, ∃ q : FirstReverseWiredArrival a,
                  ∃ p : FirstReverseInterleavedPair q,
                    CompleteThrough (z.first_reverse_interleaved_staged p).after 352 ∧
                      p.final.pending.length = 27 ∧
                      ((z.first_reverse_interleaved_staged p).before.emissionTimes 0 ++
                        (z.first_reverse_interleaved_staged p).after.emissionTimes 0).length = 28 ∧
                      ((z.first_reverse_interleaved_staged p).after.emissionTimes 1).length = 15 ∧
                      p.final.x 0 (.z 2) = born.x 0 (.z 2) + 3 / 5 ∧
                      p.final.x 1 (.z 2) = newborn.x (.z 2) + 9 / 5 := by
  obtain ⟨c,b,r,s,v,f,g,u,t,x,z,_,_,_,_⟩ := birth_protocol_first_coupled_teaching_exists
    hborn hb ha hqueue newborn forward backward hd
  obtain ⟨w⟩ := z.feedback_weak_entry_exists hb
  obtain ⟨a⟩ := z.first_feedback_fire_exists hb w
  have hz : Real.log (3 / 10) - 1 / 100000 ≤ z.final.x 1 (.z 2) ∧
      z.final.x 1 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [z.b_gain_other 2 (by decide)]
    simpa only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] using newborn.gain (2 : Port)
  have hg : Real.exp (w.final.x 1 (.z 2)) ≤ 2 := by
    apply (learned_gain_bounds ?_ ?_).2
    · rw [w.gain_target]; linarith [hz.1]
    · rw [w.gain_target]; linarith [hz.2]
  obtain ⟨q⟩ := first_reverse_wired_arrival_exists a hb hg hback
  obtain ⟨p⟩ := first_reverse_interleaved_pair_exists q hb
    (z.first_reverse_wire_a_low_bound hborn hb.extend_old q)
  have hcomplete : CompleteThrough (z.first_reverse_interleaved_staged p).after 352 := by
    simpa only [CompleteThrough] using p.complete
  have hc := z.first_reverse_interleaved_counts hb.extend_old p
  exact ⟨c,b,r,s,v,f,g,u,t,x,z,w,a,q,p,hcomplete,p.pending_length,hc.1,hc.2,
    z.first_reverse_interleaved_a_gain_own hborn hb p,z.first_reverse_interleaved_b_gain_own p⟩

end KernelR.Hybrid
