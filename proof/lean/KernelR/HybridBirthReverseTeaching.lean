import KernelR.HybridBirthFirstReverseInterleavedPair
import KernelR.HybridFirstReverseInterleavedMemory
import KernelR.HybridReverseTeachingCompletion

/-! Construct the complete reciprocal teaching epoch from the original
one-cell birth, retaining each cell's own initial memory and its real trace. -/
namespace KernelR.Hybrid

structure ConstructedReverseTeaching (θ : Fin 1 → Parameters) (born : Snapshot 1)
    (fresh : Parameters) (newborn : Newborn) (forward backward : ℝ → ℝ) where
  final : Snapshot 2
  staged : StagedExecution θ fresh (fun _ _ => [])
    (reciprocalEntryRouter forward backward) born final
  newborn_origin : staged.birth.newborn = newborn
  sources_origin : staged.birth.sources = constructedBBirthSources
  date : final.time = 4599 / 10
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i q, final.raw i q = none
  pending : final.pending = sourceTrain 1 2 480 8 16
  a_emission_count : (staged.before.emissionTimes 0 ++ staged.after.emissionTimes 0).length = 38
  b_emission_count : (staged.after.emissionTimes 1).length = 27
  a_gain_target : final.x 0 (.z 2) = born.x 0 (.z 2) + 9 / 5
  a_gain_first : final.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5
  a_gain_other : ∀ q, q ≠ 0 → q ≠ 2 → final.x 0 (.z q) = born.x 0 (.z q)
  b_gain_target : final.x 1 (.z 2) = newborn.x (.z 2) + 9 / 5
  b_gain_first : final.x 1 (.z 1) = newborn.x (.z 1) + 3 / 5
  b_gain_other : ∀ q, q ≠ 1 → q ≠ 2 → final.x 1 (.z q) = newborn.x (.z q)
  a_recovery : final.x 0 .b = born.x 0 .b + 1 / 10
  b_recovery : final.x 1 .b = newborn.x .b + 1 / 10
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final
  complete : CompleteThrough staged.after (4599 / 10)

namespace FirstCoupledTeaching
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {v : SecondWiredArrival s}
  {f : FirstReceiverFire v} {g : FirstReceiverFastEnd f} {u : FirstPostReceiverPair g}
  {t : ThirdWiredArrival u} {x : FirstCoupledPreparedPair t} (z : FirstCoupledTeaching x)

noncomputable def reverse_teaching_staged
    {w : FeedbackWeakEntry (extendParameters θ fresh)
      (reciprocalEntryRouter forward backward) z.final}
    {a : FeedbackFirstFire w} {q : FirstReverseWiredArrival a}
    {p : FirstReverseInterleavedPair q} (finish : ReverseTeachingCompletion p) :
    StagedExecution θ fresh (fun _ _ => [])
      (reciprocalEntryRouter forward backward) born finish.final :=
  { z.first_reverse_interleaved_staged p with
    after := (z.first_reverse_interleaved_staged p).after.append finish.execution }

end FirstCoupledTeaching

/-- No receiving calendar or reaching-execution premise is supplied: the
birth protocol constructs both cells and their actual reciprocal teaching. -/
theorem birth_protocol_reverse_teaching_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ q, born.aux 0 q = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hd : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5)
    (hback : ∀ time, (3 / 10 : ℝ) ≤ backward time ∧ backward time ≤ 2 / 5) :
    Nonempty (ConstructedReverseTeaching θ born fresh newborn forward backward) := by
  obtain ⟨c,b,r,s,v,f,g,u,t,x,z,w,a,q,p,_,_,hA,hB,hownA,hownB⟩ :=
    birth_protocol_first_reverse_interleaved_pair_exists hborn hb ha hqueue newborn forward backward hd hback
  have hzA : Real.log (3 / 10) - 1 / 100000 ≤ q.final.x 0 (.z 2) ∧
      q.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [z.first_reverse_wire_a_gain_own hb.extend_old q 2 (by decide)]
    simpa only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false]
      using ((hborn.2.2 0).2.2.2.2 (2 : Port)).1
  have hzB : Real.log (3 / 10) - 1 / 100000 ≤ newborn.x (.z 2) ∧
      newborn.x (.z 2) ≤ Real.log (3 / 10) + 1 / 100000 := by
    simpa only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] using newborn.gain (2 : Port)
  have hGB : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧ Real.exp (w.final.x 1 (.z 2)) ≤ 2 := by
    rw [z.feedback_weak_b_gain_own w]
    exact learned_gain_bounds (by linarith [hzB.1]) (by linarith [hzB.2])
  obtain ⟨finish⟩ := reverse_teaching_completion_exists p hb hzA hGB hback
  have hcomplete : CompleteThrough (z.reverse_teaching_staged finish).after (4599 / 10) := by
    simpa only [CompleteThrough] using finish.complete
  refine ⟨{
    final := finish.final, staged := z.reverse_teaching_staged finish
    newborn_origin := ?_, sources_origin := ?_
    date := finish.date, prepared := finish.prepared, charge := finish.charge
    raw_none := finish.raw_none, pending := finish.pending
    a_emission_count := ?_, b_emission_count := ?_
    a_gain_target := ?_, a_gain_first := ?_, a_gain_other := ?_
    b_gain_target := ?_, b_gain_first := ?_, b_gain_other := ?_
    a_recovery := ?_, b_recovery := ?_
    physical := finish.physical, raw_valid := finish.raw_valid, complete := hcomplete
  }⟩
  · exact b.newborn_state
  · exact b.source_list
  · simp only [FirstCoupledTeaching.reverse_teaching_staged,Execution.emissionTimes_append,
      List.length_append,finish.a_emission_count]
    simp only [List.length_append] at hA
    omega
  · simp only [FirstCoupledTeaching.reverse_teaching_staged,Execution.emissionTimes_append,
      List.length_append,finish.b_emission_count]
    omega
  · rw [finish.a_gain_target,hownA]; ring
  · rw [finish.a_gain_other 0 (by decide),p.a_gain_other 0 (by decide),q.gains,a.gains,
      w.gain_other 0 0 (Or.inl (by decide)),z.a_gain_target hb.extend_old]
  · intro port hp0 hp2
    rw [finish.a_gain_other port hp2,p.a_gain_other port hp2,q.gains,a.gains,
      w.gain_other 0 port (Or.inl (by decide)),z.a_gain_other hb.extend_old port hp0]
  · rw [finish.b_gains,hownB]
  · rw [finish.b_gains,p.b_gains,w.gain_other 1 1 (Or.inr (by decide)),z.b_gain_target hb hd]
  · intro port hp1 hp2
    rw [finish.b_gains,p.b_gains,w.gain_other 1 port (Or.inr hp2),z.b_gain_other port hp1]
  · rw [finish.recovery,p.a_recovery,q.recovery,a.recovery,w.recovery,z.a_recovery_own hb.extend_old]
  · rw [finish.recovery,p.b_recovery,z.b_recovery_own]

namespace ConstructedReverseTeaching
variable {θ born fresh newborn forward backward}
  (t : ConstructedReverseTeaching θ born fresh newborn forward backward)

theorem pending_length : t.final.pending.length = 16 := by
  rw [t.pending]
  simp only [sourceTrain,List.length_ofFn]

theorem ready (i : Fin 2) : t.final.main i = .ready := (t.prepared i).ready

end ConstructedReverseTeaching
end KernelR.Hybrid
