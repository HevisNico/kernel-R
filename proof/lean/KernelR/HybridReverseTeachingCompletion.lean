import KernelR.HybridReverseEntryCompletion
import KernelR.HybridReverseLearnedEpoch

/-! The complete reciprocal teaching suffix, constructed from the actual
first reverse interleaving at352 through the closed section459.9. -/
namespace KernelR.Hybrid

structure ReverseTeachingCompletion {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    (p : FirstReverseInterleavedPair r) where
  entry : ReverseEntryCompletion p
  epoch : ReverseLearnedEpoch f.parametersA f.parametersB forward backward entry.final
  final : Snapshot 2
  execution : Execution θ (reciprocalEntryRouter forward backward) p.final final
  date : final.time = 4599 / 10
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i q, final.raw i q = none
  pending : final.pending = sourceTrain 1 2 480 8 16
  a_gain_target : final.x 0 (.z 2) = p.final.x 0 (.z 2) + 6 / 5
  a_gain_other : ∀ q, q ≠ 2 → final.x 0 (.z q) = p.final.x 0 (.z q)
  b_gains : ∀ q, final.x 1 (.z q) = p.final.x 1 (.z q)
  recovery : ∀ i, final.x i .b = p.final.x i .b
  a_emission_count : (execution.emissionTimes 0).length = 10
  b_emission_count : (execution.emissionTimes 1).length = 12
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (4599 / 10)

theorem reverse_teaching_completion_exists {θ ε forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    (p : FirstReverseInterleavedPair r) (hb : PhysicalBox θ ε)
    (hzA : Real.log (3 / 10) - 1 / 100000 ≤ r.final.x 0 (.z 2) ∧
      r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000)
    (hGB : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧ Real.exp (w.final.x 1 (.z 2)) ≤ 2)
    (hback : ∀ t, (3 / 10 : ℝ) ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (ReverseTeachingCompletion p) := by
  obtain ⟨entry⟩ := reverse_entry_completion_exists p hb hzA hGB hback
  have hbP : PhysicalBox (extendParameters f.parametersA (f.parametersB 0)) ε := by
    rw [f.parameters_product]
    exact hb
  have hfP : PhysicalInvariant (extendParameters f.parametersA (f.parametersB 0)) entry.final := by
    rw [f.parameters_product]
    exact entry.physical
  have hGA : 9 / 5 ≤ Real.exp (entry.final.x 0 (.z 2)) ∧ Real.exp (entry.final.x 0 (.z 2)) ≤ 2 := by
    have hz : entry.final.x 0 (.z 2) = r.final.x 0 (.z 2) + 9 / 5 := by
      rw [entry.a_gain_target,p.a_gain_target hb hzA.2]
      ring
    exact learned_gain_bounds (by rw [hz]; linarith [hzA.1]) (by rw [hz]; linarith [hzA.2])
  have hGB' : 9 / 5 ≤ Real.exp (entry.final.x 1 (.z 2)) ∧ Real.exp (entry.final.x 1 (.z 2)) ≤ 2 := by
    rw [entry.b_gains,p.b_gains]
    exact hGB
  obtain ⟨epoch⟩ := reverse_learned_epoch_exists hbP entry.final hfP entry.raw_valid entry.date
    entry.prepared entry.charge hGA hGB' entry.raw_active entry.raw_other entry.pending
    forward backward hback
  let execution := entry.execution.append (epoch.execution.cast_parameters f.parameters_product)
  have hcast (i : Fin 2) :
      (epoch.execution.cast_parameters f.parameters_product).emissionTimes i = epoch.execution.emissionTimes i := by
    simp only [Execution.emissionTimes,Execution.cast_parameters_ledger]
  refine ⟨{
    entry := entry, epoch := epoch, final := epoch.final, execution := execution
    date := epoch.date, prepared := epoch.prepared, charge := epoch.charge, raw_none := epoch.raw_none
    pending := epoch.pending
    a_gain_target := (epoch.gains 0 2).trans entry.a_gain_target
    a_gain_other := fun q hq => (epoch.gains 0 q).trans (entry.a_gain_other q hq)
    b_gains := fun q => (epoch.gains 1 q).trans (entry.b_gains q)
    recovery := fun i => (epoch.recovery i).trans (entry.recovery i)
    a_emission_count := ?_, b_emission_count := ?_
    physical := by simpa only [f.parameters_product] using epoch.physical
    raw_valid := epoch.raw_valid, complete := ?_
  }⟩
  · simp only [execution,Execution.emissionTimes_append,List.length_append,hcast,
      entry.a_emission_count,epoch.a_emission_count]
  · simp only [execution,Execution.emissionTimes_append,List.length_append,hcast,
      entry.b_emission_count,epoch.b_emission_count]
  · simpa only [CompleteThrough] using epoch.complete

namespace ReverseTeachingCompletion
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
  {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
  {p : FirstReverseInterleavedPair r} (t : ReverseTeachingCompletion p)

theorem pending_length : t.final.pending.length = 16 := by
  rw [t.pending]
  simp only [sourceTrain,List.length_ofFn]

theorem a_error_dose : t.execution.ledger.error 0 2 = 6 / 5 := by
  have h := t.execution.gain_balance 0 2
  rw [t.a_gain_target] at h
  linarith

theorem error_other (i : Fin 2) (q : Port) (h : i ≠ 0 ∨ q ≠ 2) :
    t.execution.ledger.error i q = 0 := by
  have hb := t.execution.gain_balance i q
  rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
  · rw [t.a_gain_other q (by simpa using h)] at hb
    linarith
  · rw [t.b_gains] at hb
    linarith

theorem recovery_zero (i : Fin 2) : t.execution.ledger.recovery i = 0 := by
  have h := t.execution.recovery_balance i
  rw [t.recovery] at h
  linarith

end ReverseTeachingCompletion
end KernelR.Hybrid
