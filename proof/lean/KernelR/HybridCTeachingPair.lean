import KernelR.HybridCPreparedPair
import KernelR.HybridCLearnedEpoch

/-! Complete the actual B/C teaching pair from C's independent birth state.
The first three contacts prepare C; thirteen learned cycles finish the epoch. -/
namespace KernelR.Hybrid

structure CTeachingPair {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay} {c : ConstructedCBirth t freshC newbornC delay}
    {w : CWeakEntry c} {p : CFirstLearnedBoundary w} (x : CPreparedPair p) where
  epoch : CLearnedEpoch (fun _ : Fin 1 => freshB) (fun _ => freshC) delay x.final
  final : Snapshot 2
  execution : Execution (cBirthPairParameters freshB freshC) (cBirthPairRouter delay) c.activePair final
  date : final.time = 6399 / 10
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i q, final.raw i q = none
  pending : final.pending = sourceTrain 1 0 640 4 25
  sender_gains : ∀ q, final.x 0 (.z q) = c.activePair.x 0 (.z q)
  c_gain_target : final.x 1 (.z 1) = newbornC.x (.z 1) + 3 / 5
  c_gain_other : ∀ q, q ≠ 1 → final.x 1 (.z q) = newbornC.x (.z q)
  sender_recovery : final.x 0 .b = c.activePair.x 0 .b
  c_recovery : final.x 1 .b = newbornC.x .b + 1 / 10
  b_emission_count : (execution.emissionTimes 0).length = 16
  c_emission_count : (execution.emissionTimes 1).length = 14
  physical : PhysicalInvariant (cBirthPairParameters freshB freshC) final
  raw_valid : RawValid final
  complete : CompleteThrough execution (6399 / 10)

theorem c_teaching_pair_exists {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay ε} {c : ConstructedCBirth t freshC newbornC delay}
    {w : CWeakEntry c} {p : CFirstLearnedBoundary w} (x : CPreparedPair p)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hd : ∀ F, (3 / 10 : ℝ) ≤ delay F ∧ delay F ≤ 2 / 5) :
    Nonempty (CTeachingPair x) := by
  have hbPair := cBirthPairParameters_physical_box hb
  obtain ⟨epoch⟩ := c_learned_epoch_exists (θC := fun _ : Fin 1 => freshC) hbPair x.final
    x.protectedReturn.physical x.protectedReturn.raw_valid x.date x.protectedReturn.prepared
    x.protectedReturn.charge x.sender_gain_bounds x.c_gain_bounds
    (by rw [x.protectedReturn.date]; exact x.protectedReturn.raw_active)
    x.protectedReturn.raw_other x.pending delay hd
  let execution := x.execution.append epoch.execution
  refine ⟨{
    epoch := epoch, final := epoch.final, execution := execution
    date := epoch.date, prepared := epoch.prepared, charge := epoch.charge, raw_none := epoch.raw_none
    pending := epoch.pending
    sender_gains := fun q => (epoch.gains 0 q).trans (x.sender_gains q)
    c_gain_target := (epoch.gains 1 1).trans x.c_gain_target
    c_gain_other := fun q hq => (epoch.gains 1 q).trans (x.c_gain_other q hq)
    sender_recovery := (epoch.recovery 0).trans x.sender_recovery
    c_recovery := (epoch.recovery 1).trans x.c_recovery
    b_emission_count := ?_, c_emission_count := ?_
    physical := epoch.physical, raw_valid := epoch.raw_valid, complete := ?_
  }⟩
  · simp only [execution,Execution.emissionTimes_append,List.length_append,
      x.sender_emission_count,epoch.b_emission_count]
  · simp only [execution,Execution.emissionTimes_append,List.length_append,
      x.c_emission_count,epoch.c_emission_count]
  · simpa only [CompleteThrough] using epoch.complete

namespace CTeachingPair
variable {θ born freshB newbornB forward backward}
  {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
  {freshC newbornC delay} {c : ConstructedCBirth t freshC newbornC delay}
  {w : CWeakEntry c} {p : CFirstLearnedBoundary w} {x : CPreparedPair p} (e : CTeachingPair x)

theorem pending_length : e.final.pending.length = 25 := by
  rw [e.pending]
  simp only [sourceTrain,List.length_ofFn]

theorem error_target : e.execution.ledger.error 1 1 = 3 / 5 := by
  have h := e.execution.gain_balance 1 1
  rw [e.c_gain_target,c.active_pair_c_coordinates] at h
  linarith

theorem recovery_target : e.execution.ledger.recovery 1 = 1 / 10 := by
  have h := e.execution.recovery_balance 1
  rw [e.c_recovery,c.active_pair_c_coordinates] at h
  linarith

end CTeachingPair
end KernelR.Hybrid
