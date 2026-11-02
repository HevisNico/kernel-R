import KernelR.HybridConstructedCadenceCascade

/-! The original birth and both independent later births supply a complete
constructed three-cell cadence, with exact cumulative physical counts. -/
namespace KernelR.Hybrid

structure ConstructedBirthCadence (θ : Fin 1 → Parameters) (born : Snapshot 1)
    (freshB freshC : Parameters) (newbornB newbornC : Newborn)
    (forward backward delay cascadeForward cascadeBackward : ℝ → ℝ) where
  entry : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward
  cascade : ConstructedCadenceCascade entry

theorem birth_protocol_cadence_cascade_exists {θ born freshB freshC ε}
    (hborn : @BirthState 1 born)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ q, born.aux 0 q = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newbornB newbornC : Newborn) (forward backward delay cascadeForward cascadeBackward : ℝ → ℝ)
    (hforward : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5)
    (hback : ∀ time, (3 / 10 : ℝ) ≤ backward time ∧ backward time ≤ 2 / 5)
    (hdelay : ∀ time, (3 / 10 : ℝ) ≤ delay time ∧ delay time ≤ 2 / 5)
    (hcascadeForward : ∀ time, (3 / 10 : ℝ) ≤ cascadeForward time ∧ cascadeForward time ≤ 2 / 5)
    (hcascadeBackward : ∀ time, (3 / 10 : ℝ) ≤ cascadeBackward time ∧ cascadeBackward time ≤ 2 / 5) :
    Nonempty (ConstructedBirthCadence θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward) := by
  obtain ⟨entry⟩ := birth_protocol_cadence_first_mark_return_exists hborn hb ha hqueue newbornB newbornC
    forward backward delay cascadeForward cascadeBackward hforward hback hdelay
    hcascadeForward hcascadeBackward
  obtain ⟨cascade⟩ := constructed_cadence_cascade_exists entry hb hborn hcascadeForward hcascadeBackward
  exact ⟨⟨entry,cascade⟩⟩

namespace ConstructedBirthCadence
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  (c : ConstructedBirthCadence θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward)

noncomputable abbrev final : Snapshot 3 := c.cascade.final

noncomputable abbrev execution := c.cascade.execution

theorem date : c.final.time = 7899 / 10 := c.cascade.date

theorem pending : c.final.pending = [] := c.cascade.pending

theorem ready (i : Fin 3) : ReadyCoordinates c.final i := c.cascade.ready i

theorem charge (i : Fin 3) : c.final.x i .q = 1 / 10 := c.cascade.charge i

theorem raw_none (i : Fin 3) (q : Port) : c.final.raw i q = none := c.cascade.raw_none i q

theorem complete : CompleteThrough c.execution (7899 / 10) := c.cascade.complete

theorem a_emission_count :
    (c.entry.wave.cadence.teaching.reverse.staged.before.emissionTimes 0 ++
      c.entry.wave.cadence.teaching.reverse.staged.after.emissionTimes 0).length +
      (c.entry.wave.cadence.teaching.staged.before.emissionTimes 0).length +
      (c.entry.wave.cadence.teaching.staged.after.emissionTimes 0).length +
      (c.execution.emissionTimes 0).length = 54 := by
  rw [c.cascade.a_emission_count,c.entry.wave.cadence.teaching.a_emission_count]

theorem b_emission_count : (c.entry.wave.cadence.teaching.reverse.staged.after.emissionTimes 1).length +
    (c.entry.wave.cadence.teaching.staged.before.emissionTimes 1).length +
    (c.entry.wave.cadence.teaching.staged.after.emissionTimes 1).length +
    (c.execution.emissionTimes 1).length = 61 := by
  rw [c.cascade.b_emission_count,c.entry.wave.cadence.teaching.b_emission_count]

theorem c_emission_count : (c.entry.wave.cadence.teaching.staged.after.emissionTimes 2).length +
    (c.execution.emissionTimes 2).length = 34 := by
  rw [c.cascade.c_emission_count,c.entry.wave.cadence.teaching.c_emission_count]

theorem a_gain_own : c.final.x 0 (.z 2) = born.x 0 (.z 2) + 12 / 5 := c.cascade.a_gain_target

theorem b_gain_own : c.final.x 1 (.z 2) = newbornB.x (.z 2) + 12 / 5 := c.cascade.b_gain_target

theorem c_gain_own : c.final.x 2 (.z 0) = newbornC.x (.z 0) + 12 / 5 := c.cascade.c_gain_target

theorem a_recovery_own : c.final.x 0 .b = born.x 0 .b + 3 / 10 := c.cascade.a_recovery

theorem b_recovery_own : c.final.x 1 .b = newbornB.x .b + 3 / 10 := c.cascade.b_recovery

theorem c_recovery_own : c.final.x 2 .b = newbornC.x .b + 3 / 10 := c.cascade.c_recovery

end ConstructedBirthCadence
end KernelR.Hybrid
