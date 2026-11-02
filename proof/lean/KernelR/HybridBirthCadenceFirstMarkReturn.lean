import KernelR.HybridBirthCadenceFirstWave
import KernelR.HybridCadenceFirstMarkReturn

/-! The original births and first cadence wave reach the actual C660
source after C's first fast-cadence protected MARK. -/
namespace KernelR.Hybrid

structure ConstructedCadenceFirstMarkReturn (θ : Fin 1 → Parameters) (born : Snapshot 1)
    (freshB freshC : Parameters) (newbornB newbornC : Newborn)
    (forward backward delay cascadeForward cascadeBackward : ℝ → ℝ) where
  wave : ConstructedCadenceFirstWave θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward
  source : FirstCadenceMarkSource wave.firstA
  mark : FirstCadenceMarkReturn source
  execution : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) wave.cadence.teaching.final mark.final
  reconstruct : execution = (wave.execution.append source.execution).append mark.execution

theorem birth_protocol_cadence_first_mark_return_exists {θ born freshB freshC ε}
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
    Nonempty (ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward) := by
  obtain ⟨wave⟩ := birth_protocol_cadence_first_wave_exists hborn hb ha hqueue newbornB newbornC
    forward backward delay cascadeForward cascadeBackward hforward hback hdelay
    hcascadeForward hcascadeBackward
  obtain ⟨source⟩ := first_cadence_mark_source_exists wave.firstA hb
  obtain ⟨mark⟩ := first_cadence_mark_return_exists source hb
  exact ⟨⟨wave,source,mark,(wave.execution.append source.execution).append mark.execution,rfl⟩⟩

namespace ConstructedCadenceFirstMarkReturn
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward)

noncomputable abbrev final : Snapshot 3 := c.mark.final

theorem date : c.final.time = 660 := c.mark.date

theorem pending : c.final.pending = sourceTrain 2 0 664 4 19 := c.mark.pending

theorem pending_length : c.final.pending.length = 19 := by
  rw [c.pending]
  simp only [sourceTrain,List.length_ofFn]

theorem complete : CompleteThrough c.execution (660 : ℝ) := by
  simpa only [CompleteThrough] using c.mark.complete

theorem emissions : c.execution.ledger.emissions = c.wave.execution.ledger.emissions := by
  rw [c.reconstruct,Execution.emissions_append,Execution.emissions_append,
    c.source.emissions,c.mark.emissions,List.append_nil,List.append_nil]

theorem emission_times (i : Fin 3) :
    c.execution.emissionTimes i = c.wave.execution.emissionTimes i := by
  simp only [Execution.emissionTimes,c.emissions]

theorem a_emission_count :
    (c.wave.cadence.teaching.reverse.staged.before.emissionTimes 0 ++
      c.wave.cadence.teaching.reverse.staged.after.emissionTimes 0).length +
      (c.wave.cadence.teaching.staged.before.emissionTimes 0).length +
      (c.wave.cadence.teaching.staged.after.emissionTimes 0).length +
      (c.execution.emissionTimes 0).length = 39 := by
  rw [c.emission_times]
  exact c.wave.a_emission_count

theorem b_emission_count : (c.wave.cadence.teaching.reverse.staged.after.emissionTimes 1).length +
    (c.wave.cadence.teaching.staged.before.emissionTimes 1).length +
    (c.wave.cadence.teaching.staged.after.emissionTimes 1).length +
    (c.execution.emissionTimes 1).length = 44 := by
  rw [c.emission_times]
  exact c.wave.b_emission_count

theorem c_emission_count : (c.wave.cadence.teaching.staged.after.emissionTimes 2).length +
    (c.execution.emissionTimes 2).length = 15 := by
  rw [c.emission_times]
  exact c.wave.c_emission_count

theorem gains (i : Fin 3) (q : Port) : c.final.x i (.z q) = c.wave.final.x i (.z q) := by
  rw [c.mark.gains,c.source.gains]

theorem c_gain_own : c.final.x 2 (.z 0) = newbornC.x (.z 0) + 9 / 5 := by
  rw [c.gains,c.wave.c_gain_own]

theorem c_recovery_own : c.final.x 2 .b = newbornC.x .b + 1 / 5 := by
  rw [c.mark.c_recovery_gain,c.source.recovery,c.wave.recovery,
    c.wave.cadence.teaching.c_recovery]
  ring

end ConstructedCadenceFirstMarkReturn
end KernelR.Hybrid
