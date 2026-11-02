import KernelR.HybridCadenceFirstWire

/-! The original birth, both independent teaching births, three actual
period-four weak inputs and the first cadence C-to-B wire receipt. -/
namespace KernelR.Hybrid

structure ConstructedCadenceFirstWire (θ : Fin 1 → Parameters) (born : Snapshot 1)
    (freshB freshC : Parameters) (newbornB newbornC : Newborn)
    (forward backward delay cascadeForward cascadeBackward : ℝ → ℝ) where
  teaching : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay
  warmup : ConstructedCadenceWarmup teaching cascadeForward cascadeBackward
  wire : FirstCadenceWire warmup
  execution : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) teaching.final wire.final
  reconstruct : execution = warmup.execution.append wire.execution

theorem birth_protocol_cadence_first_wire_exists {θ born freshB freshC ε}
    (hborn : @BirthState 1 born)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ q, born.aux 0 q = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newbornB newbornC : Newborn) (forward backward delay cascadeForward cascadeBackward : ℝ → ℝ)
    (hforward : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5)
    (hback : ∀ time, (3 / 10 : ℝ) ≤ backward time ∧ backward time ≤ 2 / 5)
    (hdelay : ∀ time, (3 / 10 : ℝ) ≤ delay time ∧ delay time ≤ 2 / 5)
    (hcascade : ∀ time, (3 / 10 : ℝ) ≤ cascadeForward time ∧ cascadeForward time ≤ 2 / 5) :
    Nonempty (ConstructedCadenceFirstWire θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward) := by
  obtain ⟨teaching⟩ := birth_protocol_c_teaching_exists hborn hb ha hqueue newbornB newbornC
    forward backward delay hforward hback hdelay
  obtain ⟨warmup⟩ := constructed_cadence_warmup_exists teaching hb cascadeForward cascadeBackward
  obtain ⟨wire⟩ := first_cadence_wire_exists warmup hb hcascade
  exact ⟨⟨teaching,warmup,wire,warmup.execution.append wire.execution,rfl⟩⟩

namespace ConstructedCadenceFirstWire
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  (c : ConstructedCadenceFirstWire θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward)

noncomputable abbrev final : Snapshot 3 := c.wire.final

theorem window : 6527 / 10 < c.final.time ∧ c.final.time < 6533 / 10 := c.wire.window

theorem pending : c.final.pending = sourceTrain 2 0 656 4 21 := c.wire.pending

theorem pending_length : c.final.pending.length = 21 := by
  rw [c.pending]
  simp only [sourceTrain,List.length_ofFn]

theorem complete : CompleteThrough c.execution c.final.time := by
  simpa only [CompleteThrough] using c.wire.complete

theorem emissions : c.execution.ledger.emissions = [(2,c.wire.fire.final.time)] := by
  rw [c.reconstruct,Execution.emissions_append,c.warmup.emissions,c.wire.emissions,List.nil_append]

theorem emission_times_a : c.execution.emissionTimes 0 = [] := by
  simp [Execution.emissionTimes,c.emissions]

theorem emission_times_b : c.execution.emissionTimes 1 = [] := by
  simp [Execution.emissionTimes,c.emissions]

theorem emission_times_c : c.execution.emissionTimes 2 = [c.wire.fire.final.time] := by
  simp [Execution.emissionTimes,c.emissions]

theorem a_emission_count :
    (c.teaching.reverse.staged.before.emissionTimes 0 ++ c.teaching.reverse.staged.after.emissionTimes 0).length +
      (c.teaching.staged.before.emissionTimes 0).length +
      (c.teaching.staged.after.emissionTimes 0).length + (c.execution.emissionTimes 0).length = 38 := by
  rw [c.emission_times_a,List.length_nil,Nat.add_zero]
  exact c.teaching.a_emission_count

theorem b_emission_count : (c.teaching.reverse.staged.after.emissionTimes 1).length +
    (c.teaching.staged.before.emissionTimes 1).length +
    (c.teaching.staged.after.emissionTimes 1).length + (c.execution.emissionTimes 1).length = 43 := by
  rw [c.emission_times_b,List.length_nil,Nat.add_zero]
  exact c.teaching.b_emission_count

theorem c_emission_count : (c.teaching.staged.after.emissionTimes 2).length +
    (c.execution.emissionTimes 2).length = 15 := by
  rw [c.emission_times_c,List.length_singleton,c.teaching.c_emission_count]

theorem c_gain_own : c.final.x 2 (.z 0) = newbornC.x (.z 0) + 9 / 5 := by
  rw [c.wire.gains,c.warmup.c_gain_target,c.teaching.c_gain_other 0 (by decide)]

theorem gain_other (i : Fin 3) (q : Port) (h : i ≠ 2 ∨ q ≠ 0) :
    c.final.x i (.z q) = c.teaching.final.x i (.z q) := by
  rw [c.wire.gains,c.warmup.gains_other i q h]

theorem recovery (i : Fin 3) : c.final.x i .b = c.teaching.final.x i .b := by
  rw [c.wire.recovery,c.warmup.recovery]

theorem raw_receiver : c.final.raw 1 2 = some c.final.time := c.wire.b_raw_active

theorem a_prepared : PreparedSection c.final 0 := c.wire.a_prepared

theorem b_prepared : PreparedSection c.final 1 := c.wire.b_prepared

end ConstructedCadenceFirstWire
end KernelR.Hybrid
