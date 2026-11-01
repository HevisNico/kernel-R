import KernelR.HybridBirthCadenceFirstWire
import KernelR.HybridCadenceFirstAFire

/-! Original birth through the first genuine cadence wave C→B→A. The
unfinished physical paths of all three cells remain in the witness. -/
namespace KernelR.Hybrid

structure ConstructedCadenceFirstWave (θ : Fin 1 → Parameters) (born : Snapshot 1)
    (freshB freshC : Parameters) (newbornB newbornC : Newborn)
    (forward backward delay cascadeForward cascadeBackward : ℝ → ℝ) where
  cadence : ConstructedCadenceFirstWire θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward
  relay : FirstCadenceRelayWire cadence.wire
  firstA : FirstCadenceAFire relay
  execution : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) cadence.teaching.final firstA.final
  reconstruct : execution = (cadence.execution.append relay.execution).append firstA.execution

theorem birth_protocol_cadence_first_wave_exists {θ born freshB freshC ε}
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
    Nonempty (ConstructedCadenceFirstWave θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward) := by
  obtain ⟨cadence⟩ := birth_protocol_cadence_first_wire_exists hborn hb ha hqueue newbornB newbornC
    forward backward delay cascadeForward cascadeBackward hforward hback hdelay hcascadeForward
  obtain ⟨relay⟩ := first_cadence_relay_wire_exists cadence.wire hb hcascadeBackward
  obtain ⟨firstA⟩ := first_cadence_a_fire_exists relay hb hborn
  exact ⟨⟨cadence,relay,firstA,(cadence.execution.append relay.execution).append firstA.execution,rfl⟩⟩

namespace ConstructedCadenceFirstWave
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  (c : ConstructedCadenceFirstWave θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward)

noncomputable abbrev final : Snapshot 3 := c.firstA.final

theorem window : 6538 / 10 < c.final.time ∧ c.final.time < 6551 / 10 := c.firstA.window

theorem pending : c.final.pending = sourceTrain 2 0 656 4 21 := c.firstA.pending

theorem pending_length : c.final.pending.length = 21 := by
  rw [c.pending]
  simp only [sourceTrain,List.length_ofFn]

theorem complete : CompleteThrough c.execution c.final.time := by
  simpa only [CompleteThrough] using c.firstA.complete

theorem emissions : c.execution.ledger.emissions =
    [(2,c.cadence.wire.fire.final.time),(1,c.relay.senderCycle.fire.final.time),
      (0,c.firstA.localCycle.fire.final.time)] := by
  rw [c.reconstruct,Execution.emissions_append,Execution.emissions_append,
    c.cadence.emissions,c.relay.emissions,c.firstA.emissions]
  rfl

theorem emission_times_a : c.execution.emissionTimes 0 = [c.firstA.localCycle.fire.final.time] := by
  simp [Execution.emissionTimes,c.emissions]

theorem emission_times_b : c.execution.emissionTimes 1 = [c.relay.senderCycle.fire.final.time] := by
  simp [Execution.emissionTimes,c.emissions]

theorem emission_times_c : c.execution.emissionTimes 2 = [c.cadence.wire.fire.final.time] := by
  simp [Execution.emissionTimes,c.emissions]

theorem a_emission_count :
    (c.cadence.teaching.reverse.staged.before.emissionTimes 0 ++
      c.cadence.teaching.reverse.staged.after.emissionTimes 0).length +
      (c.cadence.teaching.staged.before.emissionTimes 0).length +
      (c.cadence.teaching.staged.after.emissionTimes 0).length +
      (c.execution.emissionTimes 0).length = 39 := by
  rw [c.emission_times_a,List.length_singleton,c.cadence.teaching.a_emission_count]

theorem b_emission_count : (c.cadence.teaching.reverse.staged.after.emissionTimes 1).length +
    (c.cadence.teaching.staged.before.emissionTimes 1).length +
    (c.cadence.teaching.staged.after.emissionTimes 1).length +
    (c.execution.emissionTimes 1).length = 44 := by
  rw [c.emission_times_b,List.length_singleton,c.cadence.teaching.b_emission_count]

theorem c_emission_count : (c.cadence.teaching.staged.after.emissionTimes 2).length +
    (c.execution.emissionTimes 2).length = 15 := by
  rw [c.emission_times_c,List.length_singleton,c.cadence.teaching.c_emission_count]

theorem gains (i : Fin 3) (q : Port) :
    c.final.x i (.z q) = c.cadence.final.x i (.z q) := by
  rw [c.firstA.gains,c.relay.gains]

theorem recovery (i : Fin 3) : c.final.x i .b = c.cadence.teaching.final.x i .b := by
  rw [c.firstA.recovery,c.relay.recovery,c.cadence.recovery]

theorem c_gain_own : c.final.x 2 (.z 0) = newbornC.x (.z 0) + 9 / 5 := by
  rw [c.gains,c.cadence.c_gain_own]

end ConstructedCadenceFirstWave
end KernelR.Hybrid
