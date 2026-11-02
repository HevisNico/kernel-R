import KernelR.HybridBirthCadenceCascade
import KernelR.HybridTeachingCadenceRouter

/-! The original two genuine births and one fixed gated three-cell routing
law reach789.9. Retargeting and concatenation keep the complete physical
ledgers, including all actual issued and consumed wire occurrences. -/
namespace KernelR.Hybrid

structure ConstructedBirthCadenceProtocol (θ : Fin 1 → Parameters) (born : Snapshot 1)
    (freshB freshC : Parameters) (newbornB newbornC : Newborn)
    (forward backward delay cascadeForward cascadeBackward : ℝ → ℝ) where
  cadence : ConstructedBirthCadence θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward
  staged : StagedExecution (extendParameters θ freshB) freshC
    (reciprocalEntryRouter forward backward) (teachingCadenceRouter delay cascadeForward cascadeBackward)
    cadence.entry.wave.cadence.teaching.reverse.final cadence.final
  before_eq : HEq staged.before cadence.entry.wave.cadence.teaching.staged.before
  birth_eq : HEq staged.birth cadence.entry.wave.cadence.teaching.staged.birth
  before_times : ∀ i, staged.before.emissionTimes i =
    cadence.entry.wave.cadence.teaching.staged.before.emissionTimes i
  after_ledger : staged.after.ledger = cadence.entry.wave.cadence.teaching.staged.after.ledger.add
    cadence.execution.ledger
  after_deliveries : staged.after.deliveries =
    cadence.entry.wave.cadence.teaching.staged.after.deliveries ++ cadence.execution.deliveries
  after_times : ∀ i, staged.after.emissionTimes i =
    cadence.entry.wave.cadence.teaching.staged.after.emissionTimes i ++ cadence.execution.emissionTimes i
  complete : CompleteThrough staged.after (7899 / 10)

theorem ConstructedBirthCadence.protocol_exists
    {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (c : ConstructedBirthCadence θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward) :
    Nonempty (ConstructedBirthCadenceProtocol θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward) := by
  have hOld : c.entry.wave.cadence.teaching.final.time < (640 : ℝ) := by
    rw [c.entry.wave.cadence.teaching.date]
    norm_num
  have hNew : (630 : ℝ) ≤ c.entry.wave.cadence.teaching.final.time := by
    rw [c.entry.wave.cadence.teaching.date]
    norm_num
  obtain ⟨after,hLedger,hDeliveries,hComplete⟩ := teaching_cadence_append_exists delay
    cascadeForward cascadeBackward c.entry.wave.cadence.teaching.staged.after c.execution hOld hNew c.complete
  let staged : StagedExecution (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (teachingCadenceRouter delay cascadeForward cascadeBackward)
      c.entry.wave.cadence.teaching.reverse.final c.final := {
    beforeBirth := c.entry.wave.cadence.teaching.staged.beforeBirth
    afterBirth := c.entry.wave.cadence.teaching.staged.afterBirth
    before := c.entry.wave.cadence.teaching.staged.before
    birth := c.entry.wave.cadence.teaching.staged.birth
    after := after
  }
  refine ⟨{
    cadence := c, staged := staged, before_eq := HEq.rfl, birth_eq := HEq.rfl
    before_times := fun _ => rfl, after_ledger := hLedger, after_deliveries := hDeliveries
    after_times := ?_, complete := hComplete
  }⟩
  intro i
  change after.emissionTimes i = _
  simp only [Execution.emissionTimes,hLedger,Ledger.add,List.filter_append,List.map_append]

theorem birth_protocol_complete_cadence_exists {θ born freshB freshC ε}
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
    Nonempty (ConstructedBirthCadenceProtocol θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward) := by
  obtain ⟨c⟩ := birth_protocol_cadence_cascade_exists hborn hb ha hqueue newbornB newbornC
    forward backward delay cascadeForward cascadeBackward hforward hback hdelay
    hcascadeForward hcascadeBackward
  exact c.protocol_exists

namespace ConstructedBirthCadenceProtocol
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  (c : ConstructedBirthCadenceProtocol θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward)

noncomputable abbrev final : Snapshot 3 := c.cadence.final

noncomputable def betweenBirths : Execution (extendParameters θ freshB)
    (reciprocalEntryRouter forward backward)
    c.cadence.entry.wave.cadence.teaching.reverse.staged.afterBirth c.staged.beforeBirth :=
  c.cadence.entry.wave.cadence.teaching.reverse.staged.after.append c.staged.before

theorem date : c.final.time = 7899 / 10 := c.cadence.date

theorem pending : c.final.pending = [] := c.cadence.pending

theorem ready (i : Fin 3) : ReadyCoordinates c.final i := c.cadence.ready i

theorem charge (i : Fin 3) : c.final.x i .q = 1 / 10 := c.cadence.charge i

theorem raw_none (i : Fin 3) (q : Port) : c.final.raw i q = none := c.cadence.raw_none i q

theorem a_emission_count :
    (c.cadence.entry.wave.cadence.teaching.reverse.staged.before.emissionTimes 0 ++
      c.cadence.entry.wave.cadence.teaching.reverse.staged.after.emissionTimes 0).length +
      (c.staged.before.emissionTimes 0).length + (c.staged.after.emissionTimes 0).length = 54 := by
  rw [c.before_times,c.after_times,List.length_append]
  have h := c.cadence.a_emission_count
  simp only [List.length_append] at h ⊢
  omega

theorem b_emission_count :
    (c.cadence.entry.wave.cadence.teaching.reverse.staged.after.emissionTimes 1).length +
      (c.staged.before.emissionTimes 1).length + (c.staged.after.emissionTimes 1).length = 61 := by
  rw [c.before_times,c.after_times,List.length_append]
  have h := c.cadence.b_emission_count
  omega

theorem c_emission_count : (c.staged.after.emissionTimes 2).length = 34 := by
  rw [c.after_times,List.length_append]
  exact c.cadence.c_emission_count

end ConstructedBirthCadenceProtocol
end KernelR.Hybrid
