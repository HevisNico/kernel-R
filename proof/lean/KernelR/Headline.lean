import KernelR.HybridBirthCadenceProtocol

/-! Public N=3 headline statements. Fabrication parameters are fixed functions
of the cell index, not of time. The factory quantifies universally over its
admissible data and returns an existential execution witness. It does not
assert that all admissible executions refine this witness. -/
namespace KernelR.Hybrid.Headline

theorem three_cell_protocol_exists {θ born freshB freshC ε}
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
  exact birth_protocol_complete_cadence_exists hborn hb ha hqueue newbornB newbornC
    forward backward delay cascadeForward cascadeBackward hforward hback hdelay
    hcascadeForward hcascadeBackward

variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  (c : ConstructedBirthCadenceProtocol θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward)

/-- A's actual FIRE count, across both dimension-changing births. -/
noncomputable def aCount : ℕ :=
  (c.cadence.entry.wave.cadence.teaching.reverse.staged.before.emissionTimes 0 ++
    c.cadence.entry.wave.cadence.teaching.reverse.staged.after.emissionTimes 0).length +
    (c.staged.before.emissionTimes 0).length + (c.staged.after.emissionTimes 0).length

/-- B's actual FIRE count, starting at B's genuine birth. -/
noncomputable def bCount : ℕ :=
  (c.cadence.entry.wave.cadence.teaching.reverse.staged.after.emissionTimes 1).length +
    (c.staged.before.emissionTimes 1).length + (c.staged.after.emissionTimes 1).length

/-- C's actual FIRE count, starting at C's genuine birth. -/
noncomputable def cCount : ℕ := (c.staged.after.emissionTimes 2).length

theorem terminal_state_and_counts :
    c.final.time = (7899 : ℝ) / 10 ∧
    (∀ i : Fin 3, ReadyCoordinates c.final i) ∧
    (∀ i : Fin 3, c.final.x i .q = 1 / 10) ∧
    (∀ (i : Fin 3) (p : Port), c.final.raw i p = none) ∧
    c.final.pending = [] ∧ aCount c = 54 ∧ bCount c = 61 ∧ cCount c = 34 := by
  exact ⟨c.date, c.ready, c.charge, c.raw_none, c.pending,
    c.a_emission_count, c.b_emission_count, c.c_emission_count⟩

theorem learned_memories :
    c.final.x 0 (.z 2) = born.x 0 (.z 2) + 12 / 5 ∧
    c.final.x 1 (.z 2) = newbornB.x (.z 2) + 12 / 5 ∧
    c.final.x 2 (.z 0) = newbornC.x (.z 0) + 12 / 5 ∧
    c.final.x 0 .b = born.x 0 .b + 3 / 10 ∧
    c.final.x 1 .b = newbornB.x .b + 3 / 10 ∧
    c.final.x 2 .b = newbornC.x .b + 3 / 10 := by
  exact ⟨c.cadence.a_gain_own, c.cadence.b_gain_own, c.cadence.c_gain_own,
    c.cadence.a_recovery_own, c.cadence.b_recovery_own, c.cadence.c_recovery_own⟩

#print axioms three_cell_protocol_exists
#print axioms terminal_state_and_counts
#print axioms learned_memories

end KernelR.Hybrid.Headline
