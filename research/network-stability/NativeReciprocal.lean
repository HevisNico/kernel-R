import KernelR.HybridBirthReverseTeaching
import KernelR.HybridUniversalExecution
import KernelR.FutureControls

namespace NetworkStability.NativeReciprocal

open KernelR.Hybrid

/-- Each direction of the router is enabled at a time in its own gate. -/
theorem reciprocal_edges (forward backward : ℝ → ℝ) :
    (∃ d ∈ reciprocalEntryRouter forward backward 0 160, d.cell = 1) ∧
    (∃ d ∈ reciprocalEntryRouter forward backward 1 320, d.cell = 0) := by
  classical
  constructor
  · refine ⟨(teachingContact forward).token 160, ?_, rfl⟩
    norm_num [reciprocalEntryRouter, Contact.route, teachingContact, feedbackContact]
  · refine ⟨(feedbackContact backward).token 320, ?_, rfl⟩
    norm_num [reciprocalEntryRouter, Contact.route, teachingContact, feedbackContact]

/-- Native two-cell staged protocol, observed at the end of reverse teaching.
Quantification over complete histories starts at the same post-birth snapshot
and uses the same router and parameters. -/
theorem reciprocal_epoch {θ born fresh ε}
    (hborn : @BirthState 1 born) (box : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ready : ∀ p, born.aux 0 p = .ready)
    (queue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hf : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5)
    (hb : ∀ time, (3 / 10 : ℝ) ≤ backward time ∧ backward time ≤ 2 / 5) :
    ∃ epoch : ConstructedReverseTeaching θ born fresh newborn forward backward,
      ∀ u (run : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward)
          epoch.staged.afterBirth u),
        CompleteThrough run (4599 / 10) →
          (∀ i, run.emissionTimes i = epoch.staged.after.emissionTimes i) ∧
          u.x 0 (.z 2) = born.x 0 (.z 2) + 9 / 5 ∧
          u.x 1 (.z 2) = newborn.x (.z 2) + 9 / 5 ∧
          u.x 0 .b = born.x 0 .b + 1 / 10 ∧
          u.x 1 .b = newborn.x .b + 1 / 10 := by
  obtain ⟨epoch⟩ := birth_protocol_reverse_teaching_exists hborn box ready queue newborn
    forward backward hf hb
  have initial := hborn.physical_invariant box.extend_old
  have afterBirth := epoch.staged.birth.physical_invariant box
    (epoch.staged.before.physical_invariant box.extend_old initial)
  refine ⟨epoch, fun u run complete => ?_⟩
  have eq := (run.observational_unique epoch.staged.after box afterBirth complete epoch.complete).1
  refine ⟨fun i => run.emissionTimes_unique epoch.staged.after box afterBirth complete epoch.complete i, ?_⟩
  rw [eq.values]
  exact ⟨epoch.a_gain_target, epoch.b_gain_target, epoch.a_recovery, epoch.b_recovery⟩

noncomputable def nominalStart : Snapshot 1 :=
  { Newborn.nominal.snapshot with
    pending := sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16 }

noncomputable def nominalDelay (_ : ℝ) : ℝ := 7 / 20

/-- Concrete witness with nominal parameters and both delays fixed at 7/20. -/
theorem nominal_reciprocal_epoch :
    ∃ epoch : ConstructedReverseTeaching KernelR.FutureControls.parameters nominalStart
        (KernelR.FutureControls.parameters 0) Newborn.nominal nominalDelay nominalDelay,
      CompleteThrough epoch.staged.after (4599 / 10) ∧
      epoch.final.x 0 (.z 2) = nominalStart.x 0 (.z 2) + 9 / 5 ∧
      epoch.final.x 1 (.z 2) = Newborn.nominal.x (.z 2) + 9 / 5 := by
  have born : BirthState nominalStart := Newborn.nominal_birth_state
  have box : PhysicalBox
      (extendParameters KernelR.FutureControls.parameters (KernelR.FutureControls.parameters 0))
      (1 / 10) := by
    refine ⟨KernelR.FutureControls.parameters_box.1, ?_⟩
    intro i p
    fin_cases i <;> exact KernelR.FutureControls.parameters_box.2 0 p
  have delay : ∀ t, (3 / 10 : ℝ) ≤ nominalDelay t ∧ nominalDelay t ≤ 2 / 5 := by
    intro t
    norm_num [nominalDelay]
  obtain ⟨epoch, _⟩ := reciprocal_epoch born box (fun _ => rfl) rfl Newborn.nominal
    nominalDelay nominalDelay delay delay
  exact ⟨epoch, epoch.complete, epoch.a_gain_target, epoch.b_gain_target⟩

end NetworkStability.NativeReciprocal
