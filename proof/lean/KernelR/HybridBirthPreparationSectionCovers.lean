import KernelR.HybridBirthPreparationExists
import KernelR.HybridCompleteSectionCovers
import KernelR.HybridUniformSectionCovers
import KernelR.HybridSectionCoverSplice
import KernelR.HybridSectionGates

/-! Actual covers for the constructed low-port preparation. Its three weak
sections and protected MARK come from uniform physical mode traces; the
surrounding execution is proved structurally inactive using open gates. -/
namespace KernelR.Hybrid

private theorem append_seven {n θ route s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇}
    (e₀ : @Execution n θ route s₀ s₁) (e₁ : Execution θ route s₁ s₂)
    (e₂ : Execution θ route s₂ s₃) (e₃ : Execution θ route s₃ s₄)
    (e₄ : Execution θ route s₄ s₅) (e₅ : Execution θ route s₅ s₆)
    (e₆ : Execution θ route s₆ s₇) :
    ((((((e₀.append e₁).append e₂).append e₃).append e₄).append e₅).append e₆) =
      e₀.append (e₁.append (e₂.append (e₃.append (e₄.append (e₅.append e₆))))) := by
  simp only [Execution.append_assoc]

private theorem append_four {n θ route s₀ s₁ s₂ s₃ s₄}
    (e₀ : @Execution n θ route s₀ s₁) (e₁ : Execution θ route s₁ s₂)
    (e₂ : Execution θ route s₂ s₃) (e₃ : Execution θ route s₃ s₄) :
    ((e₀.append e₁).append e₂).append e₃ =
      e₀.append (e₁.append (e₂.append e₃)) := by
  simp only [Execution.append_assoc]

private theorem gates_three {n θ route s₀ s₁ s₂ s₃}
    (e₀ : @Execution n θ route s₀ s₁) (e₁ : Execution θ route s₁ s₂)
    (e₂ : Execution θ route s₂ s₃) :
    LearningGatesOpen (e₀.append (e₁.append e₂)) ↔
      LearningGatesOpen e₀ ∧ LearningGatesOpen e₁ ∧ LearningGatesOpen e₂ := by
  simp only [LearningGatesOpen, Execution.allFlows_append]

theorem ConstructedBirthPreparation.learning_gates_open {θ ε born}
    (c : ConstructedBirthPreparation θ born) (hb : PhysicalBox θ ε) :
    LearningGatesOpen c.execution := by
  obtain ⟨outcome⟩ := c.outcome hb
  have birth := c.at40.mark.first.weak.birth
  apply c.execution.learningGatesOpen_of_final_headroom hb (birth.physical_invariant hb)
  · intro i p
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hz := ((birth.2.2 0).2.2.2.2 p).1.2
    by_cases hp : p = 0
    · subst p
      rw [outcome.gain_target]
      norm_num [nominalGain] at hz
      linarith [hb.low_gain_headroom 0 0]
    · rw [outcome.gain_other p hp]
      have nom : 0 < nominalGain p ∧ nominalGain p ≤ 6/5 := by
        unfold nominalGain; split_ifs <;> norm_num
      have hlog := Real.log_le_log nom.1 nom.2
      linarith [hb.fast_nominal_headroom 0 p]
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [outcome.recovery_gain]
    linarith [(birth.2.2 0).2.2.1.2]

theorem ConstructedBirthPreparation.section_covered {θ ε born}
    (c : ConstructedBirthPreparation θ born) (hb : PhysicalBox θ ε) :
    c.execution.SectionCovered := by
  obtain ⟨outcome⟩ := c.outcome hb
  have gates := c.learning_gates_open hb
  let mark := c.at40.mark
  let weak := mark.first.weak
  let errorTail := mark.first.fire.execution.append
    (mark.fast.execution.append (mark.arrival.execution.append
      (mark.markTrace.append (c.at40.suffix.append c.suffix))))
  have errorTrace : c.execution = weak.execution.append errorTail :=
    append_seven weak.execution mark.first.fire.execution mark.fast.execution
      mark.arrival.execution mark.markTrace c.at40.suffix c.suffix
  let markBefore := (mark.first.execution.append mark.fast.execution).append mark.arrival.execution
  let markAfter := c.at40.suffix.append c.suffix
  have markTrace : c.execution = markBefore.append (mark.markTrace.append markAfter) :=
    append_four markBefore mark.markTrace c.at40.suffix c.suffix
  constructor
  · intro i p
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    by_cases hp : p = 0
    · subst p
      have split : LearningGatesOpen weak.execution ∧ LearningGatesOpen errorTail := by
        rw [errorTrace] at gates
        exact (Execution.allFlows_append _ _ _).mp gates
      obtain ⟨cover⟩ := weak.execution.error_cover_of_uniform_ready 0 0 split.1 weak.ready_flows
        (by rw [mark.initial_aux 0]; decide) (by rw [((weak.ready 0).auxiliary 0).1]; decide)
      have h := (Execution.nil born).error_cover_splice weak.execution errorTail hb
        (by simpa only [Execution.append, ← errorTrace] using gates) 0 0 cover
        (by simp only [Execution.append, ← errorTrace]; rw [outcome.error_target, weak.error_dose])
      simpa only [Execution.append, ← errorTrace] using h
    · obtain ⟨cover, _⟩ := c.execution.error_cover_of_zero_open hb gates 0 p
        (outcome.error_other p hp)
      exact ⟨cover⟩
  · intro i p
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    by_cases hp : p = 0
    · subst p
      have split : LearningGatesOpen markBefore ∧
          LearningGatesOpen mark.markTrace ∧ LearningGatesOpen markAfter :=
        (gates_three markBefore mark.markTrace markAfter).mp (markTrace ▸ gates)
      have slow := mark.markTrace.protected_flows_of_mainFlows 0 .slow
        (by decide) mark.mark.slow_flows
      obtain ⟨cover⟩ := mark.markTrace.mark_cover_of_uniform_protected 0 0 split.2.1 slow
        (fun h => (by decide : AuxMode.ready ≠ .mark) ((mark.mark.initial_aux 0).symm.trans h))
        (fun h => (by decide : AuxMode.silent ≠ .mark) (mark.mark.aux_silent.symm.trans h))
      rw [markTrace]
      apply markBefore.mark_cover_splice mark.markTrace markAfter hb
        (markTrace ▸ gates) 0 0 cover
      have total : (markBefore.append (mark.markTrace.append markAfter)).ledger.mark 0 0 = 1/10 :=
        (congrArg (fun e => e.ledger.mark 0 0) markTrace).symm.trans outcome.mark_target
      change (markBefore.append (mark.markTrace.append markAfter)).ledger.mark 0 0 =
        mark.mark.execution.ledger.mark 0 0
      rw [total]
      have balance := mark.mark.execution.recovery_balance 0
      have sum := mark.mark.execution.recovery_sum_marks 0
      have others : ∀ q, q ≠ 0 → mark.mark.execution.ledger.mark 0 q = 0 := by
        intro q hq
        have no : NoArrivalAt mark.mark.execution 0 q := by simp [NoArrivalAt, mark.mark.deliveries]
        have states := mark.mark.execution.aux_ready_without_input_band 0 q
          (mark.mark.initial_aux q) (mark.arrival.rest q).2
          (mark.arrival.raw_other q hq) no
        exact mark.mark.execution.mark_zero_aux 0 q .ready (by decide)
          (mark.mark.execution.allStates_aux_flows 0 q .ready states)
      have one : (∑ q : Port, mark.mark.execution.ledger.mark 0 q) =
          mark.mark.execution.ledger.mark 0 0 :=
        Finset.sum_eq_single 0 (fun q _ hq => others q hq) (by simp)
      rw [one] at sum
      rw [mark.mark.recovery_gain] at balance
      linarith
    · obtain ⟨cover, _⟩ := c.execution.mark_cover_of_zero_open hb gates 0 p
        (outcome.mark_other p hp)
      exact ⟨cover⟩

#print axioms ConstructedBirthPreparation.section_covered

end KernelR.Hybrid
