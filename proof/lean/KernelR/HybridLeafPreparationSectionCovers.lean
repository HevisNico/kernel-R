import KernelR.HybridFiniteChainLeafPreparation
import KernelR.HybridCompleteSectionCovers
import KernelR.HybridUniformSectionCovers
import KernelR.HybridSectionCoverSplice
import KernelR.HybridProtocolMarkSectionCovers
import KernelR.HybridSectionGates

/-! Actual covers of the leaf's sixteen-source preparation. The weak ERROR
and protected MARK are reconstructed from their physical traces, then embedded
in the retained execution; open gates certify its remaining moves inactive. -/
namespace KernelR.Hybrid

theorem FiniteChainLeafPreparation.learning_gates_open {θ ε born future}
    (c : FiniteChainLeafPreparation θ born future) (hb : PhysicalBox θ ε)
    (hborn : BirthState born) : LearningGatesOpen c.execution := by
  apply c.execution.learningGatesOpen_of_final_headroom hb (hborn.physical_invariant hb)
  · intro i p
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hz := ((hborn.2.2 0).2.2.2.2 p).1.2
    have nominal : 0 < nominalGain p ∧ nominalGain p ≤ 6/5 := by
      unfold nominalGain
      split_ifs <;> norm_num
    have hlog := Real.log_le_log nominal.1 nominal.2
    have headroom := hb.fast_nominal_headroom 0 p
    by_cases hp : p = 1
    · subst p
      rw [c.gain_target]
      linarith
    · rw [c.gain_other p hp]
      linarith
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [c.recovery]
    linarith [(hborn.2.2 0).2.2.1.2]

theorem FiniteChainLeafPreparation.section_covered {θ ε born future}
    (c : FiniteChainLeafPreparation θ born future) (hb : PhysicalBox θ ε)
    (gates : LearningGatesOpen c.execution) (hborn : BirthState born)
    (ha : ∀ p, born.aux 0 p = .ready) : c.execution.SectionCovered := by
  let last := c.learnedPrefix.execution.append
    (c.lastCycle.execution.append (Execution.cons (.flow c.waitFlow) (Execution.nil _)))
  let errorBefore : Execution θ (fun _ _ => []) born _ :=
    Execution.cons (.jump c.firstArrival) (Execution.nil _)
  let errorAfter := c.source8.execution.append ((c.fire.execution.append c.fast.execution).append
    (c.slow16.execution.append (Execution.cons (.jump c.arrival16)
      (c.protectedCycle.execution.append (c.source24.execution.append last)))))
  have errorTrace : c.execution = errorBefore.append (c.weak.execution.append errorAfter) := by
    rw [c.reconstruct]
    simp only [errorBefore, errorAfter, last, Execution.append_assoc, Execution.append]
  let markBefore := (Execution.cons (.jump c.firstArrival) c.weak.execution).append
    (c.source8.execution.append ((c.fire.execution.append c.fast.execution).append
      (c.slow16.execution.append (Execution.cons (.jump c.arrival16) (Execution.nil _)))))
  let markAfter := c.source24.execution.append last
  have markTrace : c.execution = markBefore.append (c.protectedCycle.execution.append markAfter) := by
    rw [c.reconstruct]
    simp only [markBefore, markAfter, last, Execution.append_assoc, Execution.append]
  have mark_other (p : Port) (hp : p ≠ 1) : c.execution.ledger.mark 0 p = 0 := by
    have no : NoArrivalAt c.execution 0 p := by
      intro d hd
      rw [c.deliveries] at hd
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hd
      exact Or.inr (Ne.symm hp)
    have states := c.execution.aux_ready_without_input_band 0 p (ha p)
      ((hborn.ready_coordinates 0 ha).auxiliary p).2.2 (hborn.2.1 0 p) no
    exact c.execution.mark_zero_aux 0 p .ready (by decide)
      (c.execution.allStates_aux_flows 0 p .ready states)
  have mark_target : c.execution.ledger.mark 0 1 = 1/10 := by
    have balance := c.execution.recovery_balance 0
    rw [c.recovery, c.execution.recovery_sum_marks 0,
      Finset.sum_eq_single 1 (fun q _ hq => mark_other q hq) (by simp)] at balance
    linarith
  constructor
  · intro i p
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    by_cases hp : p = 1
    · subst p
      have split : LearningGatesOpen errorBefore ∧
          LearningGatesOpen c.weak.execution ∧ LearningGatesOpen errorAfter := by
        rw [errorTrace] at gates
        simpa only [LearningGatesOpen, Execution.allFlows_append] using gates
      obtain ⟨cover⟩ := c.weak.execution.error_cover_of_uniform_ready 0 1 split.2.1
        (c.weak.execution.allStates_main_flows 0 .ready c.weak.pulse.ready_states)
        (by change born.aux 0 1 ≠ .error; rw [ha]; decide)
        (by rw [(c.weak.pulse.coordinates.auxiliary 1).1]; decide)
      rw [errorTrace]
      apply errorBefore.error_cover_splice c.weak.execution errorAfter hb
        (errorTrace ▸ gates) 0 1 cover
      rw [← errorTrace]
      have whole := c.execution.gain_balance 0 1
      rw [c.gain_target] at whole
      rw [c.weak.pulse.error_dose]
      linarith
    · obtain ⟨cover, _⟩ := c.execution.error_cover_of_unchanged_gain hb gates 0 p
        (c.gain_other p hp)
      exact ⟨cover⟩
  · intro i p
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    by_cases hp : p = 1
    · subst p
      let arrived : Execution θ (fun _ _ => []) c.slow16.final _ :=
        Execution.cons (.jump c.arrival16) (Execution.nil _)
      have entry : MarkEntry
          (leafPreparationArrived c.slow16.final (sourceTrain 0 1 24 8 13 ++ future)) 0 := by
        refine ⟨c.slow16.main_slow, ?_, ?_, ?_⟩
        · have charge := c.slow16.near_charge (by rw [c.source8.date]; norm_num)
          change 7/50 ≤ c.slow16.final.x 0 .q ∧ c.slow16.final.x 0 .q ≤ 1/4
          constructor <;> linarith [charge.1, charge.2]
        · change 7999/100000 ≤ c.slow16.final.x 0 .b ∧ c.slow16.final.x 0 .b ≤ 8001/100000
          rw [c.slow16.recovery, c.fast.recovery, c.fire.recovery_preserved]
          exact c.slow16.initial_low_b
        · intro q
          exact ⟨c.slow16.auxiliary 0 q, c.slow16.rest q⟩
      obtain ⟨cover, _⟩ := c.protectedCycle.mark_section_cover hb
        (arrived.physical_invariant hb c.slow16.physical)
        (arrived.raw_valid c.slow16.raw_valid) entry
      rw [markTrace]
      apply markBefore.mark_cover_splice c.protectedCycle.execution markAfter hb
        (markTrace ▸ gates) 0 1 cover
      rw [← markTrace, mark_target, c.protectedCycle.mark_dose]
    · obtain ⟨cover, _⟩ := c.execution.mark_cover_of_zero_open hb gates 0 p (mark_other p hp)
      exact ⟨cover⟩

/-- The original physical birth hypotheses suffice; no cover or learning-gate
certificate is supplied by the caller. -/
theorem FiniteChainLeafPreparation.sectionCovered {θ ε born future}
    (c : FiniteChainLeafPreparation θ born future) (hb : PhysicalBox θ ε)
    (hborn : BirthState born) (ha : ∀ p, born.aux 0 p = .ready) :
    c.execution.SectionCovered :=
  c.section_covered hb (c.learning_gates_open hb hborn) hborn ha

#print axioms FiniteChainLeafPreparation.section_covered
#print axioms FiniteChainLeafPreparation.sectionCovered

end KernelR.Hybrid
