import KernelR.HybridBirthCadenceChain
import KernelR.HybridDoseCountingTools
import KernelR.HybridSectionGates

/-! Exact counts for the physical finite-chain witness. Count identification
is performed only after actual section covers have been constructed. -/
namespace KernelR.Hybrid

theorem ConstructedBirthCadenceChain.terminal_learning_headroom
    {n θ bornCells K sigma centre delay T ε}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (hb : PhysicalBox θ ε) :
    (∀ i p, c.final.x i (.z p) < Real.log ((θ i).cap p)) ∧
      ∀ i, c.final.x i .b < 11 / 10 := by
  constructor
  · intro i p
    have born := c.preparation.initial_birth i
    by_cases active : p = cadenceActivePort n i
    · subst p
      have nominal : nominalGain (cadenceActivePort n i) = 3 / 10 := by
        unfold cadenceActivePort
        split_ifs <;> norm_num [nominalGain]
      have hz := ((born.2.2 0).2.2.2.2 (cadenceActivePort n i)).1
      rw [nominal] at hz
      have hg := c.gain_target i
      have bounds := cadence_four_dose_gain_bounds
        (show Real.log (3 / 10) + 12 / 5 - 1 / 100000 ≤
            c.final.x i (.z (cadenceActivePort n i)) ∧
            c.final.x i (.z (cadenceActivePort n i)) ≤
              Real.log (3 / 10) + 12 / 5 + 1 / 100000 by
          constructor <;> linarith [hz.1, hz.2])
      have cap : (18 / 5 : ℝ) ≤ (θ i).cap (cadenceActivePort n i) := by
        have h := (hb.2 i (cadenceActivePort n i)).1.1
        linarith [hb.epsilon_bounds.2]
      apply Real.exp_lt_exp.mp
      rw [Real.exp_log (by linarith)]
      linarith [bounds.2]
    · rw [c.gain_other i p active]
      have nom : 0 < nominalGain p ∧ nominalGain p ≤ 6 / 5 := by
        unfold nominalGain
        split_ifs <;> norm_num
      have hz := ((born.2.2 0).2.2.2.2 p).1.2
      have hlog := Real.log_le_log nom.1 nom.2
      have headroom := hb.fast_nominal_headroom i p
      by_cases same : p = finiteChainPreparationPort n i
      · rw [same, c.preparation.gain_target]
        have leaf : i = Fin.last n := by
          by_contra h
          have hv : i.val ≠ n := fun hv => h (Fin.ext hv)
          apply active
          simp only [finiteChainPreparationPort, h, ite_false] at same
          simpa only [cadenceActivePort, hv, ite_false] using same
        have dose : finiteChainPreparationDose n i = 3 / 5 := by
          simp [finiteChainPreparationDose, leaf]
        rw [dose]
        rw [same] at hz hlog headroom
        linarith
      · rw [c.preparation.gain_other i p same]
        linarith
  · intro i
    rw [c.recovery]
    have h := (c.preparation.initial_birth i).2.2 0
    linarith [h.2.2.1.2]

theorem ConstructedBirthCadenceChain.learning_gates_open
    {n θ bornCells K sigma centre delay T ε}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (hb : PhysicalBox θ ε) : LearningGatesOpen c.execution := by
  have bounds := c.terminal_learning_headroom hb
  exact c.execution.learningGatesOpen_of_final_headroom hb
    (c.source_birth.physical_invariant hb) bounds.1 bounds.2

theorem ConstructedBirthCadenceChain.identify_section_counts
    {n θ bornCells K sigma centre delay T}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (errors : ∀ i p, ErrorSectionCover i p c.execution)
    (marks : ∀ i p, MarkSectionCover i p c.execution) :
    (∀ i, (errors i (cadenceActivePort n i)).count = 4) ∧
      ∀ i, (∑ p : Port, (marks i p).count) = 3 := by
  have memory := c.execution.memory_of_section_covers errors marks
  constructor
  · intro i
    have counted := memory.1 i (cadenceActivePort n i)
    rw [c.source_values] at counted
    have physical := c.gain_target i
    have exactCount : ((errors i (cadenceActivePort n i)).count : ℝ) = 4 := by
      linarith
    exact_mod_cast exactCount
  · intro i
    have counted := memory.2 i
    rw [c.source_values] at counted
    have physical := c.recovery i
    have exactCount : ((∑ p : Port, (marks i p).count : ℕ) : ℝ) = 3 := by
      linarith
    exact_mod_cast exactCount

/-- The constructed protocol has actual complete ERROR and protected MARK
covers. Its physical parameter box supplies all exposure obligations. -/
theorem ConstructedBirthCadenceChain.sectionCovered
    {n θ bornCells K sigma centre delay T ε}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (hb : PhysicalBox θ ε) : c.execution.SectionCovered := by
  have bounds := c.terminal_learning_headroom hb
  have prepared : c.preparedExecution.SectionCovered :=
    c.preparation.section_covered.of_runs id
      (fun kind i p count run => c.preparation_sections kind i p false false count run)
  have fast : c.fast.stage.execution.SectionCovered := by
    apply c.fast.section_covered
    · intro i p
      rw [c.preparation.cadence_parameters_full]
      exact bounds.1 i p
    · exact bounds.2
  have lifted : c.fastExecution.SectionCovered :=
    fast.of_runs id (fun kind i p count run => c.fast_sections kind i p false false count run)
  rw [c.reconstruct]
  exact prepared.append lifted

/-- On the finite-chain witness the active port has four complete ERROR
sections, and each cell has three complete protected MARK sections in total.
The covers are constructed before endpoint identities identify their counts. -/
theorem ConstructedBirthCadenceChain.exact_section_counts
    {n θ bornCells K sigma centre delay T ε}
    (c : @ConstructedBirthCadenceChain n θ bornCells K sigma centre delay T)
    (hb : PhysicalBox θ ε) :
    ∃ (errors : ∀ i p, ErrorSectionCover i p c.execution)
      (marks : ∀ i p, MarkSectionCover i p c.execution),
      (∀ i, (errors i (cadenceActivePort n i)).count = 4) ∧
        ∀ i, (∑ p : Port, (marks i p).count) = 3 := by
  classical
  have covered := c.sectionCovered hb
  let errors := fun i p => Classical.choice (covered.1 i p)
  let marks := fun i p => Classical.choice (covered.2 i p)
  exact ⟨errors, marks, c.identify_section_counts errors marks⟩

#print axioms ConstructedBirthCadenceChain.sectionCovered
#print axioms ConstructedBirthCadenceChain.exact_section_counts
#print axioms ConstructedBirthCadenceChain.learning_gates_open

end KernelR.Hybrid
