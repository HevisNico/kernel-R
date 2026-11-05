import KernelR.HybridCompleteSectionCovers
import KernelR.HybridFiniteCausalExtension

/-! Complete learning sections survive the actual finite causal extension.
The proof transports open-section runs, then reconstructs covers of the
returned global execution. No endpoint memory equality supplies a cover. -/
namespace KernelR.Hybrid

theorem FiniteCausalExtension.sectionCovered
    {d : FiniteCausalChainData} {T : ℝ} {n : ℕ}
    {stage : FiniteCausalChainStage d T n}
    {head : FiniteCausalCell (d.headParameters n) stage.nextSource T}
    (extension : FiniteCausalExtension stage head)
    (old : stage.execution.SectionCovered) (newHead : head.execution.SectionCovered) :
    extension.next.execution.SectionCovered := by
  constructor
  · intro i p
    cases i using Fin.cases with
    | zero =>
      obtain ⟨cover⟩ := newHead.1 0 p
      obtain ⟨mapped, _⟩ := error_section_run_iff.mp
        (extension.head_sections .error p false false cover.count cover.sectionRun)
      exact ⟨mapped⟩
    | succ i =>
      obtain ⟨cover⟩ := old.1 i p
      obtain ⟨mapped, _⟩ := error_section_run_iff.mp
        (extension.tail_sections .error i p false false cover.count cover.sectionRun)
      exact ⟨mapped⟩
  · intro i p
    cases i using Fin.cases with
    | zero =>
      obtain ⟨cover⟩ := newHead.2 0 p
      obtain ⟨mapped, _⟩ := mark_section_run_iff.mp
        (extension.head_sections .mark p false false cover.count cover.sectionRun)
      exact ⟨mapped⟩
    | succ i =>
      obtain ⟨cover⟩ := old.2 i p
      obtain ⟨mapped, _⟩ := mark_section_run_iff.mp
        (extension.tail_sections .mark i p false false cover.count cover.sectionRun)
      exact ⟨mapped⟩

/-- Terminal headroom of the actual combined execution supplies the matching
headroom obligations for both retained component executions. -/
theorem FiniteCausalExtension.sectionCovered_of_headroom
    {d : FiniteCausalChainData} {T : ℝ} {n : ℕ}
    {stage : FiniteCausalChainStage d T n}
    {head : FiniteCausalCell (d.headParameters n) stage.nextSource T}
    (extension : FiniteCausalExtension stage head)
    (old : (∀ i p, stage.final.x i (.z p) < Real.log ((d.parameters n i).cap p)) →
      (∀ i, stage.final.x i .b < 11 / 10) → stage.execution.SectionCovered)
    (newHead : (∀ p, head.final.x 0 (.z p) < Real.log ((d.headParameters n).cap p)) →
      head.final.x 0 .b < 11 / 10 → head.execution.SectionCovered)
    (gain : ∀ i p, extension.next.final.x i (.z p) <
      Real.log ((d.parameters (n + 1) i).cap p))
    (recovery : ∀ i, extension.next.final.x i .b < 11 / 10) :
    extension.next.execution.SectionCovered := by
  apply extension.sectionCovered
  · apply old
    · intro i p
      have h := gain i.succ p
      change extension.next.final.x i.succ (.z p) <
        Real.log ((d.parameters n i).cap p) at h
      rw [extension.tail_values] at h
      exact h
    · intro i
      have h := recovery i.succ
      rw [extension.tail_values] at h
      exact h
  · apply newHead
    · intro p
      have h := gain 0 p
      change extension.next.final.x 0 (.z p) <
        Real.log ((d.headParameters n).cap p) at h
      rw [extension.head_values] at h
      exact h
    · have h := recovery 0
      rw [extension.head_values] at h
      exact h

/-- The stage's actual retained local executions suffice, independently of
the construction's endpoint formulas or output calendars. -/
theorem FiniteCausalChainStage.sectionCovered_of_cells
    {d : FiniteCausalChainData} {T : ℝ} {n : ℕ}
    (stage : FiniteCausalChainStage d T n)
    (locals : ∀ i, (stage.cells i).2.execution.SectionCovered) :
    stage.execution.SectionCovered := by
  constructor
  · intro i p
    obtain ⟨cover⟩ := (locals i).1 0 p
    obtain ⟨mapped, _⟩ := error_section_run_iff.mp
      (stage.section_runs .error i p false false cover.count cover.sectionRun)
    exact ⟨mapped⟩
  · intro i p
    obtain ⟨cover⟩ := (locals i).2 0 p
    obtain ⟨mapped, _⟩ := mark_section_run_iff.mp
      (stage.section_runs .mark i p false false cover.count cover.sectionRun)
    exact ⟨mapped⟩

end KernelR.Hybrid
