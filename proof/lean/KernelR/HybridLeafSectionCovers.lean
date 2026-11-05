import KernelR.HybridCadenceTailSectionCovers
import KernelR.HybridCadenceSectionCovers
import KernelR.HybridConstructedCadenceLeafK
import KernelR.HybridCompleteSectionCovers

/-! Complete section covers for the constructed leaf's genuine FAST trace.
The four components are the first source, three weak cycles, first protected
MARK response, and mixed/high tail. No active cover follows from a dose total. -/
namespace KernelR.Hybrid

private theorem leafGatesFour {θ s a b c u}
    (e₀ : @Execution 1 θ (fun _ _ => []) s a)
    (e₁ : Execution θ (fun _ _ => []) a b)
    (e₂ : Execution θ (fun _ _ => []) b c)
    (e₃ : Execution θ (fun _ _ => []) c u) :
    LearningGatesOpen (e₀.append (e₁.append (e₂.append e₃))) ↔
      LearningGatesOpen e₀ ∧ LearningGatesOpen e₁ ∧
        LearningGatesOpen e₂ ∧ LearningGatesOpen e₃ := by
  rw [learningGatesOpen_append, learningGatesOpen_append, learningGatesOpen_append]

theorem ConstructedCadenceLeafFirstMarkK.section_covers {θ ε s p K}
    {warmup : ConstructedCadenceWeakWarmupK θ (fun _ _ => []) s p K}
    (c : ConstructedCadenceLeafFirstMarkK warmup) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen c.execution) (q : Port) :
    Nonempty (ErrorSectionCover 0 q c.execution) ∧
      Nonempty (MarkSectionCover 0 q c.execution) := by
  constructor
  · obtain ⟨cover, _⟩ := c.execution.error_cover_of_zero_open box gates 0 q (c.error_zero q)
    exact ⟨cover⟩
  · rw [c.reconstruct, learningGatesOpen_append] at gates
    have unchanged : c.source.x 0 .b = warmup.final.x 0 .b := by
      rw [c.source_values]
      exact (c.span.recovery 0).trans ((c.fast.recovery 0).trans (c.fire.recovery_preserved 0))
    obtain ⟨head, _⟩ := c.strong.mark_cover_of_unchanged_recovery box gates.1 0 q unchanged
    have physical := c.strong.physical_invariant box warmup.physical
    have raw := c.strong.raw_valid warmup.raw_valid
    have active : c.source.raw 0 p = some c.source.time := by
      rw [c.source_state]
      simp [setRaw]
    have other : ∀ r, r ≠ p → c.source.raw 0 r = none := by
      intro r different
      rw [c.source_state]
      simp [setRaw, different, c.span.raw_none]
    have auxiliary : ∀ r, c.source.aux 0 r = .ready ∧ RestBand (c.source.x 0 (.m r)) := by
      intro r
      rw [c.source_state]
      exact ⟨c.span.auxiliary 0 r, c.span.rest r⟩
    obtain ⟨tail⟩ := c.mark.mark_section_covers box physical raw c.source_slow
      (by linarith [c.source_charge.1])
      (by have gain := c.mark.recovery_gain; linarith [c.mark.recovery_band.2])
      auxiliary active other (by rw [c.source_date]; linarith) gates.2 q
    rw [c.reconstruct]
    exact ⟨head.append tail⟩

theorem ConstructedCadenceLeafK.section_covers {θ ε s p start K terminal}
    (c : ConstructedCadenceLeafK θ s p start K terminal) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen c.execution) (q : Port) :
    Nonempty (ErrorSectionCover 0 q c.execution) ∧
      Nonempty (MarkSectionCover 0 q c.execution) := by
  have gates := (leafGatesFour c.firstSource.execution c.warmup.execution
    c.firstMark.execution c.tail.execution).mp (c.reconstruct ▸ gates)
  obtain ⟨e₁, _⟩ := c.firstSource.execution.error_cover_of_unchanged_gain box gates.1 0 q
    (c.firstSource.gains q)
  obtain ⟨m₁, _⟩ := c.firstSource.execution.mark_cover_of_unchanged_recovery box gates.1 0 q
    c.firstSource.recovery
  obtain ⟨⟨e₂⟩, ⟨m₂⟩⟩ := c.warmup.section_covers box gates.2.1 c.firstSource.raw_valid
    (by rw [c.firstSource.date]; exact c.firstSource.raw_active) q
  obtain ⟨⟨e₃⟩, ⟨m₃⟩⟩ := c.firstMark.section_covers box gates.2.2.1 q
  obtain ⟨⟨e₄⟩, ⟨m₄⟩⟩ := c.tail.section_covers box gates.2.2.2 q
  rw [c.reconstruct]
  exact ⟨⟨e₁.append (e₂.append (e₃.append e₄))⟩, ⟨m₁.append (m₂.append (m₃.append m₄))⟩⟩

theorem ConstructedCadenceLeafK.section_covered {θ ε s p start K terminal}
    (c : ConstructedCadenceLeafK θ s p start K terminal) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen c.execution) : c.execution.SectionCovered := by
  constructor
  · intro i q
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (c.section_covers box gates q).1
  · intro i q
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (c.section_covers box gates q).2

#print axioms ConstructedCadenceLeafK.section_covered
end KernelR.Hybrid
