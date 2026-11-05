import KernelR.HybridInactiveSectionCovers

/-! Extend actual complete-section covers across physically inactive context.
Nonnegative actuation and open gates establish the structural inactivity of
the context; the counted middle must already have a real section cover. -/
namespace KernelR.Hybrid

theorem Execution.error_cover_splice {n θ ε route s a b u}
    (before : @Execution n θ route s a) (middle : Execution θ route a b)
    (after : Execution θ route b u) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen (before.append (middle.append after)))
    (i : Fin n) (p : Port) (cover : ErrorSectionCover i p middle)
    (dose : (before.append (middle.append after)).ledger.error i p = middle.ledger.error i p) :
    Nonempty (ErrorSectionCover i p (before.append (middle.append after))) := by
  have split := (Execution.allFlows_append before (middle.append after) _).mp gates
  have tail := (Execution.allFlows_append middle after _).mp split.2
  have nonnegBefore := before.section_error_nonnegative box i p
  have nonnegAfter := after.section_error_nonnegative box i p
  have balance : before.ledger.error i p + (middle.ledger.error i p + after.ledger.error i p) =
      middle.ledger.error i p := by simpa only [Execution.dose_error_append, Execution.dose_mark_append] using dose
  obtain ⟨left, _⟩ := before.error_cover_of_zero_open box split.1 i p (by linarith)
  obtain ⟨right, _⟩ := after.error_cover_of_zero_open box tail.2 i p (by linarith)
  exact ⟨left.append (cover.append right)⟩

theorem Execution.mark_cover_splice {n θ ε route s a b u}
    (before : @Execution n θ route s a) (middle : Execution θ route a b)
    (after : Execution θ route b u) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen (before.append (middle.append after)))
    (i : Fin n) (p : Port) (cover : MarkSectionCover i p middle)
    (dose : (before.append (middle.append after)).ledger.mark i p = middle.ledger.mark i p) :
    Nonempty (MarkSectionCover i p (before.append (middle.append after))) := by
  have split := (Execution.allFlows_append before (middle.append after) _).mp gates
  have tail := (Execution.allFlows_append middle after _).mp split.2
  have nonnegBefore := before.section_mark_nonnegative box i p
  have nonnegAfter := after.section_mark_nonnegative box i p
  have balance : before.ledger.mark i p + (middle.ledger.mark i p + after.ledger.mark i p) =
      middle.ledger.mark i p := by simpa only [Execution.dose_error_append, Execution.dose_mark_append] using dose
  obtain ⟨left, _⟩ := before.mark_cover_of_zero_open box split.1 i p (by linarith)
  obtain ⟨right, _⟩ := after.mark_cover_of_zero_open box tail.2 i p (by linarith)
  exact ⟨left.append (cover.append right)⟩

#print axioms Execution.error_cover_splice
#print axioms Execution.mark_cover_splice

end KernelR.Hybrid
