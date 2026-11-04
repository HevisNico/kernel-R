import KernelR.HybridWeakExecutionComparison

/-! A constructed transverse reference extends every finite weak prefix
from its actual endpoint. Completeness of that prefix is not assumed. -/
namespace KernelR.Hybrid
open Set

theorem WeakExecution.physical_invariant {n θ ε route s u}
    (execution : @WeakExecution n θ route s u) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) : PhysicalInvariant θ u := by
  induction execution with
  | nil => exact physical
  | @cons s a u move rest ih =>
    apply ih
    cases move with
    | flow flow => exact flow.physical_invariant box physical
    | jump jump =>
      exact (Execution.cons (.jump jump) (.nil a) : Execution θ route s a).physical_invariant box physical

/-- An arbitrary finite weak prefix can be completed by a strict transverse
history, using the constructed reference and no hypothesis on its outcome. -/
theorem WeakExecution.continue_to_transverse_complete {n θ ε route s u v T}
    (initialRun : @WeakExecution n θ route s u) (reference : Execution θ route s v)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (complete : CompleteThrough reference T) (positive : reference.ContactsTransversal)
    (before : u.time ≤ T) :
    ∃ w, ∃ tail : Execution θ route u w,
      CompleteThrough tail T ∧ tail.ContactsTransversal := by
  have all : ∀ count, ∀ {s u v}
      (initialRun : WeakExecution θ route s u) (reference : Execution θ route s v),
      initialRun.moveCount + reference.moveCount = count → PhysicalInvariant θ s →
      CompleteThrough reference T → reference.ContactsTransversal → u.time ≤ T →
      ∃ w, ∃ tail : Execution θ route u w,
        CompleteThrough tail T ∧ tail.ContactsTransversal := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
      intro s u v initialRun reference size physical complete positive before
      cases initialRun with
      | nil s => exact ⟨v, reference, complete, positive⟩
      | @cons s a u move rest =>
        have nextPhysical : PhysicalInvariant θ a :=
          (WeakExecution.cons move (.nil a) : WeakExecution θ route s a).physical_invariant box physical
        cases move with
        | jump jump =>
          obtain ⟨v', reference', _, complete', _, shorter, positive'⟩ :=
            reference.strip_initial_jump_transversal box complete positive jump
          have smaller : rest.moveCount + reference'.moveCount < count := by
            simp only [WeakExecution.moveCount] at size
            omega
          exact ih _ smaller rest reference' rfl nextPhysical complete' positive' before
        | flow weak =>
          cases reference with
          | nil s =>
            exact False.elim (by
              have later := rest.time_monotone
              have terminal := complete.1
              linarith [weak.positive])
          | @cons s b v move referenceRest =>
            cases move with
            | jump jump =>
              exact False.elim (weak.no_initial_transverse_jump b jump positive.1)
            | flow flow =>
              by_cases earlier : a.time < b.time
              · have same : a.ObservationalEq (flow.at a.time) := by
                  have h := flow.at_observational_unique_weak weak box physical
                    ⟨weak.positive.le, earlier.le⟩ ⟨weak.positive.le, le_rfl⟩
                  rw [weak.at_final] at h
                  exact h.symm
                let remaining : Execution θ route (flow.at a.time) v :=
                  .cons (.flow (flow.suffix weak.positive.le earlier)) referenceRest
                have remainingComplete : CompleteThrough remaining T := complete
                have remainingPositive : remaining.ContactsTransversal := positive
                obtain ⟨v'', reference'', observed, _, countEq, positive''⟩ :=
                  remaining.transport_observational_transversal same.symm remainingPositive
                have complete'' :=
                  completeThrough_of_observational remaining reference'' observed remainingComplete
                have smaller : rest.moveCount + reference''.moveCount < count := by
                  simp only [WeakExecution.moveCount, Execution.moveCount, remaining] at size countEq
                  omega
                exact ih _ smaller rest reference'' rfl nextPhysical complete'' positive'' before
              · by_cases equal : a.time = b.time
                · have same : a.ObservationalEq b :=
                    (flow.final_observational_unique_weak weak box physical equal.symm).symm
                  obtain ⟨v', reference', observed, _, countEq, positive'⟩ :=
                    referenceRest.transport_observational_transversal same.symm positive
                  have complete' :=
                    completeThrough_of_observational referenceRest reference' observed complete
                  have smaller : rest.moveCount + reference'.moveCount < count := by
                    simp only [WeakExecution.moveCount, Execution.moveCount] at size
                    omega
                  exact ih _ smaller rest reference' rfl nextPhysical complete' positive' before
                · have shorter : b.time < a.time :=
                    lt_of_le_of_ne (le_of_not_gt earlier) (Ne.symm equal)
                  have same : (weak.at b.time).ObservationalEq b := by
                    have h := flow.at_observational_unique_weak weak box physical
                      ⟨flow.positive.le, le_rfl⟩ ⟨flow.positive.le, shorter.le⟩
                    rw [flow.at_final] at h
                    exact h.symm
                  let remaining : WeakExecution θ route (weak.at b.time) u :=
                    .cons (.flow (weak.suffix flow.positive.le shorter)) rest
                  have atPhysical : PhysicalInvariant θ (weak.at b.time) :=
                    same.symm.physical_invariant
                      ((Execution.cons (.flow flow) (.nil b) : Execution θ route s b).physical_invariant box physical)
                  obtain ⟨v', reference', observed, _, countEq, positive'⟩ :=
                    referenceRest.transport_observational_transversal same.symm positive
                  have complete' :=
                    completeThrough_of_observational referenceRest reference' observed complete
                  have smaller : remaining.moveCount + reference'.moveCount < count := by
                    simp only [WeakExecution.moveCount, Execution.moveCount, remaining] at size countEq ⊢
                    omega
                  exact ih _ smaller remaining reference' rfl atPhysical complete' positive' before
  exact all _ initialRun reference rfl physical complete positive before

/-- The finite weak prefix itself need not be complete: appending the derived
continuation gives a complete weak execution at the chosen horizon. -/
theorem WeakExecution.extend_transverse_complete {n θ ε route s u v T}
    (initialRun : @WeakExecution n θ route s u) (reference : Execution θ route s v)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (complete : CompleteThrough reference T) (positive : reference.ContactsTransversal)
    (before : u.time ≤ T) :
    ∃ w, ∃ tail : Execution θ route u w,
      WeakCompleteThrough (initialRun.append tail.toWeak) T ∧ tail.ContactsTransversal := by
  obtain ⟨w, tail, hc, hp⟩ :=
    initialRun.continue_to_transverse_complete reference box physical complete positive before
  exact ⟨w, tail, hc.toWeak, hp⟩

#print axioms WeakExecution.continue_to_transverse_complete
#print axioms WeakExecution.extend_transverse_complete

end KernelR.Hybrid
