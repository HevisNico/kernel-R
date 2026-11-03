import KernelR.HybridUniversalExecution

/-!
# Finite progress relative to a constructed complete execution

The reference execution is an actual complete witness, not a caller-supplied
output calendar. The finite-chain existence theorem already constructs one.
Every competing finite execution ending by the same horizon can be continued
from its own actual final snapshot. No equality of pending-list presentations,
event priority, or completeness of the competing prefix is required.

This is finite-horizon progress. It does not assert local existence for every
possible network or define maximal infinite executions.
-/
namespace KernelR.Hybrid

/-- A complete witness supplies a complete continuation of every finite
competing execution whose endpoint has not passed the witness horizon.
Induction aligns actual flows and strips enabled jumps from the reference.
-/
theorem Execution.continue_to_complete {n θ ε route s u v T}
    (initialRun : @Execution n θ route s u)
    (reference : Execution θ route s v)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s)
    (complete : CompleteThrough reference T) (before : u.time ≤ T) :
    ∃ w, ∃ tail : Execution θ route u w, CompleteThrough tail T := by
  have all : ∀ count, ∀ {s u v}
      (initialRun : Execution θ route s u) (reference : Execution θ route s v),
      initialRun.moveCount + reference.moveCount = count →
      PhysicalInvariant θ s → CompleteThrough reference T → u.time ≤ T →
      ∃ w, ∃ tail : Execution θ route u w, CompleteThrough tail T := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
      intro s u v initialRun reference size hs complete before
      cases initialRun with
      | nil s => exact ⟨v, reference, complete⟩
      | @cons s a u move rest =>
        have ha : PhysicalInvariant θ a :=
          (Execution.cons move (.nil a) : Execution θ route s a).physical_invariant hb hs
        cases move with
        | jump j =>
          obtain ⟨v', reference', _, complete', _, shorter⟩ :=
            reference.strip_initial_jump complete j
          have hsmall : rest.moveCount + reference'.moveCount < count := by
            simp only [Execution.moveCount] at size
            omega
          exact ih _ hsmall rest reference' rfl ha complete' before
        | flow f =>
          cases reference with
          | nil s =>
            exact False.elim (by
              have later := rest.time_monotone
              have terminal := complete.1
              linarith [f.positive])
          | @cons s b v move referenceRest =>
            cases move with
            | jump j => exact False.elim ((f.no_initial_jump b).false j)
            | flow g =>
              by_cases earlier : a.time < b.time
              · have same : a.ObservationalEq (g.at a.time) := by
                  have h := f.at_observational_unique g hb hs
                    ⟨f.positive.le, le_rfl⟩ ⟨f.positive.le, earlier.le⟩
                  rwa [f.at_final] at h
                let remaining : Execution θ route (g.at a.time) v :=
                  .cons (.flow (g.suffix f.positive.le earlier)) referenceRest
                have remainingComplete : CompleteThrough remaining T := complete
                -- Retain the syntactic move count with the stronger transport
                -- interface, rather than postulating a complexity bound.
                obtain ⟨v'', reference'', observed, _, countEq⟩ :=
                  remaining.transport_observational_emissions_count same.symm
                have complete'' : CompleteThrough reference'' T :=
                  completeThrough_of_observational remaining reference'' observed remainingComplete
                have hsmall : rest.moveCount + reference''.moveCount < count := by
                  simp only [Execution.moveCount, remaining] at size countEq
                  omega
                exact ih _ hsmall rest reference'' rfl ha complete'' before
              · by_cases equal : a.time = b.time
                · have same := f.final_observational_unique g hb hs equal
                  obtain ⟨v', reference', observed, _, countEq⟩ :=
                    referenceRest.transport_observational_emissions_count same.symm
                  have complete' : CompleteThrough reference' T :=
                    completeThrough_of_observational referenceRest reference' observed complete
                  have hsmall : rest.moveCount + reference'.moveCount < count := by
                    simp only [Execution.moveCount] at size
                    omega
                  exact ih _ hsmall rest reference' rfl ha complete' before
                · have shorter : b.time < a.time :=
                    lt_of_le_of_ne (le_of_not_gt earlier) (Ne.symm equal)
                  have same : (f.at b.time).ObservationalEq b := by
                    have h := f.at_observational_unique g hb hs
                      ⟨g.positive.le, shorter.le⟩ ⟨g.positive.le, le_rfl⟩
                    rwa [g.at_final] at h
                  let remaining : Execution θ route (f.at b.time) u :=
                    .cons (.flow (f.suffix g.positive.le shorter)) rest
                  have physical : PhysicalInvariant θ (f.at b.time) :=
                    (Execution.cons (.flow (f.prefix g.positive shorter.le))
                      (.nil _) : Execution θ route s (f.at b.time)).physical_invariant hb hs
                  obtain ⟨v', reference', observed, _, countEq⟩ :=
                    referenceRest.transport_observational_emissions_count same.symm
                  have complete' : CompleteThrough reference' T :=
                    completeThrough_of_observational referenceRest reference' observed complete
                  have hsmall : remaining.moveCount + reference'.moveCount < count := by
                    simp only [Execution.moveCount, remaining] at size countEq ⊢
                    omega
                  exact ih _ hsmall remaining reference' rfl physical complete' before
  exact all _ initialRun reference rfl hs complete before

/-- At least one complete continuation exists from the supplied initial state.
For the chain protocol, this premise is discharged by its constructed witness.
-/
def HasCompleteExecution {n} (θ : Fin n → Parameters) (route : Router n)
    (s : Snapshot n) (T : ℝ) : Prop :=
  ∃ u, ∃ execution : Execution θ route s u, CompleteThrough execution T

theorem Execution.extend_complete {n θ ε route s u T}
    (initialRun : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s)
    (existsComplete : HasCompleteExecution θ route s T) (before : u.time ≤ T) :
    ∃ w, ∃ tail : Execution θ route u w, CompleteThrough (initialRun.append tail) T := by
  obtain ⟨v, reference, complete⟩ := existsComplete
  obtain ⟨w, tail, completeTail⟩ :=
    initialRun.continue_to_complete reference hb hs complete before
  exact ⟨w, tail, completeTail⟩

/-- Finite right-maximality at a horizon: no legal next move remains within
that horizon. This includes zero-time jumps and positive-duration flows.
-/
def RightMaximalThrough {n} (θ : Fin n → Parameters) (route : Router n)
    (state : Snapshot n) (T : ℝ) : Prop :=
  state.time ≤ T ∧ ∀ (next : Snapshot n), Move θ route state next → T < next.time

/-- A saturated endpoint at H has no next move which stays at or below H. -/
theorem Execution.complete_right_maximal {n θ route s u T}
    (initialRun : @Execution n θ route s u) (complete : CompleteThrough initialRun T) :
    RightMaximalThrough θ route u T := by
  refine ⟨complete.1.le, ?_⟩
  intro next move
  cases move with
  | flow flow => simpa only [complete.1] using flow.positive
  | jump jump => exact False.elim ((complete.2.1 next).false jump)

/-- A finite maximal competing execution is complete through the reference
horizon. The proof derives saturation instead of assuming it for that trace.
-/
theorem Execution.maximal_complete {n θ ε route s u T}
    (initialRun : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s)
    (existsComplete : HasCompleteExecution θ route s T)
    (maximal : RightMaximalThrough θ route u T) : CompleteThrough initialRun T := by
  obtain ⟨v, reference, complete⟩ := existsComplete
  obtain ⟨w, tail, completeTail⟩ :=
    initialRun.continue_to_complete reference hb hs complete maximal.1
  cases tail with
  | nil => exact completeTail
  | cons move rest =>
    exact False.elim (by
      have tooLate := maximal.2 _ move
      have endpoint := rest.time_monotone
      have horizon := completeTail.1
      linarith)

/-- With an actual complete witness available, finite right-maximality and
terminal completeness characterize the same competing executions.
-/
theorem Execution.complete_iff_right_maximal {n θ ε route s u T}
    (initialRun : @Execution n θ route s u)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (existsComplete : HasCompleteExecution θ route s T) :
    CompleteThrough initialRun T ↔ RightMaximalThrough θ route u T :=
  ⟨initialRun.complete_right_maximal,
    initialRun.maximal_complete box physical existsComplete⟩

#print axioms Execution.continue_to_complete
#print axioms Execution.maximal_complete

end KernelR.Hybrid
