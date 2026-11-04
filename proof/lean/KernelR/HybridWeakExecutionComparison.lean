import KernelR.HybridWeakJumpStripping
import KernelR.HybridWeakFlowStrictification
import KernelR.HybridWeakFlowUrgency
import KernelR.HybridWeakEvents

/-! Finite complete comparison with one constructed transverse reference.
The competing execution may touch READY thresholds without firing. -/
namespace KernelR.Hybrid
open Set

theorem Flow.at_observational_unique_weak {n θ ε s u v}
    (flow : @Flow n θ s u) (weak : WeakFlow θ s v) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) :
    (flow.at t).ObservationalEq (weak.at t) :=
  ⟨rfl, flow.path_unique_weak weak box physical hf hg, rfl, rfl, rfl, List.Perm.refl _⟩

theorem Flow.final_observational_unique_weak {n θ ε s u v}
    (flow : @Flow n θ s u) (weak : WeakFlow θ s v) (box : PhysicalBox θ ε)
    (physical : PhysicalInvariant θ s) (date : u.time = v.time) :
    u.ObservationalEq v := by
  refine ⟨date, ?_, flow.main_fixed.trans weak.main_fixed.symm,
    flow.aux_fixed.trans weak.aux_fixed.symm, flow.raw_fixed.trans weak.raw_fixed.symm, ?_⟩
  · have same := flow.path_unique_weak weak box physical ⟨flow.positive.le, le_rfl⟩
      (show u.time ∈ Icc s.time v.time by rw [date]; exact ⟨weak.positive.le, le_rfl⟩)
    rw [flow.final, date, weak.final] at same
    exact same
  · rw [flow.queue_fixed, weak.queue_fixed]

/-- Any finite weak execution complete through the same horizon has the
reference's physical endpoint and actual FIRE multiset. Only the reference
must have positive READY contacts; no outcome or transversality premise is
imposed on the competing execution. -/
theorem Execution.observational_unique_weak {n θ ε route T}
    (box : @PhysicalBox n θ ε) {s u v}
    (reference : Execution θ route s u) (candidate : WeakExecution θ route s v)
    (physical : PhysicalInvariant θ s) (complete : CompleteThrough reference T)
    (positive : reference.ContactsTransversal) (weakComplete : WeakCompleteThrough candidate T) :
    u.ObservationalEq v ∧ reference.ledger.emissions.Perm candidate.ledger.emissions := by
  have all : ∀ k, ∀ {s u v} (reference : Execution θ route s u)
      (candidate : WeakExecution θ route s v),
      reference.moveCount + candidate.moveCount = k → PhysicalInvariant θ s →
      CompleteThrough reference T → reference.ContactsTransversal →
      WeakCompleteThrough candidate T →
      u.ObservationalEq v ∧ reference.ledger.emissions.Perm candidate.ledger.emissions := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro s u v reference candidate hcount physical complete positive weakComplete
      cases candidate with
      | nil s =>
        cases reference with
        | nil => exact ⟨.refl s, List.Perm.refl _⟩
        | @cons s a u move rest =>
          cases move with
          | flow flow =>
            have ht := rest.time_monotone
            have h₁ := complete.1
            have h₂ := weakComplete.1
            exact False.elim (by linarith [flow.positive])
          | jump jump => exact False.elim (weakComplete.2.1 a jump positive.1)
      | @cons s b v move q =>
        cases move with
        | jump jump =>
          obtain ⟨a, tail, same, hc, labels, hsize, hp⟩ :=
            reference.strip_initial_jump_transversal box complete positive jump
          have nextPhysical : PhysicalInvariant θ b :=
            (Execution.cons (.jump jump) (.nil b) : Execution θ route s b).physical_invariant box physical
          have smaller : tail.moveCount + q.moveCount < k := by
            simp only [WeakExecution.moveCount] at hcount
            omega
          obtain ⟨endpoints, emissions⟩ := ih _ smaller tail q rfl nextPhysical hc hp weakComplete
          refine ⟨same.trans endpoints, ?_⟩
          exact labels.symm.trans (by
            simpa only [WeakExecution.ledger, WeakMove.ledger, Ledger.add] using
              emissions.append_left jump.ledger.emissions)
        | flow weak =>
          cases reference with
          | nil =>
            have ht := q.time_monotone
            have h₁ := complete.1
            have h₂ := weakComplete.1
            exact False.elim (by linarith [weak.positive])
          | @cons s a u move r =>
            cases move with
            | jump jump =>
              exact False.elim (weak.no_initial_transverse_jump a jump positive.1)
            | flow flow =>
              by_cases date : a.time ≤ b.time
              · by_cases strict : a.time < b.time
                · have same : a.ObservationalEq (weak.at a.time) := by
                    have h := flow.at_observational_unique_weak weak box physical
                      ⟨flow.positive.le, le_rfl⟩ ⟨flow.positive.le, date⟩
                    rwa [flow.at_final] at h
                  obtain ⟨w, r', hw, he, hsize, hp⟩ :=
                    r.transport_observational_transversal same positive
                  let tail : WeakExecution θ route (weak.at a.time) v :=
                    .cons (.flow (weak.suffix flow.positive.le strict)) q
                  have nextPhysical : PhysicalInvariant θ (weak.at a.time) :=
                    same.physical_invariant
                      ((Execution.cons (.flow flow) (.nil a) : Execution θ route s a).physical_invariant box physical)
                  have smaller : r'.moveCount + tail.moveCount < k := by
                    simp only [Execution.moveCount, WeakExecution.moveCount] at hcount
                    simp only [tail, WeakExecution.moveCount]
                    omega
                  obtain ⟨endpoints, emissions⟩ := ih _ smaller r' tail rfl nextPhysical
                    (completeThrough_of_observational r r' hw complete) hp weakComplete
                  refine ⟨hw.trans endpoints, ?_⟩
                  simpa only [Execution.ledger, Move.ledger, Flow.ledger, WeakExecution.ledger,
                    WeakMove.ledger, WeakFlow.ledger, Ledger.add, Ledger.zero, List.nil_append, tail, he] using emissions
                · have equalDate : a.time = b.time := le_antisymm date (le_of_not_gt strict)
                  have same := flow.final_observational_unique_weak weak box physical equalDate
                  obtain ⟨w, r', hw, he, hsize, hp⟩ :=
                    r.transport_observational_transversal same positive
                  have nextPhysical := weak.physical_invariant box physical
                  have smaller : r'.moveCount + q.moveCount < k := by
                    simp only [Execution.moveCount, WeakExecution.moveCount] at hcount
                    omega
                  obtain ⟨endpoints, emissions⟩ := ih _ smaller r' q rfl nextPhysical
                    (completeThrough_of_observational r r' hw complete) hp weakComplete
                  refine ⟨hw.trans endpoints, ?_⟩
                  simpa only [Execution.ledger, Move.ledger, Flow.ledger, WeakExecution.ledger,
                    WeakMove.ledger, WeakFlow.ledger, Ledger.add, Ledger.zero, List.nil_append, he] using emissions
              · have strict : b.time < a.time := lt_of_not_ge date
                have same : b.ObservationalEq (flow.at b.time) := by
                  have h := flow.at_observational_unique_weak weak box physical
                    ⟨weak.positive.le, strict.le⟩ ⟨weak.positive.le, le_rfl⟩
                  rw [weak.at_final] at h
                  exact h.symm
                obtain ⟨w, q', hw, he, hsize⟩ :=
                  q.transport_observational_emissions_count same
                let tail : Execution θ route (flow.at b.time) u :=
                  .cons (.flow (flow.suffix weak.positive.le strict)) r
                have nextPhysical := same.physical_invariant (weak.physical_invariant box physical)
                have smaller : tail.moveCount + q'.moveCount < k := by
                  simp only [Execution.moveCount, WeakExecution.moveCount] at hcount
                  simp only [tail, Execution.moveCount]
                  omega
                obtain ⟨endpoints, emissions⟩ := ih _ smaller tail q' rfl nextPhysical complete positive
                  (weakCompleteThrough_of_observational q q' hw weakComplete)
                refine ⟨endpoints.trans hw.symm, ?_⟩
                simpa only [Execution.ledger, Move.ledger, Flow.ledger, WeakExecution.ledger,
                  WeakMove.ledger, WeakFlow.ledger, Ledger.add, Ledger.zero, List.nil_append, tail, he] using emissions
  exact all _ reference candidate rfl physical complete positive weakComplete

/-- Ordered per-cell FIRE times agree exactly, even when simultaneous events
have different legal interleavings. -/
theorem Execution.emissionTimes_unique_weak {n θ ε route s u v T}
    (reference : @Execution n θ route s u) (candidate : WeakExecution θ route s v)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (complete : CompleteThrough reference T) (positive : reference.ContactsTransversal)
    (weakComplete : WeakCompleteThrough candidate T) (i : Fin n) :
    reference.emissionTimes i = candidate.emissionTimes i := by
  have permutation := (reference.observational_unique_weak box candidate physical complete positive weakComplete).2
  exact List.Perm.eq_of_pairwise (le := fun a b : ℝ => a ≤ b)
    (fun _ _ _ _ h h' => le_antisymm h h')
    (reference.emissionTimes_chronological i) (candidate.emissionTimes_chronological i)
    ((permutation.filter _).map _)

#print axioms Execution.observational_unique_weak
#print axioms Execution.emissionTimes_unique_weak

end KernelR.Hybrid
