import KernelR.HybridContactTransversalityTransport
import KernelR.HybridPortPermutation

/-! A port permutation retains the actual positive contact field. -/
namespace KernelR.Hybrid

theorem Jump.contactTransversal_permutePorts {n θ s u}
    (jump : @Jump n (fun _ _ => []) s u) (σ : Equiv.Perm Port) :
    (jump.permutePorts σ).ContactTransversal (permuteParameters θ σ) ↔
      jump.ContactTransversal θ := by
  rw [(jump.permutePorts σ).contactTransversal_iff_departures,
    jump.contactTransversal_iff_departures]
  change ((∀ i, s.main i = .ready → u.main i ≠ s.main i →
      0 < field (permuteParameters θ σ) (s.permutePorts σ) (s.x.permutePorts σ) s.time i .q) ∧
    (∀ i p, s.aux i (σ p) = .ready → u.aux i (σ p) ≠ s.aux i (σ p) →
      0 < field (permuteParameters θ σ) (s.permutePorts σ) (s.x.permutePorts σ) s.time i (.m p))) ↔ _
  simp only [field_permutePorts, Coord.permutePorts]
  constructor
  · rintro ⟨main, aux⟩
    refine ⟨main, ?_⟩
    intro i p ready changed
    simpa only [Equiv.apply_symm_apply] using
      aux i (σ.symm p) (by simpa only [Equiv.apply_symm_apply] using ready)
        (by simpa only [Equiv.apply_symm_apply] using changed)
  · rintro ⟨main, aux⟩
    exact ⟨main, fun i p => aux i (σ p)⟩

theorem Execution.contactsTransversal_permutePorts {n θ s u}
    (execution : @Execution n θ (fun _ _ => []) s u) (σ : Equiv.Perm Port)
    (positive : execution.ContactsTransversal) :
    (execution.permutePorts σ).ContactsTransversal := by
  induction execution with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow flow => exact ih positive
    | jump jump =>
      exact ⟨(jump.contactTransversal_permutePorts σ).mpr positive.1, ih positive.2⟩

end KernelR.Hybrid
