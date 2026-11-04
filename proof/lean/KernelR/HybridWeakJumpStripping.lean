import KernelR.HybridTransverseJumpDiamond
import KernelR.HybridWeakObservationalTransport

/-! Cancellation against a transverse reference retains the certificate of
its remaining history. The competing jump itself need not be transverse. -/
namespace KernelR.Hybrid

/-- Strip any enabled physical jump from a complete transverse reference.
Only the remaining reference receives a positive-contact certificate. -/
theorem Execution.strip_initial_jump_transversal {n θ ε route s u a T}
    (execution : @Execution n θ route s u) (box : PhysicalBox θ ε)
    (complete : CompleteThrough execution T)
    (positive : execution.ContactsTransversal) (jump : Jump route s a) :
    ∃ b, ∃ tail : Execution θ route a b,
      u.ObservationalEq b ∧ CompleteThrough tail T ∧
      (jump.ledger.emissions ++ tail.ledger.emissions).Perm execution.ledger.emissions ∧
      tail.moveCount + 1 = execution.moveCount ∧ tail.ContactsTransversal := by
  induction execution generalizing a with
  | nil s => exact False.elim ((complete.2.1 a).false jump)
  | @cons s mid u move rest ih =>
    have hrest : CompleteThrough rest T := complete
    cases move with
    | flow flow => exact False.elim ((flow.no_initial_jump a).false jump)
    | jump reference =>
      rcases jump.transverse_local_diamond box reference with
        ⟨same, labels⟩ | ⟨a', b', residual, competing, same, labels, hp, _hq⟩
      · obtain ⟨v, tail, hv, hem, hcount, hpositive⟩ :=
          rest.transport_observational_transversal same.symm positive.2
        refine ⟨v, tail, hv, completeThrough_of_observational rest tail hv hrest, ?_, ?_, hpositive⟩
        · change (jump.ledger.emissions ++ tail.ledger.emissions).Perm
            (reference.ledger.emissions ++ rest.ledger.emissions)
          rw [hem]
          exact labels.append_right _
        · simp only [Execution.moveCount, hcount]
      · obtain ⟨v, tail, hv, hcomplete, hem, hcount, hpositive⟩ := ih hrest positive.2 competing
        obtain ⟨w, tail', hw, heq, hsize, hpositive'⟩ :=
          tail.transport_observational_transversal same.symm hpositive
        let remaining : Execution θ route a w := .cons (.jump residual) tail'
        refine ⟨w, remaining, hv.trans hw,
          completeThrough_of_observational tail remaining hw hcomplete, ?_, ?_, ?_⟩
        · change (jump.ledger.emissions ++ (residual.ledger.emissions ++ tail'.ledger.emissions)).Perm
            (reference.ledger.emissions ++ rest.ledger.emissions)
          rw [heq, ← List.append_assoc]
          exact (labels.append_right _).trans (by
            rw [List.append_assoc]
            exact hem.append_left _)
        · change tail'.moveCount + 1 + 1 = rest.moveCount + 1
          omega
        · exact ⟨hp positive.1, hpositive'⟩

end KernelR.Hybrid
