import KernelR.HybridContactTransversalityTransport
import KernelR.HybridLocalSourceRestriction

/-! Restricting only the future source queue retains contact fields. -/
namespace KernelR.Hybrid

theorem Execution.retainSourcesThrough_transversal {n θ s u}
    (execution : @Execution n θ (fun _ _ => []) s u) (positive : execution.ContactsTransversal)
    (cutoff : ℝ) (before : u.time ≤ cutoff) :
    ∃ lifted : Execution θ (fun _ _ => [])
      (retainSourcesThrough cutoff s) (retainSourcesThrough cutoff u),
      lifted.ledger = execution.ledger ∧ lifted.deliveries = execution.deliveries ∧
      lifted.ContactsTransversal := by
  induction execution with
  | nil => exact ⟨.nil _, rfl, rfl, trivial⟩
  | @cons s v u move rest ih =>
    cases move with
    | flow flow =>
      obtain ⟨tail, ledger, deliveries, transverse⟩ := ih positive before
      let lifted := flow.retainSourcesThrough cutoff
      refine ⟨.cons (.flow lifted) tail, ?_, ?_, transverse⟩
      · change lifted.ledger.add tail.ledger = flow.ledger.add rest.ledger
        rw [ledger, flow.retainSourcesThrough_ledger]
      · change [] ++ tail.deliveries = [] ++ rest.deliveries
        rw [deliveries]
    | jump jump =>
      obtain ⟨tail, ledger, deliveries, transverse⟩ := ih positive.2 before
      have firstDate : s.time ≤ cutoff := by
        rw [← jump.time_unchanged]
        exact rest.time_monotone.trans before
      obtain ⟨lifted, liftedLedger, liftedDeliveries⟩ :=
        jump.retainSourcesThrough_emptyRoute cutoff firstDate
      have liftedPositive : lifted.ContactTransversal θ :=
        (jump.contactTransversal_requeue lifted).mp positive.1
      refine ⟨.cons (.jump lifted) tail, ?_, ?_, liftedPositive, transverse⟩
      · change lifted.ledger.add tail.ledger = jump.ledger.add rest.ledger
        rw [liftedLedger, ledger]
      · change lifted.deliveries ++ tail.deliveries = jump.deliveries ++ rest.deliveries
        rw [liftedDeliveries, deliveries]

end KernelR.Hybrid
