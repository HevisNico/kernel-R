import KernelR.HybridLocalFutureFrame
import KernelR.HybridContactTransversalityTransport

/-! Carry a proved contact certificate through future-queue framing. -/
namespace KernelR.Hybrid

@[simp] theorem Execution.contactsTransversal_cast_source {n θ route s v u}
    (execution : @Execution n θ route s u) (same : v = s) :
    (execution.cast_source same).ContactsTransversal ↔ execution.ContactsTransversal := by
  cases same
  rfl

theorem Jump.appendFuture_emptyRoute_transversal {n θ s u}
    (jump : @Jump n (fun _ _ => []) s u) (future : List (Delivery n)) :
    ∃ lifted : Jump (fun _ _ => []) (appendPending s future) (appendPending u future),
      lifted.ledger = jump.ledger ∧ lifted.deliveries = jump.deliveries ∧
      (lifted.ContactTransversal θ ↔ jump.ContactTransversal θ) := by
  obtain ⟨lifted, ledger, deliveries⟩ := jump.appendFuture_emptyRoute future
  exact ⟨lifted, ledger, deliveries, (jump.contactTransversal_requeue lifted).symm⟩

theorem Execution.appendFuture_emptyRoute_transversal {n θ s u}
    (execution : @Execution n θ (fun _ _ => []) s u) (future : List (Delivery n))
    (later : ∀ delivery ∈ future, u.time ≤ delivery.due) :
    ∃ lifted : Execution θ (fun _ _ => []) (appendPending s future) (appendPending u future),
      lifted.ledger = execution.ledger ∧ lifted.deliveries = execution.deliveries ∧
      (lifted.ContactsTransversal ↔ execution.ContactsTransversal) := by
  induction execution with
  | nil => exact ⟨.nil _, rfl, rfl, Iff.rfl⟩
  | @cons s middle u move rest ih =>
    obtain ⟨tail, ledger, deliveries, transversal⟩ := ih later
    cases move with
    | flow flow =>
      let lifted := flow.appendFuture future
        (fun delivery member => rest.time_monotone.trans (later delivery member))
      refine ⟨.cons (.flow lifted) tail, ?_, ?_, transversal⟩
      · change lifted.ledger.add tail.ledger = flow.ledger.add rest.ledger
        rw [ledger, flow.appendFuture_ledger]
      · change [] ++ tail.deliveries = [] ++ rest.deliveries
        rw [deliveries]
    | jump jump =>
      obtain ⟨lifted, jumpLedger, jumpDeliveries, jumpTransversal⟩ :=
        jump.appendFuture_emptyRoute_transversal future (θ := θ)
      refine ⟨.cons (.jump lifted) tail, ?_, ?_, ?_⟩
      · change lifted.ledger.add tail.ledger = jump.ledger.add rest.ledger
        rw [jumpLedger, ledger]
      · change lifted.deliveries ++ tail.deliveries = jump.deliveries ++ rest.deliveries
        rw [jumpDeliveries, deliveries]
      · simp only [Execution.ContactsTransversal, jumpTransversal, transversal]

end KernelR.Hybrid
