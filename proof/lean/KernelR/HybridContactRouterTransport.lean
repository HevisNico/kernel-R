import KernelR.HybridEmissionRouterTransport
import KernelR.HybridContactTransversalityTransport

/-! Preserve the contact certificate when the router agrees at every actual
FIRE. The exact source and endpoint snapshots are retained. -/
namespace KernelR.Hybrid

theorem Jump.retarget_router_transversal {n θ route s u} (jump : @Jump n route s u)
    (newRoute : Router n)
    (hMatches : ∀ event ∈ jump.ledger.emissions,
      route event.1 event.2 = newRoute event.1 event.2) :
    ∃ lifted : Jump newRoute s u,
      lifted.ledger = jump.ledger ∧ lifted.deliveries = jump.deliveries ∧
      (lifted.ContactTransversal θ ↔ jump.ContactTransversal θ) := by
  obtain ⟨lifted, ledger, deliveries⟩ := jump.retarget_router newRoute hMatches
  exact ⟨lifted, ledger, deliveries,
    (jump.contactTransversal_of_observational lifted (.refl _) (.refl _)).symm⟩

theorem Execution.retarget_router_transversal {n θ route s u}
    (execution : @Execution n θ route s u) (newRoute : Router n)
    (hMatches : ∀ event ∈ execution.ledger.emissions,
      route event.1 event.2 = newRoute event.1 event.2) :
    ∃ lifted : Execution θ newRoute s u,
      lifted.ledger = execution.ledger ∧ lifted.deliveries = execution.deliveries ∧
      (lifted.ContactsTransversal ↔ execution.ContactsTransversal) := by
  induction execution with
  | nil => exact ⟨.nil _, rfl, rfl, Iff.rfl⟩
  | @cons s middle u move rest ih =>
    obtain ⟨tail, ledger, deliveries, transversal⟩ :=
      ih (fun event member => hMatches event (List.mem_append_right _ member))
    cases move with
    | flow flow =>
      refine ⟨.cons (.flow flow) tail, ?_, ?_, transversal⟩
      · change flow.ledger.add tail.ledger = flow.ledger.add rest.ledger
        rw [ledger]
      · change [] ++ tail.deliveries = [] ++ rest.deliveries
        rw [deliveries]
    | jump jump =>
      obtain ⟨lifted, jumpLedger, jumpDeliveries, jumpTransversal⟩ :=
        jump.retarget_router_transversal newRoute
          (fun event member => hMatches event (List.mem_append_left _ member)) (θ := θ)
      refine ⟨.cons (.jump lifted) tail, ?_, ?_, ?_⟩
      · change lifted.ledger.add tail.ledger = jump.ledger.add rest.ledger
        rw [jumpLedger, ledger]
      · change lifted.deliveries ++ tail.deliveries = jump.deliveries ++ rest.deliveries
        rw [jumpDeliveries, deliveries]
      · simp only [Execution.ContactsTransversal, jumpTransversal, transversal]

end KernelR.Hybrid
