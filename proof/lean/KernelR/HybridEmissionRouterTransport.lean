import KernelR.HybridInputs
import KernelR.HybridPulseSection

/-! Change a routing law only where its values are observationally unchanged
on actual FIRE events. Physical states, queues, clocks, doses and deliveries
are retained exactly; this is not an input insertion or a router switch. -/
namespace KernelR.Hybrid

theorem Jump.retarget_router {n route s u} (j : @Jump n route s u) (newRoute : Router n)
    (hMatches : ∀ event ∈ j.ledger.emissions, route event.1 event.2 = newRoute event.1 event.2) :
    ∃ lifted : Jump newRoute s u, lifted.ledger = j.ledger ∧ lifted.deliveries = j.deliveries := by
  cases j with
  | fire i hm hq =>
    have hroute : route i s.time = newRoute i s.time := hMatches (i,s.time) (by simp [Jump.ledger])
    simp only [Jump.ledger,Jump.deliveries]
    rw [hroute]
    exact ⟨.fire s i hm hq,rfl,rfl⟩
  | fastEnd i hm hq => exact ⟨.fastEnd _ i hm hq,rfl,rfl⟩
  | reopen i hm hq => exact ⟨.reopen _ i hm hq,rfl,rfl⟩
  | mark i p hm hq => exact ⟨.mark _ i p hm hq,rfl,rfl⟩
  | silent i p hm hq => exact ⟨.silent _ i p hm hq,rfl,rfl⟩
  | error i p hm hq => exact ⟨.error _ i p hm hq,rfl,rfl⟩
  | auxReady i p hm hq => exact ⟨.auxReady _ i p hm hq,rfl,rfl⟩
  | rawEnd i p origin hr ht => exact ⟨.rawEnd _ i p origin hr ht,rfl,rfl⟩
  | arrive d before after hqueue ht hr => exact ⟨.arrive _ d before after hqueue ht hr,rfl,rfl⟩

theorem Move.retarget_router {n θ route s u} (m : @Move n θ route s u) (newRoute : Router n)
    (hMatches : ∀ event ∈ m.ledger.emissions, route event.1 event.2 = newRoute event.1 event.2) :
    ∃ lifted : Move θ newRoute s u, lifted.ledger = m.ledger ∧ lifted.deliveries = m.deliveries := by
  cases m with
  | flow f => exact ⟨.flow f,rfl,rfl⟩
  | jump j =>
    obtain ⟨g,hL,hD⟩ := j.retarget_router newRoute hMatches
    exact ⟨.jump g,hL,hD⟩

/-- Same complete physical execution endpoints and exact operational queues;
only the router type changes, using equality at every real emitted event. -/
theorem Execution.retarget_router {n θ route s u} (e : @Execution n θ route s u)
    (newRoute : Router n)
    (hMatches : ∀ event ∈ e.ledger.emissions, route event.1 event.2 = newRoute event.1 event.2) :
    ∃ lifted : Execution θ newRoute s u, lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries := by
  induction e with
  | nil => exact ⟨.nil _,rfl,rfl⟩
  | @cons s v u move rest ih =>
    obtain ⟨tail,hRL,hRD⟩ := ih (fun event he => hMatches event (List.mem_append_right _ he))
    obtain ⟨step,hML,hMD⟩ := move.retarget_router newRoute
      (fun event he => hMatches event (List.mem_append_left _ he))
    refine ⟨.cons step tail,?_,?_⟩
    · change step.ledger.add tail.ledger = move.ledger.add rest.ledger
      rw [hML,hRL]
    · change step.deliveries ++ tail.deliveries = move.deliveries ++ rest.deliveries
      rw [hMD,hRD]

/-- Whether any instantaneous jump is enabled depends on the physical guards,
RAW and queue, not on which token list a hypothetical FIRE would issue. -/
theorem no_jump_retarget_router {n route s}
    (hblocked : ∀ v, IsEmpty (@Jump n route s v)) (newRoute : Router n) :
    ∀ v, IsEmpty (Jump newRoute s v) := by
  intro v
  constructor
  intro jump
  cases jump with
  | fire i hm hq => exact (hblocked _).false (.fire s i hm hq)
  | fastEnd i hm hq => exact (hblocked _).false (.fastEnd s i hm hq)
  | reopen i hm hq => exact (hblocked _).false (.reopen s i hm hq)
  | mark i p hm hq => exact (hblocked _).false (.mark s i p hm hq)
  | silent i p hm hq => exact (hblocked _).false (.silent s i p hm hq)
  | error i p hm hq => exact (hblocked _).false (.error s i p hm hq)
  | auxReady i p hm hq => exact (hblocked _).false (.auxReady s i p hm hq)
  | rawEnd i p origin hr ht => exact (hblocked _).false (.rawEnd s i p origin hr ht)
  | arrive d before after hqueue ht hr => exact (hblocked _).false (.arrive s d before after hqueue ht hr)

/-- Completion is retained even though only actual FIRE routes need agree. -/
theorem Execution.retarget_router_complete {n θ route s u T} (e : @Execution n θ route s u)
    (newRoute : Router n)
    (hMatches : ∀ event ∈ e.ledger.emissions, route event.1 event.2 = newRoute event.1 event.2)
    (hComplete : CompleteThrough e T) :
    ∃ lifted : Execution θ newRoute s u,
      lifted.ledger = e.ledger ∧ lifted.deliveries = e.deliveries ∧ CompleteThrough lifted T := by
  obtain ⟨lifted,hL,hD⟩ := e.retarget_router newRoute hMatches
  exact ⟨lifted,hL,hD,hComplete.1,no_jump_retarget_router hComplete.2.1 newRoute,hComplete.2.2⟩

end KernelR.Hybrid
