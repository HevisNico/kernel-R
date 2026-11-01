import KernelR.HybridQuietExecutionProduct

/-! Quiet products require only actual READY preguards, not a narrow charge band. -/
namespace KernelR.Hybrid

/-- Pair an actual local execution without outputs or arrivals with a quiet
second cell. The endpoint uses its original quiet clock across every cut. -/
theorem Execution.product_with_guarded_quiet_left {θA θB : Fin 1 → Parameters} {routeA : Router 1}
    {sA uA : Snapshot 1} (e : Execution θA routeA sA uA)
    (he : e.ledger.emissions = []) (hd : e.deliveries = [])
    (sB : Snapshot 1) (hstart : sA.time = sB.time)
    (hmB : sB.main 0 = .ready) (haB : ∀ p, sB.aux 0 p = .ready)
    (hrB : ∀ p, sB.raw 0 p = none) (hqB : sB.x 0 .q < 1) (hxB : ∀ p, sB.x 0 (.m p) < 1) (Q : List (Delivery 2))
    (hQ : ∀ d ∈ Q, uA.time ≤ d.due) (route : Router 2) :
    ∃ lifted : Execution (extendParameters θA (θB 0)) route
        (sA.product sB Q) (uA.product (quietAt sB uA.time) Q),
      lifted.ledger.emissions = [] ∧ lifted.deliveries = [] := by
  induction e generalizing sB with
  | nil s =>
    have hquiet : quietAt sB s.time = sB := by rw [hstart,quietAt_self]
    rw [hquiet]
    exact ⟨.nil _,rfl,rfl⟩
  | @cons s v u move rest ih =>
    change move.ledger.emissions ++ rest.ledger.emissions = [] at he
    change move.deliveries ++ rest.deliveries = [] at hd
    obtain ⟨heMove,heRest⟩ := List.append_eq_nil_iff.mp he
    obtain ⟨hdMove,hdRest⟩ := List.append_eq_nil_iff.mp hd
    cases move with
    | flow f =>
      let b0 : Snapshot 1 := {sB with pending := []}
      let qflow : Flow θB b0 (quietAt b0 v.time) := quietFlow b0
        (by change sB.time < v.time; rw [← hstart]; exact f.positive)
        (by intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hmB)
        (by intro j p; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact haB p)
        (by intro j p; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hrB p)
        (by intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hqB)
        (by intro j p; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hxB p)
        (by intro d hd; exact False.elim (List.not_mem_nil hd))
      let combined : Flow (extendParameters θA (θB 0)) (s.product sB Q)
          (v.product (quietAt sB v.time) Q) :=
        f.product qflow hstart rfl Q (fun d hd => rest.time_monotone.trans (hQ d hd))
      have hstartB : sB.time ≤ v.time := by rw [← hstart]; exact f.positive.le
      obtain ⟨tail,heTail,hdTail⟩ := ih heRest hdRest (quietAt sB v.time) rfl
        hmB haB hrB
        (relax_lt (by norm_num) hstartB hqB (by norm_num))
        (fun p => relax_lt (by norm_num) hstartB (hxB p) (by norm_num)) hQ
      have hresult : ∃ lifted : Execution (extendParameters θA (θB 0)) route
          (s.product sB Q) (u.product (quietAt (quietAt sB v.time) u.time) Q),
          lifted.ledger.emissions = [] ∧ lifted.deliveries = [] := by
        refine ⟨.cons (.flow combined) tail,?_,?_⟩
        · change [] ++ tail.ledger.emissions = []
          simpa using heTail
        · change [] ++ tail.deliveries = []
          simpa using hdTail
      rw [quietAt_quietAt] at hresult
      exact hresult
    | jump j =>
      obtain ⟨g,heG,hdG⟩ := j.product_left_empty (j.queueNeutral_of_no_events heMove hdMove) sB Q route
      obtain ⟨tail,heTail,hdTail⟩ := ih heRest hdRest sB (j.time_unchanged.trans hstart) hmB haB hrB hqB hxB hQ
      refine ⟨.cons (.jump g) tail,?_,?_⟩
      · change g.ledger.emissions ++ tail.ledger.emissions = []
        rw [heG,heTail]; rfl
      · change g.deliveries ++ tail.deliveries = []
        rw [hdG,hdTail]; rfl


end KernelR.Hybrid
