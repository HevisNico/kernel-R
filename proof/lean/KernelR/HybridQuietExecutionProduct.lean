import KernelR.HybridTwoCellJumpProduct
import KernelR.HybridQuietSourceArrival

/-! An actual event-free local execution can run alongside a truly quiet cell.
The one global queue stays exact; no local queue is inserted into it. -/
namespace KernelR.Hybrid

theorem relax_restart (rate target initial start cut t : ℝ) :
    relax rate target (relax rate target initial start cut) cut t =
      relax rate target initial start t := by
  unfold relax
  rw [add_sub_cancel_left,mul_assoc,← Real.exp_add]
  rw [show -rate * (cut - start) + -rate * (t - cut) = -rate * (t - start) by ring]

theorem quietAt_self {n} (s : Snapshot n) : quietAt s s.time = s := by
  unfold quietAt
  rw [quietValues_initial]

theorem quietAt_quietAt {n} (s : Snapshot n) (cut t : ℝ) :
    quietAt (quietAt s cut) t = quietAt s t := by
  cases s
  simp only [quietAt]
  congr 1
  funext i c
  cases c <;> simp [quietValues,relax_restart]

theorem Jump.queueNeutral_of_no_events {n route s u} (j : @Jump n route s u)
    (he : j.ledger.emissions = []) (hd : j.deliveries = []) : j.QueueNeutral := by
  cases j <;> simp_all [Jump.QueueNeutral,Jump.ledger,Ledger.zero,Jump.deliveries]

/-- A queue-neutral local jump admits a genuine lift whose global ledgers are
empty. The global route is arbitrary because none of these jumps is FIRE. -/
theorem Jump.product_left_empty {routeA : Router 1} {sA uA : Snapshot 1}
    (j : Jump routeA sA uA) (hn : j.QueueNeutral) (sB : Snapshot 1) (Q : List (Delivery 2))
    (route : Router 2) :
    ∃ g : Jump route (sA.product sB Q) (uA.product sB Q),
      g.ledger.emissions = [] ∧ g.deliveries = [] := by
  cases j with
  | fire => exact False.elim hn
  | arrive => exact False.elim hn
  | fastEnd i hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setMain_left]
    exact ⟨.fastEnd _ 0 hm hq,rfl,rfl⟩
  | reopen i hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setMain_left]
    exact ⟨.reopen _ 0 hm hq,rfl,rfl⟩
  | mark i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setAux_left]
    exact ⟨.mark _ 0 p hm hq,rfl,rfl⟩
  | silent i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setAux_left]
    exact ⟨.silent _ 0 p hm hq,rfl,rfl⟩
  | error i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setAux_left]
    exact ⟨.error _ 0 p hm hq,rfl,rfl⟩
  | auxReady i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setAux_left]
    exact ⟨.auxReady _ 0 p hm hq,rfl,rfl⟩
  | rawEnd i p origin hr ht =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setRaw_left]
    exact ⟨.rawEnd _ 0 p origin hr ht,rfl,rfl⟩

/-- Pair an actual local execution without outputs or arrivals with a quiet
second cell. The endpoint uses its original quiet clock across every cut. -/
theorem Execution.product_with_quiet_left {θA θB : Fin 1 → Parameters} {routeA : Router 1}
    {sA uA : Snapshot 1} (e : Execution θA routeA sA uA)
    (he : e.ledger.emissions = []) (hd : e.deliveries = [])
    (sB : Snapshot 1) (hstart : sA.time = sB.time) (hsB : ReadyCoordinates sB 0)
    (hrB : ∀ p, sB.raw 0 p = none) (Q : List (Delivery 2))
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
        (by intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hsB.ready)
        (by intro j p; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact (hsB.auxiliary p).1)
        (by intro j p; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hrB p)
        (by intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact lt_of_le_of_lt hsB.charge.2 (by norm_num))
        (by intro j p; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(hsB.auxiliary p).2.2])
        (by intro d hd; exact False.elim (List.not_mem_nil hd))
      let combined : Flow (extendParameters θA (θB 0)) (s.product sB Q)
          (v.product (quietAt sB v.time) Q) :=
        f.product qflow hstart rfl Q (fun d hd => rest.time_monotone.trans (hQ d hd))
      have hstartB : sB.time ≤ v.time := by rw [← hstart]; exact f.positive.le
      obtain ⟨tail,heTail,hdTail⟩ := ih heRest hdRest (quietAt sB v.time) rfl
        (quietAt_ready_coordinates sB 0 hsB hstartB) hrB hQ
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
      obtain ⟨tail,heTail,hdTail⟩ := ih heRest hdRest sB (j.time_unchanged.trans hstart) hsB hrB hQ
      refine ⟨.cons (.jump g) tail,?_,?_⟩
      · change g.ledger.emissions ++ tail.ledger.emissions = []
        rw [heG,heTail]; rfl
      · change g.deliveries ++ tail.deliveries = []
        rw [hdG,hdTail]; rfl

end KernelR.Hybrid
