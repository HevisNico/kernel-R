import KernelR.HybridQuietExecutionProduct

/-! Finite weaving of two actual executions without FIRE or arrival events.
Longer flows are cut and resumed with their original paths. -/
namespace KernelR.Hybrid

/-- The finite syntactic length, counting both flows and jumps. -/
@[simp] def Execution.moveCount {n θ route s u} : @Execution n θ route s u → ℕ
  | .nil _ => 0
  | .cons _ tail => tail.moveCount + 1

theorem Jump.product_right_empty {routeB : Router 1} {sB uB : Snapshot 1}
    (j : Jump routeB sB uB) (hn : j.QueueNeutral) (sA : Snapshot 1)
    (hclock : sA.time = sB.time) (Q : List (Delivery 2)) (route : Router 2) :
    ∃ g : Jump route (sA.product sB Q) (sA.product uB Q),
      g.ledger.emissions = [] ∧ g.deliveries = [] := by
  cases j with
  | fire => exact False.elim hn
  | arrive => exact False.elim hn
  | fastEnd i hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setMain_right]
    exact ⟨.fastEnd _ 1 hm hq,rfl,rfl⟩
  | reopen i hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setMain_right]
    exact ⟨.reopen _ 1 hm hq,rfl,rfl⟩
  | mark i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setAux_right]
    exact ⟨.mark _ 1 p hm hq,rfl,rfl⟩
  | silent i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setAux_right]
    exact ⟨.silent _ 1 p hm hq,rfl,rfl⟩
  | error i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setAux_right]
    exact ⟨.error _ 1 p hm hq,rfl,rfl⟩
  | auxReady i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setAux_right]
    exact ⟨.auxReady _ 1 p hm hq,rfl,rfl⟩
  | rawEnd i p origin hr ht =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.product_setRaw_right]
    exact ⟨.rawEnd _ 1 p origin hr (hclock.trans ht),rfl,rfl⟩

/-- Prefix an empty-ledger move to an already constructed empty-ledger tail. -/
theorem Execution.prepend_empty_witness {n θ route s v u} (m : @Move n θ route s v)
    (he : m.ledger.emissions = []) (hd : m.deliveries = [])
    (tail : ∃ e : Execution θ route v u, e.ledger.emissions = [] ∧ e.deliveries = []) :
    ∃ e : Execution θ route s u, e.ledger.emissions = [] ∧ e.deliveries = [] := by
  obtain ⟨e,heE,hdE⟩ := tail
  refine ⟨.cons m e,?_,?_⟩
  · change m.ledger.emissions ++ e.ledger.emissions = []
    rw [he,heE]; rfl
  · change m.deliveries ++ e.deliveries = []
    rw [hd,hdE]; rfl

/-- Weave two finite local executions at their actual shared times. The only
queue used by the resulting execution is the supplied fixed global queue. -/
theorem Execution.product_neutral {θA θB : Fin 1 → Parameters} {routeA routeB : Router 1}
    {sA uA sB uB : Snapshot 1} (eA : Execution θA routeA sA uA) (eB : Execution θB routeB sB uB)
    (hstart : sA.time = sB.time) (hfinish : uA.time = uB.time)
    (heA : eA.ledger.emissions = []) (hdA : eA.deliveries = [])
    (heB : eB.ledger.emissions = []) (hdB : eB.deliveries = [])
    (Q : List (Delivery 2)) (hQ : ∀ d ∈ Q, uA.time ≤ d.due) (route : Router 2) :
    ∃ e : Execution (extendParameters θA (θB 0)) route (sA.product sB Q) (uA.product uB Q),
      e.ledger.emissions = [] ∧ e.deliveries = [] := by
  suffices aux : ∀ N : ℕ, ∀ {a b : Snapshot 1}
      (l : Execution θA routeA a uA) (r : Execution θB routeB b uB),
      l.moveCount + r.moveCount = N → a.time = b.time →
      l.ledger.emissions = [] → l.deliveries = [] →
      r.ledger.emissions = [] → r.deliveries = [] →
      ∃ e : Execution (extendParameters θA (θB 0)) route (a.product b Q) (uA.product uB Q),
        e.ledger.emissions = [] ∧ e.deliveries = [] by
    exact aux _ eA eB rfl hstart heA hdA heB hdB
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro sA sB eA eB hsize hstart heA hdA heB hdB
    have recurse {a b : Snapshot 1} (l : Execution θA routeA a uA) (r : Execution θB routeB b uB)
        (hdec : l.moveCount + r.moveCount < N) (hsync : a.time = b.time)
        (hel : l.ledger.emissions = []) (hdl : l.deliveries = [])
        (her : r.ledger.emissions = []) (hdr : r.deliveries = []) :
        ∃ e : Execution (extendParameters θA (θB 0)) route (a.product b Q) (uA.product uB Q),
          e.ledger.emissions = [] ∧ e.deliveries = [] :=
      ih _ hdec l r rfl hsync hel hdl her hdr
    cases eA with
    | nil =>
      cases eB with
      | nil => exact ⟨.nil _,rfl,rfl⟩
      | @cons _ vB _ mB restB =>
        change mB.ledger.emissions ++ restB.ledger.emissions = [] at heB
        change mB.deliveries ++ restB.deliveries = [] at hdB
        obtain ⟨heMB,heRB⟩ := List.append_eq_nil_iff.mp heB
        obtain ⟨hdMB,hdRB⟩ := List.append_eq_nil_iff.mp hdB
        cases mB with
        | flow fB => exact False.elim (by linarith [fB.positive,restB.time_monotone])
        | jump jB =>
          obtain ⟨g,heG,hdG⟩ := jB.product_right_empty (jB.queueNeutral_of_no_events heMB hdMB) uA hstart Q route
          apply Execution.prepend_empty_witness (.jump g) heG hdG
          exact recurse (Execution.nil (θ := θA) (route := routeA) uA) restB
            (by simp only [Execution.moveCount] at hsize ⊢; omega)
            (hstart.trans jB.time_unchanged.symm) rfl rfl heRB hdRB
    | @cons _ vA _ mA restA =>
      change mA.ledger.emissions ++ restA.ledger.emissions = [] at heA
      change mA.deliveries ++ restA.deliveries = [] at hdA
      obtain ⟨heMA,heRA⟩ := List.append_eq_nil_iff.mp heA
      obtain ⟨hdMA,hdRA⟩ := List.append_eq_nil_iff.mp hdA
      cases mA with
      | jump jA =>
        obtain ⟨g,heG,hdG⟩ := jA.product_left_empty (jA.queueNeutral_of_no_events heMA hdMA) sB Q route
        apply Execution.prepend_empty_witness (.jump g) heG hdG
        exact recurse restA eB (by simp only [Execution.moveCount] at hsize ⊢; omega)
          (jA.time_unchanged.trans hstart) heRA hdRA heB hdB
      | flow fA =>
        cases eB with
        | nil => exact False.elim (by linarith [fA.positive,restA.time_monotone])
        | @cons _ vB _ mB restB =>
          change mB.ledger.emissions ++ restB.ledger.emissions = [] at heB
          change mB.deliveries ++ restB.deliveries = [] at hdB
          obtain ⟨heMB,heRB⟩ := List.append_eq_nil_iff.mp heB
          obtain ⟨hdMB,hdRB⟩ := List.append_eq_nil_iff.mp hdB
          cases mB with
          | jump jB =>
            obtain ⟨g,heG,hdG⟩ := jB.product_right_empty (jB.queueNeutral_of_no_events heMB hdMB) sA hstart Q route
            apply Execution.prepend_empty_witness (.jump g) heG hdG
            exact recurse (Execution.cons (.flow fA) restA) restB
              (by simp only [Execution.moveCount] at hsize ⊢; omega)
              (hstart.trans jB.time_unchanged.symm)
              (by change [] ++ restA.ledger.emissions = []; simpa using heRA)
              (by change [] ++ restA.deliveries = []; simpa using hdRA) heRB hdRB
          | flow fB =>
            rcases lt_trichotomy vA.time vB.time with hshort | hequal | hlong
            · have hprefix : sB.time < vA.time := by rw [← hstart]; exact fA.positive
              let prefixB := fB.prefix hprefix hshort.le
              let suffixB := fB.suffix hprefix.le hshort
              let remainingB : Execution θB routeB (fB.at vA.time) uB := .cons (.flow suffixB) restB
              let combined := fA.product prefixB hstart rfl Q
                (fun d hd => restA.time_monotone.trans (hQ d hd))
              apply Execution.prepend_empty_witness (.flow combined) rfl rfl
              exact recurse restA remainingB
                (by simp only [remainingB,Execution.moveCount] at hsize ⊢; omega) rfl heRA hdRA
                (by change [] ++ restB.ledger.emissions = []; simpa using heRB)
                (by change [] ++ restB.deliveries = []; simpa using hdRB)
            · let combined := fA.product fB hstart hequal Q
                (fun d hd => restA.time_monotone.trans (hQ d hd))
              apply Execution.prepend_empty_witness (.flow combined) rfl rfl
              exact recurse restA restB (by simp only [Execution.moveCount] at hsize ⊢; omega)
                hequal heRA hdRA heRB hdRB
            · have hprefix : sA.time < vB.time := by rw [hstart]; exact fB.positive
              let prefixA := fA.prefix hprefix hlong.le
              let suffixA := fA.suffix hprefix.le hlong
              let remainingA : Execution θA routeA (fA.at vB.time) uA := .cons (.flow suffixA) restA
              let combined := prefixA.product fB hstart rfl Q (by
                intro d hd
                change vB.time ≤ d.due
                rw [hfinish] at hQ
                exact restB.time_monotone.trans (hQ d hd))
              apply Execution.prepend_empty_witness (.flow combined) rfl rfl
              exact recurse remainingA restB
                (by simp only [remainingA,Execution.moveCount] at hsize ⊢; omega) rfl
                (by change [] ++ restA.ledger.emissions = []; simpa using heRA)
                (by change [] ++ restA.deliveries = []; simpa using hdRA) heRB hdRB

end KernelR.Hybrid
