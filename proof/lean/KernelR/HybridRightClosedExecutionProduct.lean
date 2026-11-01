import KernelR.HybridNeutralExecutionProduct
import KernelR.HybridPreparedTrain

/-! A neutral sender can run alongside an emitting receiver whose global
outgoing contact is closed. Every receiver FIRE remains a real global FIRE. -/
namespace KernelR.Hybrid

/-- Lift a local B jump with no delivery. A local FIRE is transported by an
actual global FIRE, using closure only to retain the fixed global queue. -/
theorem Jump.product_right_closed {sB uB : Snapshot 1}
    (j : Jump (fun _ _ => []) sB uB) (hd : j.deliveries = [])
    (sA : Snapshot 1) (hclock : sA.time = sB.time) (Q : List (Delivery 2)) (route : Router 2)
    (hclosed : route 1 sB.time = []) :
    ∃ g : Jump route (sA.product sB Q) (sA.product uB Q),
      g.ledger.emissions = j.ledger.emissions.map (fun event => (1,event.2)) ∧ g.deliveries = [] := by
  by_cases he : j.ledger.emissions = []
  · obtain ⟨g,hg,hdg⟩ := j.product_right_empty (j.queueNeutral_of_no_events he hd) sA hclock Q route
    refine ⟨g,?_,hdg⟩
    rw [he,List.map_nil]
    exact hg
  · cases j <;> try exact False.elim (he rfl)
    case fire i hm hq =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      let before := sA.product sB Q
      let after := sA.product
        ({(setMain sB 0 .fast) with pending := sB.pending ++ []} : Snapshot 1) Q
      have heq : after = {(setMain before 1 .fast) with pending := before.pending ++ route 1 before.time} := by
        change sA.product (setMain sB 0 .fast) Q =
          {(setMain (sA.product sB Q) 1 .fast) with pending := Q ++ route 1 sA.time}
        rw [hclock,hclosed,List.append_nil,Snapshot.product_setMain_right]
        rfl
      let g : Jump route before after := heq.symm ▸ Jump.fire before 1 hm hq
      have hfast : after.main 1 = .fast := by
        change (setMain sB 0 .fast).main 0 = .fast
        simp [setMain]
      have hgem : g.ledger.emissions = [(1,before.time)] :=
        g.ready_main_departure_emission 1 hm (by rw [hfast]; decide)
      have hgdel : g.deliveries = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro d hdg
        have hz := g.no_emissions_of_delivery d hdg
        rw [hgem] at hz
        contradiction
      refine ⟨g,?_,hgdel⟩
      rw [hgem]
      change [(1,sA.time)] = [(1,sB.time)]
      rw [hclock]

/-- Prefix a real move with its exact emission contribution. -/
theorem Execution.prepend_emission_witness {n θ route s v u}
    (m : @Move n θ route s v) (M E : List (Fin n × ℝ))
    (he : m.ledger.emissions = M) (hd : m.deliveries = [])
    (tail : ∃ e : Execution θ route v u, e.ledger.emissions = E ∧ e.deliveries = []) :
    ∃ e : Execution θ route s u, e.ledger.emissions = M ++ E ∧ e.deliveries = [] := by
  obtain ⟨e,heE,hdE⟩ := tail
  refine ⟨.cons m e,?_,?_⟩
  · change m.ledger.emissions ++ e.ledger.emissions = _
    rw [he,heE]
  · change m.deliveries ++ e.deliveries = []
    rw [hd,hdE]
    rfl

/-- Weave two finite actual executions. A has no output, B has no local
routing, and the global B contact is closed at every relevant event clock.
Only B's true output list is mapped to cell1; no chronology merge is needed. -/
theorem Execution.product_right_closed {θA θB : Fin 1 → Parameters} {routeA : Router 1}
    {sA uA sB uB : Snapshot 1} (eA : Execution θA routeA sA uA)
    (eB : Execution θB (fun _ _ => []) sB uB)
    (hstart : sA.time = sB.time) (hfinish : uA.time = uB.time)
    (heA : eA.ledger.emissions = []) (hdA : eA.deliveries = []) (hdB : eB.deliveries = [])
    (Q : List (Delivery 2)) (hQ : ∀ d ∈ Q, uA.time ≤ d.due) (route : Router 2)
    (hclosed : ∀ t, t ≤ uB.time → route 1 t = []) :
    ∃ e : Execution (extendParameters θA (θB 0)) route (sA.product sB Q) (uA.product uB Q),
      e.ledger.emissions = eB.ledger.emissions.map (fun event => (1,event.2)) ∧ e.deliveries = [] := by
  suffices aux : ∀ N : ℕ, ∀ {a b : Snapshot 1}
      (l : Execution θA routeA a uA) (r : Execution θB (fun _ _ => []) b uB),
      l.moveCount + r.moveCount = N → a.time = b.time →
      l.ledger.emissions = [] → l.deliveries = [] → r.deliveries = [] →
      ∃ e : Execution (extendParameters θA (θB 0)) route (a.product b Q) (uA.product uB Q),
        e.ledger.emissions = r.ledger.emissions.map (fun event => (1,event.2)) ∧ e.deliveries = [] by
    exact aux _ eA eB rfl hstart heA hdA hdB
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro sA sB eA eB hsize hstart heA hdA hdB
    have recurse {a b : Snapshot 1} (l : Execution θA routeA a uA)
        (r : Execution θB (fun _ _ => []) b uB)
        (hdec : l.moveCount + r.moveCount < N) (hsync : a.time = b.time)
        (hel : l.ledger.emissions = []) (hdl : l.deliveries = []) (hdr : r.deliveries = []) :
        ∃ e : Execution (extendParameters θA (θB 0)) route (a.product b Q) (uA.product uB Q),
          e.ledger.emissions = r.ledger.emissions.map (fun event => (1,event.2)) ∧ e.deliveries = [] :=
      ih _ hdec l r rfl hsync hel hdl hdr
    cases eA with
    | nil =>
      cases eB with
      | nil => exact ⟨.nil _,rfl,rfl⟩
      | @cons _ vB _ mB restB =>
        change mB.deliveries ++ restB.deliveries = [] at hdB
        obtain ⟨hdMB,hdRB⟩ := List.append_eq_nil_iff.mp hdB
        cases mB with
        | flow fB => exact False.elim (by linarith [fB.positive,restB.time_monotone])
        | jump jB =>
          have htime : sB.time ≤ uB.time := by
            have h := restB.time_monotone
            rwa [jB.time_unchanged] at h
          obtain ⟨g,heG,hdG⟩ := jB.product_right_closed hdMB uA hstart Q route (hclosed _ htime)
          have tail := recurse (Execution.nil (θ := θA) (route := routeA) uA) restB
            (by simp only [Execution.moveCount] at hsize ⊢; omega)
            (hstart.trans jB.time_unchanged.symm) rfl rfl hdRB
          simpa only [Execution.ledger,Move.ledger,Ledger.add,List.map_append] using
            Execution.prepend_emission_witness (.jump g) _ _ heG hdG tail
    | @cons _ vA _ mA restA =>
      change mA.ledger.emissions ++ restA.ledger.emissions = [] at heA
      change mA.deliveries ++ restA.deliveries = [] at hdA
      obtain ⟨heMA,heRA⟩ := List.append_eq_nil_iff.mp heA
      obtain ⟨hdMA,hdRA⟩ := List.append_eq_nil_iff.mp hdA
      cases mA with
      | jump jA =>
        obtain ⟨g,heG,hdG⟩ := jA.product_left_empty (jA.queueNeutral_of_no_events heMA hdMA) sB Q route
        have tail := recurse restA eB (by simp only [Execution.moveCount] at hsize ⊢; omega)
          (jA.time_unchanged.trans hstart) heRA hdRA hdB
        simpa only [List.nil_append] using
          Execution.prepend_emission_witness (.jump g) [] _ heG hdG tail
      | flow fA =>
        cases eB with
        | nil => exact False.elim (by linarith [fA.positive,restA.time_monotone])
        | @cons _ vB _ mB restB =>
          change mB.deliveries ++ restB.deliveries = [] at hdB
          obtain ⟨hdMB,hdRB⟩ := List.append_eq_nil_iff.mp hdB
          cases mB with
          | jump jB =>
            have htime : sB.time ≤ uB.time := by
              have h := restB.time_monotone
              rwa [jB.time_unchanged] at h
            obtain ⟨g,heG,hdG⟩ := jB.product_right_closed hdMB sA hstart Q route (hclosed _ htime)
            have tail := recurse (Execution.cons (.flow fA) restA) restB
              (by simp only [Execution.moveCount] at hsize ⊢; omega)
              (hstart.trans jB.time_unchanged.symm)
              (by change [] ++ restA.ledger.emissions = []; simpa using heRA)
              (by change [] ++ restA.deliveries = []; simpa using hdRA) hdRB
            simpa only [Execution.ledger,Move.ledger,Ledger.add,List.map_append] using
              Execution.prepend_emission_witness (.jump g) _ _ heG hdG tail
          | flow fB =>
            rcases lt_trichotomy vA.time vB.time with hshort | hequal | hlong
            · have hprefix : sB.time < vA.time := by rw [← hstart]; exact fA.positive
              let prefixB := fB.prefix hprefix hshort.le
              let suffixB := fB.suffix hprefix.le hshort
              let remainingB : Execution θB (fun _ _ => []) (fB.at vA.time) uB := .cons (.flow suffixB) restB
              let combined := fA.product prefixB hstart rfl Q
                (fun d hd => restA.time_monotone.trans (hQ d hd))
              have tail := recurse restA remainingB
                (by simp only [remainingB,Execution.moveCount] at hsize ⊢; omega) rfl heRA hdRA
                (by change [] ++ restB.deliveries = []; simpa using hdRB)
              simpa only [remainingB,Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero,List.nil_append] using
                Execution.prepend_emission_witness (.flow combined) [] _ rfl rfl tail
            · let combined := fA.product fB hstart hequal Q
                (fun d hd => restA.time_monotone.trans (hQ d hd))
              have tail := recurse restA restB (by simp only [Execution.moveCount] at hsize ⊢; omega)
                hequal heRA hdRA hdRB
              simpa only [Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero,List.nil_append] using
                Execution.prepend_emission_witness (.flow combined) [] _ rfl rfl tail
            · have hprefix : sA.time < vB.time := by rw [hstart]; exact fB.positive
              let prefixA := fA.prefix hprefix hlong.le
              let suffixA := fA.suffix hprefix.le hlong
              let remainingA : Execution θA routeA (fA.at vB.time) uA := .cons (.flow suffixA) restA
              let combined := prefixA.product fB hstart rfl Q (by
                intro d hd
                change vB.time ≤ d.due
                rw [hfinish] at hQ
                exact restB.time_monotone.trans (hQ d hd))
              have tail := recurse remainingA restB
                (by simp only [remainingA,Execution.moveCount] at hsize ⊢; omega) rfl
                (by change [] ++ restA.ledger.emissions = []; simpa using heRA)
                (by change [] ++ restA.deliveries = []; simpa using hdRA) hdRB
              simpa only [Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero,List.nil_append] using
                Execution.prepend_emission_witness (.flow combined) [] _ rfl rfl tail

end KernelR.Hybrid
