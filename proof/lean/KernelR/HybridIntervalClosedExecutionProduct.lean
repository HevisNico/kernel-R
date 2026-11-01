import KernelR.HybridRightClosedExecutionProduct

/-! Products with an emitting left cell and a neutral right cell. Contact
closure is required only on the constructed time interval. -/
namespace KernelR.Hybrid

/-- Lift a genuine left FIRE with a closed contact, retaining its emission. -/
theorem Jump.product_left_closed {sA uA : Snapshot 1}
    (j : Jump (fun _ _ => []) sA uA) (hd : j.deliveries = [])
    (sB : Snapshot 1) (Q : List (Delivery 2)) (route : Router 2)
    (hclosed : route 0 sA.time = []) :
    ∃ g : Jump route (sA.product sB Q) (uA.product sB Q),
      g.ledger.emissions = j.ledger.emissions.map (fun event => (0,event.2)) ∧ g.deliveries = [] := by
  by_cases he : j.ledger.emissions = []
  · obtain ⟨g,hg,hdg⟩ := j.product_left_empty (j.queueNeutral_of_no_events he hd) sB Q route
    refine ⟨g,?_,hdg⟩
    rw [he,List.map_nil]
    exact hg
  · cases j <;> try exact False.elim (he rfl)
    case fire i hm hq =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      let before := sA.product sB Q
      let after := ({(setMain sA 0 .fast) with pending := sA.pending ++ []} : Snapshot 1).product sB Q
      have heq : after = {(setMain before 0 .fast) with pending := before.pending ++ route 0 before.time} := by
        change (setMain sA 0 .fast).product sB Q =
          {(setMain (sA.product sB Q) 0 .fast) with pending := Q ++ route 0 sA.time}
        rw [hclosed,List.append_nil,Snapshot.product_setMain_left]
        rfl
      let g : Jump route before after := heq.symm ▸ Jump.fire before 0 hm hq
      have hfast : after.main 0 = .fast := by
        change (setMain sA 0 .fast).main 0 = .fast
        simp [setMain]
      have hgem : g.ledger.emissions = [(0,before.time)] :=
        g.ready_main_departure_emission 0 hm (by rw [hfast]; decide)
      have hgdel : g.deliveries = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro d hdg
        have hz := g.no_emissions_of_delivery d hdg
        rw [hgem] at hz
        contradiction
      refine ⟨g,?_,hgdel⟩
      rw [hgem]
      rfl

/-- Weave a left emitting execution and a right neutral continuation. The
left route may have been open before the initial clock. -/
theorem Execution.product_left_closed_on {θA θB : Fin 1 → Parameters} {routeB : Router 1}
    {sA uA sB uB : Snapshot 1} (eA : Execution θA (fun _ _ => []) sA uA)
    (eB : Execution θB routeB sB uB)
    (hstart : sA.time = sB.time) (hfinish : uA.time = uB.time)
    (hdA : eA.deliveries = []) (heB : eB.ledger.emissions = []) (hdB : eB.deliveries = [])
    (Q : List (Delivery 2)) (hQ : ∀ d ∈ Q, uA.time ≤ d.due) (route : Router 2)
    (hclosed : ∀ t, sA.time ≤ t → t ≤ uA.time → route 0 t = []) :
    ∃ e : Execution (extendParameters θA (θB 0)) route (sA.product sB Q) (uA.product uB Q),
      e.ledger.emissions = eA.ledger.emissions.map (fun event => (0,event.2)) ∧ e.deliveries = [] := by
  let start := sA.time
  suffices aux : ∀ N : ℕ, ∀ {a b : Snapshot 1}
      (l : Execution θA (fun _ _ => []) a uA) (r : Execution θB routeB b uB),
      l.moveCount + r.moveCount = N → a.time = b.time → start ≤ a.time →
      l.deliveries = [] → r.ledger.emissions = [] → r.deliveries = [] →
      ∃ e : Execution (extendParameters θA (θB 0)) route (a.product b Q) (uA.product uB Q),
        e.ledger.emissions = l.ledger.emissions.map (fun event => (0,event.2)) ∧ e.deliveries = [] by
    exact aux _ eA eB rfl hstart le_rfl hdA heB hdB
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro sA sB eA eB hsize hstart hlo hdA heB hdB
    have recurse {a b : Snapshot 1} (l : Execution θA (fun _ _ => []) a uA)
        (r : Execution θB routeB b uB)
        (hdec : l.moveCount + r.moveCount < N) (hsync : a.time = b.time) (hl : start ≤ a.time)
        (hdl : l.deliveries = []) (her : r.ledger.emissions = []) (hdr : r.deliveries = []) :
        ∃ e : Execution (extendParameters θA (θB 0)) route (a.product b Q) (uA.product uB Q),
          e.ledger.emissions = l.ledger.emissions.map (fun event => (0,event.2)) ∧ e.deliveries = [] :=
      ih _ hdec l r rfl hsync hl hdl her hdr
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
          have tail := recurse (Execution.nil (θ := θA) (route := fun _ _ => []) uA) restB
            (by simp only [Execution.moveCount] at hsize ⊢; omega)
            (hstart.trans jB.time_unchanged.symm) hlo rfl heRB hdRB
          simpa only [List.nil_append] using
            Execution.prepend_emission_witness (.jump g) [] _ heG hdG tail
    | @cons _ vA _ mA restA =>
      change mA.deliveries ++ restA.deliveries = [] at hdA
      obtain ⟨hdMA,hdRA⟩ := List.append_eq_nil_iff.mp hdA
      cases mA with
      | jump jA =>
        have htime : sA.time ≤ uA.time := by
          have h := restA.time_monotone
          rwa [jA.time_unchanged] at h
        obtain ⟨g,heG,hdG⟩ := jA.product_left_closed hdMA sB Q route (hclosed _ hlo htime)
        have tail := recurse restA eB (by simp only [Execution.moveCount] at hsize ⊢; omega)
          (jA.time_unchanged.trans hstart) (by rwa [jA.time_unchanged]) hdRA heB hdB
        simpa only [Execution.ledger,Move.ledger,Ledger.add,List.map_append] using
          Execution.prepend_emission_witness (.jump g) _ _ heG hdG tail
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
            have tail := recurse (Execution.cons (.flow fA) restA) restB
              (by simp only [Execution.moveCount] at hsize ⊢; omega)
              (hstart.trans jB.time_unchanged.symm) hlo
              (by change [] ++ restA.deliveries = []; simpa using hdRA) heRB hdRB
            simpa only [List.nil_append] using
              Execution.prepend_emission_witness (.jump g) [] _ heG hdG tail
          | flow fB =>
            rcases lt_trichotomy vA.time vB.time with hshort | hequal | hlong
            · have hprefix : sB.time < vA.time := by rw [← hstart]; exact fA.positive
              let prefixB := fB.prefix hprefix hshort.le
              let suffixB := fB.suffix hprefix.le hshort
              let remainingB : Execution θB routeB (fB.at vA.time) uB := .cons (.flow suffixB) restB
              let combined := fA.product prefixB hstart rfl Q
                (fun d hd => restA.time_monotone.trans (hQ d hd))
              have tail := recurse restA remainingB
                (by simp only [remainingB,Execution.moveCount] at hsize ⊢; omega) rfl
                (hlo.trans fA.positive.le) hdRA
                (by change [] ++ restB.ledger.emissions = []; simpa using heRB)
                (by change [] ++ restB.deliveries = []; simpa using hdRB)
              simpa only [Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero,List.nil_append] using
                Execution.prepend_emission_witness (.flow combined) [] _ rfl rfl tail
            · let combined := fA.product fB hstart hequal Q
                (fun d hd => restA.time_monotone.trans (hQ d hd))
              have tail := recurse restA restB (by simp only [Execution.moveCount] at hsize ⊢; omega)
                hequal (hlo.trans fA.positive.le) hdRA heRB hdRB
              simpa only [Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero,List.nil_append] using
                Execution.prepend_emission_witness (.flow combined) [] _ rfl rfl tail
            · have hprefix : sA.time < vB.time := by rw [hstart]; exact fB.positive
              let prefixA := fA.prefix hprefix hlong.le
              let suffixA := fA.suffix hprefix.le hlong
              let remainingA : Execution θA (fun _ _ => []) (fA.at vB.time) uA := .cons (.flow suffixA) restA
              let combined := prefixA.product fB hstart rfl Q (by
                intro d hd
                change vB.time ≤ d.due
                rw [hfinish] at hQ
                exact restB.time_monotone.trans (hQ d hd))
              have tail := recurse remainingA restB
                (by simp only [remainingA,Execution.moveCount] at hsize ⊢; omega) rfl
                (hlo.trans hprefix.le)
                (by change [] ++ restA.deliveries = []; simpa using hdRA) heRB hdRB
              simpa only [remainingA,Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero,List.nil_append] using
                Execution.prepend_emission_witness (.flow combined) [] _ rfl rfl tail

/-- The right emitting case, with contact closure restricted to its actual time span. -/
theorem Execution.product_right_closed_on {θA θB : Fin 1 → Parameters} {routeA : Router 1}
    {sA uA sB uB : Snapshot 1} (eA : Execution θA routeA sA uA)
    (eB : Execution θB (fun _ _ => []) sB uB)
    (hstart : sA.time = sB.time) (hfinish : uA.time = uB.time)
    (heA : eA.ledger.emissions = []) (hdA : eA.deliveries = []) (hdB : eB.deliveries = [])
    (Q : List (Delivery 2)) (hQ : ∀ d ∈ Q, uA.time ≤ d.due) (route : Router 2)
    (hclosed : ∀ t, sB.time ≤ t → t ≤ uB.time → route 1 t = []) :
    ∃ e : Execution (extendParameters θA (θB 0)) route (sA.product sB Q) (uA.product uB Q),
      e.ledger.emissions = eB.ledger.emissions.map (fun event => (1,event.2)) ∧ e.deliveries = [] := by
  let start := sB.time
  suffices aux : ∀ N : ℕ, ∀ {a b : Snapshot 1}
      (l : Execution θA routeA a uA) (r : Execution θB (fun _ _ => []) b uB),
      l.moveCount + r.moveCount = N → a.time = b.time → start ≤ b.time →
      l.ledger.emissions = [] → l.deliveries = [] → r.deliveries = [] →
      ∃ e : Execution (extendParameters θA (θB 0)) route (a.product b Q) (uA.product uB Q),
        e.ledger.emissions = r.ledger.emissions.map (fun event => (1,event.2)) ∧ e.deliveries = [] by
    exact aux _ eA eB rfl hstart le_rfl heA hdA hdB
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro sA sB eA eB hsize hstart hlo heA hdA hdB
    have recurse {a b : Snapshot 1} (l : Execution θA routeA a uA)
        (r : Execution θB (fun _ _ => []) b uB)
        (hdec : l.moveCount + r.moveCount < N) (hsync : a.time = b.time) (hl : start ≤ b.time)
        (hel : l.ledger.emissions = []) (hdl : l.deliveries = []) (hdr : r.deliveries = []) :
        ∃ e : Execution (extendParameters θA (θB 0)) route (a.product b Q) (uA.product uB Q),
          e.ledger.emissions = r.ledger.emissions.map (fun event => (1,event.2)) ∧ e.deliveries = [] :=
      ih _ hdec l r rfl hsync hl hel hdl hdr
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
          obtain ⟨g,heG,hdG⟩ := jB.product_right_closed hdMB uA hstart Q route (hclosed _ hlo htime)
          have tail := recurse (Execution.nil (θ := θA) (route := routeA) uA) restB
            (by simp only [Execution.moveCount] at hsize ⊢; omega)
            (hstart.trans jB.time_unchanged.symm) (by rwa [jB.time_unchanged]) rfl rfl hdRB
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
          (jA.time_unchanged.trans hstart) hlo heRA hdRA hdB
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
            obtain ⟨g,heG,hdG⟩ := jB.product_right_closed hdMB sA hstart Q route (hclosed _ hlo htime)
            have tail := recurse (Execution.cons (.flow fA) restA) restB
              (by simp only [Execution.moveCount] at hsize ⊢; omega)
              (hstart.trans jB.time_unchanged.symm) (by rwa [jB.time_unchanged])
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
                (by simp only [remainingB,Execution.moveCount] at hsize ⊢; omega) rfl
                (hlo.trans hprefix.le) heRA hdRA
                (by change [] ++ restB.deliveries = []; simpa using hdRB)
              simpa only [remainingB,Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero,List.nil_append] using
                Execution.prepend_emission_witness (.flow combined) [] _ rfl rfl tail
            · let combined := fA.product fB hstart hequal Q
                (fun d hd => restA.time_monotone.trans (hQ d hd))
              have tail := recurse restA restB (by simp only [Execution.moveCount] at hsize ⊢; omega)
                hequal (hlo.trans fB.positive.le) heRA hdRA hdRB
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
                (by simp only [remainingA,Execution.moveCount] at hsize ⊢; omega) rfl (hlo.trans fB.positive.le)
                (by change [] ++ restA.ledger.emissions = []; simpa using heRA)
                (by change [] ++ restA.deliveries = []; simpa using hdRA) hdRB
              simpa only [Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero,List.nil_append] using
                Execution.prepend_emission_witness (.flow combined) [] _ rfl rfl tail

end KernelR.Hybrid
