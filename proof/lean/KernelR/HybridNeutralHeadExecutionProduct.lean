import KernelR.HybridQuietHeadNeutralProduct
import KernelR.HybridNeutralExecutionProduct

/-! Weave a genuine non-emitting head-cell execution with a genuine neutral
network execution. The head may retain active RAW, auxiliary modes, and all
physical residues; only the network's exact queue occurs in the product. -/
namespace KernelR.Hybrid

@[simp] theorem Snapshot.prependQuiet_setMain_head {n} (s : Snapshot n) (a : Snapshot 1)
    (mode : MainMode) :
    s.prependQuiet (setMain a 0 mode) = setMain (s.prependQuiet a) 0 mode := by
  cases s
  cases a
  simp only [Snapshot.prependQuiet,setMain]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.succ_ne_zero]

@[simp] theorem Snapshot.prependQuiet_setAux_head {n} (s : Snapshot n) (a : Snapshot 1)
    (p : Port) (mode : AuxMode) :
    s.prependQuiet (setAux a 0 p mode) = setAux (s.prependQuiet a) 0 p mode := by
  cases s
  cases a
  simp only [Snapshot.prependQuiet,setAux]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.succ_ne_zero]

@[simp] theorem Snapshot.prependQuiet_setRaw_head {n} (s : Snapshot n) (a : Snapshot 1)
    (p : Port) (origin : Option ℝ) :
    s.prependQuiet (setRaw a 0 p origin) = setRaw (s.prependQuiet a) 0 p origin := by
  cases s
  cases a
  simp only [Snapshot.prependQuiet,setRaw]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.succ_ne_zero]

/-- Actual guard/expiry jumps of the head cell lift without changing the
network's queue. Head FIRE and arrivals are excluded by their actual ledgers. -/
theorem Jump.prependHead_neutral {route : Router 1} {a b : Snapshot 1}
    (j : Jump route a b) (he : j.ledger.emissions = []) (hd : j.deliveries = [])
    {n} (s : Snapshot n) (hstart : s.time = a.time) (global : Router (n + 1)) :
    ∃ lifted : Jump global (s.prependQuiet a) (s.prependQuiet b),
      lifted.ledger.emissions = [] ∧ lifted.deliveries = [] := by
  cases j with
  | fire i hm hq =>
    change [(i,a.time)] = [] at he
    contradiction
  | arrive d before after hq ht hf =>
    change [d] = [] at hd
    contradiction
  | fastEnd i hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.prependQuiet_setMain_head]
    exact ⟨.fastEnd _ 0 hm hq,rfl,rfl⟩
  | reopen i hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.prependQuiet_setMain_head]
    exact ⟨.reopen _ 0 hm hq,rfl,rfl⟩
  | mark i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.prependQuiet_setAux_head]
    exact ⟨.mark _ 0 p hm hq,rfl,rfl⟩
  | silent i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.prependQuiet_setAux_head]
    exact ⟨.silent _ 0 p hm hq,rfl,rfl⟩
  | error i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.prependQuiet_setAux_head]
    exact ⟨.error _ 0 p hm hq,rfl,rfl⟩
  | auxReady i p hm hq =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.prependQuiet_setAux_head]
    exact ⟨.auxReady _ 0 p hm hq,rfl,rfl⟩
  | rawEnd i p origin hr ht =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Snapshot.prependQuiet_setRaw_head]
    exact ⟨.rawEnd _ 0 p origin hr (hstart.trans ht),rfl,rfl⟩

private theorem prepend_no_emission {n θ route s v u}
    (move : @Move n θ route s v) (he : move.ledger.emissions = [])
    (D : List (Delivery n))
    (tail : ∃ e : Execution θ route v u, e.ledger.emissions = [] ∧ e.deliveries = D) :
    ∃ e : Execution θ route s u,
      e.ledger.emissions = [] ∧ e.deliveries = move.deliveries ++ D := by
  obtain ⟨e,heE,hdE⟩ := tail
  refine ⟨.cons move e,?_,?_⟩
  · change move.ledger.emissions ++ e.ledger.emissions = []
    rw [he,heE]
    rfl
  · change move.deliveries ++ e.deliveries = _
    rw [hdE]

/-- Finite weaving of a neutral active network with a neutral head path.
Every original positive flow is retained or cut with its own actual path.
No READY section or absent-RAW premise is imposed on the head cell. -/
theorem Execution.prepend_neutral {n θ θA route routeA s u a b}
    (eTail : @Execution n θ route s u) (eHead : @Execution 1 θA routeA a b)
    (hstart : s.time = a.time) (hfinish : u.time = b.time)
    (heTail : eTail.ledger.emissions = []) (heHead : eHead.ledger.emissions = [])
    (hdHead : eHead.deliveries = []) (_hHeadPending : a.pending = [])
    (global : Router (n + 1)) :
    ∃ e : Execution (prependParameters θA θ) global (s.prependQuiet a) (u.prependQuiet b),
      e.ledger.emissions = [] ∧ e.deliveries = eTail.deliveries.map Delivery.succ := by
  suffices aux : ∀ N : ℕ, ∀ {t : Snapshot n} {h : Snapshot 1}
      (tail : Execution θ route t u) (head : Execution θA routeA h b),
      tail.moveCount + head.moveCount = N → t.time = h.time →
      tail.ledger.emissions = [] → head.ledger.emissions = [] → head.deliveries = [] →
      ∃ e : Execution (prependParameters θA θ) global (t.prependQuiet h) (u.prependQuiet b),
        e.ledger.emissions = [] ∧ e.deliveries = tail.deliveries.map Delivery.succ by
    exact aux _ eTail eHead rfl hstart heTail heHead hdHead
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro s a eT eH hsize hstart heT heH hdH
    have recurse {t : Snapshot n} {h : Snapshot 1}
        (tail : Execution θ route t u) (head : Execution θA routeA h b)
        (hdec : tail.moveCount + head.moveCount < N) (hsync : t.time = h.time)
        (het : tail.ledger.emissions = []) (heh : head.ledger.emissions = [])
        (hdh : head.deliveries = []) :
        ∃ e : Execution (prependParameters θA θ) global (t.prependQuiet h) (u.prependQuiet b),
          e.ledger.emissions = [] ∧ e.deliveries = tail.deliveries.map Delivery.succ :=
      ih _ hdec tail head rfl hsync het heh hdh
    cases eT with
    | nil =>
      cases eH with
      | nil => exact ⟨.nil _,rfl,rfl⟩
      | @cons _ vH _ mH restH =>
        have hheadE : mH.ledger.emissions = [] ∧ restH.ledger.emissions = [] := List.append_eq_nil_iff.mp heH
        have hheadD : mH.deliveries = [] ∧ restH.deliveries = [] := List.append_eq_nil_iff.mp hdH
        cases mH with
        | flow fH => exact False.elim (by linarith [fH.positive,restH.time_monotone])
        | jump jH =>
          obtain ⟨g,heG,hdG⟩ := jH.prependHead_neutral hheadE.1 hheadD.1 u hstart global
          have remaining := recurse (Execution.nil (θ := θ) (route := route) u) restH
            (by simp only [Execution.moveCount] at hsize ⊢; omega)
            (hstart.trans jH.time_unchanged.symm) rfl hheadE.2 hheadD.2
          simpa only [Move.deliveries,hdG,List.nil_append] using
            prepend_no_emission (.jump g) heG _ remaining
    | @cons _ vT _ mT restT =>
      have htailE : mT.ledger.emissions = [] ∧ restT.ledger.emissions = [] := List.append_eq_nil_iff.mp heT
      cases mT with
      | jump jT =>
        obtain ⟨g,heG,hdG⟩ := jT.prependQuiet_neutral htailE.1 a global
        have remaining := recurse restT eH (by simp only [Execution.moveCount] at hsize ⊢; omega)
          (jT.time_unchanged.trans hstart) htailE.2 heH hdH
        simpa only [Move.deliveries,hdG,Execution.deliveries,List.map_append] using
          prepend_no_emission (.jump g) heG _ remaining
      | flow fT =>
        cases eH with
        | nil => exact False.elim (by linarith [fT.positive,restT.time_monotone])
        | @cons _ vH _ mH restH =>
          have hheadE : mH.ledger.emissions = [] ∧ restH.ledger.emissions = [] := List.append_eq_nil_iff.mp heH
          have hheadD : mH.deliveries = [] ∧ restH.deliveries = [] := List.append_eq_nil_iff.mp hdH
          cases mH with
          | jump jH =>
            obtain ⟨g,heG,hdG⟩ := jH.prependHead_neutral hheadE.1 hheadD.1 s hstart global
            have remaining := recurse (Execution.cons (.flow fT) restT) restH
              (by simp only [Execution.moveCount] at hsize ⊢; omega)
              (hstart.trans jH.time_unchanged.symm)
              (by change [] ++ restT.ledger.emissions = []; simpa using htailE.2)
              hheadE.2 hheadD.2
            simpa only [Move.deliveries,hdG,List.nil_append] using
              prepend_no_emission (.jump g) heG _ remaining
          | flow fH =>
            rcases lt_trichotomy vT.time vH.time with hshort | hequal | hlong
            · have hprefix : a.time < vT.time := by rw [← hstart]; exact fT.positive
              let prefixH := fH.prefix hprefix hshort.le
              let suffixH := fH.suffix hprefix.le hshort
              let remainingH : Execution θA routeA (fH.at vT.time) b := .cons (.flow suffixH) restH
              let combined := fT.prependQuiet prefixH hstart rfl
              have remaining := recurse restT remainingH
                (by simp only [remainingH,Execution.moveCount] at hsize ⊢; omega) rfl htailE.2
                (by change [] ++ restH.ledger.emissions = []; simpa using hheadE.2)
                (by change [] ++ restH.deliveries = []; simpa using hheadD.2)
              simpa only [Move.deliveries,List.nil_append,Execution.deliveries,List.map_nil] using
                prepend_no_emission (.flow combined) rfl _ remaining
            · let combined := fT.prependQuiet fH hstart hequal
              have remaining := recurse restT restH (by simp only [Execution.moveCount] at hsize ⊢; omega)
                hequal htailE.2 hheadE.2 hheadD.2
              simpa only [Move.deliveries,List.nil_append,Execution.deliveries,List.map_nil] using
                prepend_no_emission (.flow combined) rfl _ remaining
            · have hprefix : s.time < vH.time := by rw [hstart]; exact fH.positive
              let prefixT := fT.prefix hprefix hlong.le
              let suffixT := fT.suffix hprefix.le hlong
              let remainingT : Execution θ route (fT.at vH.time) u := .cons (.flow suffixT) restT
              let combined := prefixT.prependQuiet fH hstart rfl
              have remaining := recurse remainingT restH
                (by simp only [remainingT,Execution.moveCount] at hsize ⊢; omega) rfl
                (by change [] ++ restT.ledger.emissions = []; simpa using htailE.2) hheadE.2 hheadD.2
              simpa only [remainingT,Move.deliveries,List.nil_append,Execution.deliveries,List.map_nil] using
                prepend_no_emission (.flow combined) rfl _ remaining

end KernelR.Hybrid
