import KernelR.HybridTeachingQueueClosure
import KernelR.HybridFeedbackCalendar
/-! The old cells reach C's introduction without resetting the source due at 480. -/
namespace KernelR.Hybrid

/-- The terminal-source queue/raw dichotomy is local to one receiving cell;
routes and arrivals at every other cell remain part of the same execution. -/
theorem Execution.cell_terminal_source_queue {n θ route s u} (e : @Execution n θ route s u)
    (d : Delivery n) (later : List (Delivery n))
    (hq : (s.pending.filter (fun f => f.cell = d.cell)).Perm (d :: later))
    (hdate : d.due = u.time) (hlater : ∀ f ∈ later, u.time < f.due)
    (hraw : s.raw d.cell d.port = none)
    (hr : ∀ event ∈ e.ledger.emissions, ∀ f ∈ route event.1 event.2, f.cell ≠ d.cell) :
    (e.cellDeliveries d.cell = [] ∧ u.raw d.cell d.port = none ∧
      (u.pending.filter (fun f => f.cell = d.cell)).Perm (d :: later)) ∨
    (e.cellDeliveries d.cell = [d] ∧ u.raw d.cell d.port = some u.time ∧
      (u.pending.filter (fun f => f.cell = d.cell)).Perm later) := by
  classical
  have his := e.cell_due_routed_empty d.cell hr
  have hp := congrArg (Multiset.filter (fun f : Delivery n => f.cell = d.cell)) e.token_balance
  simp only [Multiset.filter_add,Multiset.filter_coe,his,Multiset.coe_nil,add_zero] at hp
  have hs : (s.pending.filter (fun f => f.cell = d.cell) : Multiset (Delivery n)) =
      ((d :: later : List (Delivery n)) : Multiset (Delivery n)) := Quot.sound hq
  rw [hs] at hp
  have hpartition : ((u.pending.filter (fun f => f.cell = d.cell)) ++ e.cellDeliveries d.cell).Perm (d :: later) :=
    Quotient.exact hp
  have hnot : d ∉ later := by
    intro hd
    have ht := hlater d hd
    rw [hdate] at ht
    exact lt_irrefl _ ht
  have honly : ∀ f ∈ e.cellDeliveries d.cell, f = d := by
    intro f hf
    have hm : f ∈ e.deliveries ∧ f.cell = d.cell := by
      simpa only [Execution.cellDeliveries,List.mem_filter,decide_eq_true_eq] using hf
    rcases e.delivery_provenance f hm.1 with hsource | ⟨event,he,hroute⟩
    · have hmem : f ∈ s.pending.filter (fun f => f.cell = d.cell) := by
        simp only [List.mem_filter,decide_eq_true_eq]
        exact ⟨hsource,hm.2⟩
      have hs' := hq.mem_iff.mp hmem
      rcases List.mem_cons.mp hs' with h | h
      · exact h
      · exact False.elim (not_lt_of_ge (e.delivery_time_bounds f hm.1).2 (hlater f h))
    · exact False.elim (hr event he f hroute hm.2)
  have hdeliveries : e.cellDeliveries d.cell = [] ∨ e.cellDeliveries d.cell = [d] := by
    cases he : e.cellDeliveries d.cell with
    | nil => exact Or.inl rfl
    | cons first rest =>
      have hfirst : first = d := honly first (by rw [he]; simp)
      subst first
      cases rest with
      | nil => exact Or.inr rfl
      | cons second tail =>
        have hsecond : second = d := honly second (by rw [he]; simp)
        subst second
        have hc := hpartition.count_eq d
        simp only [he,List.count_append,List.count_cons_self,List.count_eq_zero_of_not_mem hnot] at hc
        omega
  rcases hdeliveries with he | he
  · left
    refine ⟨he,?_,?_⟩
    · exact (e.raw_absent_of_no_arrival d.cell d.port hraw ((e.cellDeliveries_empty_iff d.cell).mp he d.port)).1
    · simpa only [he,List.append_nil] using hpartition
  · right
    obtain ⟨cut⟩ := e.first_cell_delivery d.cell d [] he
    have hafter : cut.afterArrival.time = u.time := cut.date.2.trans hdate
    have hcurrent := cut.rest.raw_persists d.cell d.port cut.afterArrival.time cut.raw_after (by rw [hafter]; linarith)
    refine ⟨he,by simpa only [hafter] using hcurrent,?_⟩
    apply e.cell_pending_perm_of_prefix d.cell [d] later
      (by simpa only [List.singleton_append] using hq) (List.Perm.of_eq he) hr

/-- Prepared rest survives until terminal-date arrivals at this cell. Other
cells' arrivals and events are retained in the isolated cell prefixes. -/
theorem Execution.idle_prepared_cell_boundary {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : PreparedSection s i) (hq : s.x i .q = 1 / 10)
    (hr : ∀ p, s.raw i p = none) (hdates : ∀ d ∈ e.cellDeliveries i, d.due = u.time) :
    Nonempty (IdlePrepared e i) := by
  cases he : e.cellDeliveries i with
  | nil =>
    exact e.idle_prepared i hs hq hr ((e.cellDeliveries_empty_iff i).mp he)
  | cons d ds =>
    obtain ⟨cut⟩ := e.first_cell_delivery i d ds he
    have hdate := hdates d (by rw [he]; simp)
    obtain ⟨idle⟩ := cut.span.idle_prepared i hs hq hr cut.no_arrivals_before
    have hafter : cut.afterArrival.time = u.time := cut.date.2.trans hdate
    have hx : u.x = cut.beforeArrival.x := by
      rw [cut.rest.zero_duration_continuous hafter.symm,cut.entry.physical_continuous]
    have hm : cut.afterArrival.main i = .ready := by rw [cut.modes_after.1]; exact idle.prepared.ready
    have ha : ∀ p, cut.afterArrival.aux i p = .ready := by
      intro p
      rw [cut.modes_after.2]
      exact (idle.prepared.auxiliary p).1
    have hmain := cut.rest.zero_duration_ready_main hafter.symm i hm (by
      rw [cut.entry.physical_continuous,idle.charge_rest]; norm_num)
    have haux : ∀ p, cut.rest.AllStates (fun v => v.aux i p = .ready) := by
      intro p
      apply cut.rest.zero_duration_ready_aux hafter.symm i p (ha p)
      rw [cut.entry.physical_continuous]
      have hb := (idle.prepared.auxiliary p).2.2
      intro h
      rw [h] at hb
      norm_num at hb
    have hem : e.emissionTimes i = [] := by
      have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
      apply e.no_emissions_of_split cut.span cut.entry cut.rest cut.reconstruct i idle.emissions
        (by rw [cut.entry.no_emissions_of_delivery d hd]; rfl)
      exact cut.rest.no_emissions_of_ready_states i hmain
    refine ⟨⟨⟨cut.rest.allStates_final hmain,?_,?_,?_⟩,?_,?_,?_,hem⟩⟩
    · rw [hx]; exact idle.prepared.charge
    · rw [hx]; exact idle.prepared.recovery
    · intro p
      exact ⟨cut.rest.allStates_final (haux p),by rw [hx]; exact (idle.prepared.auxiliary p).2⟩
    · rw [hx]; exact idle.charge_rest
    · intro p
      rw [hx]; exact idle.gain_preserved p
    · rw [hx]; exact idle.recovery_preserved

structure CIntroductionBoundary {θ route s u} (e : @Execution 2 θ route s u) where
  a_idle : IdlePrepared e 0
  b_idle : IdlePrepared e 1
  a_raw : ∀ p, u.raw 0 p = none
  a_queue : u.pending.filter (fun d => d.cell = 0) = []
  b_raw_other : ∀ p, p ≠ 2 → u.raw 1 p = none
  b_boundary :
    (u.raw 1 2 = none ∧ (u.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 480 8 16)) ∨
    (u.raw 1 2 = some u.time ∧ (u.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 488 8 15))

/-- Both old cells stay prepared up to C's birth date. Source 480 may be
pending or already fresh on B; neither event order resets any memory. -/
theorem Execution.c_introduction_boundary {θ s u} (forward backward : ℝ → ℝ)
    (e : @Execution 2 θ (reciprocalEntryRouter forward backward) s u)
    (hsA : PreparedSection s 0) (hqA : s.x 0 .q = 1 / 10) (hrA : ∀ p, s.raw 0 p = none)
    (hsB : PreparedSection s 1) (hqB : s.x 1 .q = 1 / 10) (hrB : ∀ p, s.raw 1 p = none)
    (hAempty : s.pending.filter (fun d => d.cell = 0) = [])
    (hBqueue : (s.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 480 8 16))
    (ht : s.time = 4599 / 10) (hu : u.time = 480) (hpf : PendingFuture s)
    (hforward : ∀ t, 0 ≤ forward t) (hbackward : ∀ t, 0 ≤ backward t) :
    Nonempty (CIntroductionBoundary e) := by
  have htime : ∀ event ∈ e.ledger.emissions, 310 ≤ event.2 := by
    intro event he
    have h := (e.emission_time_bounds event he).1
    rw [ht] at h
    linarith
  have hclosedB : ∀ event ∈ e.ledger.emissions,
      ∀ d ∈ reciprocalEntryRouter forward backward event.1 event.2, d.cell ≠ 1 := by
    intro event he
    exact reciprocalEntryRouter.closed_to_b forward backward event.1 (htime event he)
  have htrain : sourceTrain (1 : Fin 2) 2 480 8 16 = ⟨1,2,480⟩ :: sourceTrain 1 2 488 8 15 := by
    simpa only [show (480 : ℝ) + 8 = 488 by norm_num] using sourceTrain_succ (1 : Fin 2) 2 480 8 15
  have hqinit : (s.pending.filter (fun d => d.cell = 1)).Perm (⟨1,2,480⟩ :: sourceTrain 1 2 488 8 15) :=
    hBqueue.trans (List.Perm.of_eq htrain)
  have hlater : ∀ d ∈ sourceTrain (1 : Fin 2) 2 488 8 15, u.time < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    rw [hu]
    change (480 : ℝ) < 488 + 8 * (k.val : ℝ)
    linarith
  have hboundary := e.cell_terminal_source_queue ⟨1,2,480⟩ (sourceTrain 1 2 488 8 15)
    hqinit hu.symm hlater (hrB 2) hclosedB
  have hdatesB : ∀ d ∈ e.cellDeliveries 1, d.due = u.time := by
    rcases hboundary with ⟨he,hraw,hqueue⟩ | ⟨he,hraw,hqueue⟩
    · intro d hd
      rw [he] at hd
      contradiction
    · intro d hd
      rw [he] at hd
      simp only [List.mem_singleton] at hd
      subst d
      exact hu.symm
  obtain ⟨idleB⟩ := e.idle_prepared_cell_boundary 1 hsB hqB hrB hdatesB
  have hnoIncomingA : ∀ event ∈ e.ledger.emissions,
      ∀ d ∈ reciprocalEntryRouter forward backward event.1 event.2, d.cell ≠ 0 := by
    intro event he d hd _
    rw [reciprocalEntryRouter.after_forward forward backward event.1 (htime event he)] at hd
    unfold Contact.route at hd
    split_ifs at hd with h
    · have hcell : event.1 = (1 : Fin 2) := h.1
      have hm : event.2 ∈ e.emissionTimes 1 := by
        apply List.mem_map.mpr
        exact ⟨event,by simp [List.mem_filter,he,hcell],rfl⟩
      rw [idleB.emissions] at hm
      contradiction
    · contradiction
  have hnoA : ∀ p, NoArrivalAt e 0 p := by
    apply e.no_arrival_before_due 0
    · intro d hd hc
      have hm : d ∈ s.pending.filter (fun d => d.cell = 0) := by
        simp only [List.mem_filter,decide_eq_true_eq]
        exact ⟨hd,hc⟩
      rw [hAempty] at hm
      contradiction
    · intro event he d hd hc
      exact False.elim (hnoIncomingA event he d hd hc)
  obtain ⟨idleA⟩ := e.idle_prepared 0 hsA hqA hrA hnoA
  have hfuture : PendingFuture u := e.pending_future (reciprocalEntryRouter.causal forward backward hforward hbackward) hpf
  have hAfinal := e.cell_pending_empty_strict 0 hfuture
    (by
      intro d hd hc
      have hm : d ∈ s.pending.filter (fun d => d.cell = 0) := by
        simp only [List.mem_filter,decide_eq_true_eq]
        exact ⟨hd,hc⟩
      rw [hAempty] at hm
      contradiction)
    (fun event he d hd hc => False.elim (hnoIncomingA event he d hd hc))
  have hrawA : ∀ p, u.raw 0 p = none := fun p => (e.raw_absent_of_no_arrival 0 p (hrA p) (hnoA p)).1
  have hrawBother : ∀ p, p ≠ 2 → u.raw 1 p = none := by
    intro p hp
    apply (e.raw_absent_of_no_arrival 1 p (hrB p) ?_).1
    intro d hd
    by_cases hc : d.cell = (1 : Fin 2)
    · have hm : d ∈ e.cellDeliveries 1 := by simp [Execution.cellDeliveries,List.mem_filter,hd,hc]
      rcases hboundary with ⟨he,hraw,hqueue⟩ | ⟨he,hraw,hqueue⟩
      · rw [he] at hm
        contradiction
      · rw [he] at hm
        simp only [List.mem_singleton] at hm
        subst d
        exact Or.inr (Ne.symm hp)
    · exact Or.inl hc
  have hqueueBoundary :
      (u.raw 1 2 = none ∧ (u.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 480 8 16)) ∨
      (u.raw 1 2 = some u.time ∧ (u.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 488 8 15)) := by
    rcases hboundary with ⟨he,hraw,hqueue⟩ | ⟨he,hraw,hqueue⟩
    · left
      exact ⟨hraw,by rw [htrain]; exact hqueue⟩
    · exact Or.inr ⟨hraw,hqueue⟩
  exact ⟨⟨idleA,idleB,hrawA,hAfinal,hrawBother,hqueueBoundary⟩⟩

/-- No old-cell firing precedes the birth at 480, including compatible events
at that boundary. This is derived from the two actual empty output lists. -/
theorem CIntroductionBoundary.no_emissions {θ route s u} {e : @Execution 2 θ route s u}
    (boundary : CIntroductionBoundary e) : e.ledger.emissions = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro event he
  have hnone : ∀ i : Fin 2, e.emissionTimes i = [] := by
    intro i
    fin_cases i
    · exact boundary.a_idle.emissions
    · exact boundary.b_idle.emissions
  have hm : event.2 ∈ e.emissionTimes event.1 := by
    apply List.mem_map.mpr
    exact ⟨event,by simp [List.mem_filter,he],rfl⟩
  rw [hnone event.1] at hm
  contradiction

end KernelR.Hybrid
