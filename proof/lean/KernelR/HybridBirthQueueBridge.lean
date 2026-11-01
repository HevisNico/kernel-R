import KernelR.HybridBirthPreparation
/-! Queue/raw coupling at a terminal source date, without event priority. -/
namespace KernelR.Hybrid

/-- Empty routing makes the pending and delivered tokens an exact partition
of any permutation presentation of the initial queue. -/
theorem Execution.queue_delivery_partition {n θ route s u} (e : @Execution n θ route s u)
    (queue : List (Delivery n)) (hq : s.pending.Perm queue) (hr : ∀ i t, route i t = []) :
    (u.pending ++ e.deliveries).Perm queue := by
  have his : e.ledger.emissions.flatMap (fun event => route event.1 event.2) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun event _ => hr event.1 event.2)
  have hs : (s.pending : Multiset (Delivery n)) = (queue : Multiset (Delivery n)) := Quot.sound hq
  have hb := e.token_balance
  rw [his,hs] at hb
  simp only [Multiset.coe_nil,add_zero] at hb
  exact Quotient.exact hb

/-- If the only source that can be delivered is due exactly now, it is either
still queued with no raw current, or has been consumed and is fresh. -/
theorem Execution.terminal_source_queue {n θ route s u} (e : @Execution n θ route s u)
    (d : Delivery n) (later : List (Delivery n))
    (hq : s.pending.Perm (d :: later)) (hdate : d.due = u.time)
    (hlater : ∀ f ∈ later, u.time < f.due)
    (hraw : s.raw d.cell d.port = none) (hr : ∀ i t, route i t = []) :
    (u.raw d.cell d.port = none ∧ u.pending.Perm (d :: later)) ∨
      (u.raw d.cell d.port = some u.time ∧ u.pending.Perm later) := by
  classical
  have hb := e.queue_delivery_partition (d :: later) hq hr
  have hnot : d ∉ later := by
    intro hd
    have ht := hlater d hd
    rw [hdate] at ht
    exact lt_irrefl _ ht
  have honly : ∀ f ∈ e.deliveries, f = d := by
    intro f hf
    rcases e.delivery_provenance f hf with hs | ⟨event,he,hroute⟩
    · have hm := hq.mem_iff.mp hs
      rcases List.mem_cons.mp hm with h | h
      · exact h
      · exact False.elim (not_lt_of_ge (e.delivery_time_bounds f hf).2 (hlater f h))
    · simp only [hr,List.not_mem_nil] at hroute
  have hdeliveries : e.deliveries = [] ∨ e.deliveries = [d] := by
    cases he : e.deliveries with
    | nil => exact Or.inl rfl
    | cons first rest =>
      have hfirst : first = d := honly first (by rw [he]; simp)
      subst first
      cases rest with
      | nil => exact Or.inr rfl
      | cons second tail =>
        have hsecond : second = d := honly second (by rw [he]; simp)
        subst second
        have hc := hb.count_eq d
        simp only [he,List.count_append,List.count_cons_self,List.count_eq_zero_of_not_mem hnot] at hc
        omega
  rcases hdeliveries with he | he
  · left
    refine ⟨(e.raw_absent_of_no_arrival d.cell d.port hraw ?_).1,?_⟩
    · simp [NoArrivalAt,he]
    · simpa only [he,List.append_nil] using hb
  · right
    obtain ⟨cut⟩ := e.first_delivery d [] he
    have hafter : cut.afterArrival.time = u.time := cut.date.2.trans hdate
    have hcurrent := cut.rest.raw_persists d.cell d.port cut.afterArrival.time cut.raw_after (by rw [hafter]; linarith)
    refine ⟨by simpa only [hafter] using hcurrent,?_⟩
    have hqcast : (u.pending : Multiset (Delivery n)) + ({d} : Multiset (Delivery n)) =
        (later : Multiset (Delivery n)) + ({d} : Multiset (Delivery n)) := by
      have h : ((u.pending ++ [d] : List (Delivery n)) : Multiset (Delivery n)) =
          ((d :: later : List (Delivery n)) : Multiset (Delivery n)) :=
        Multiset.coe_eq_coe.mpr (by simpa only [he] using hb)
      rw [← Multiset.coe_add,Multiset.coe_singleton,← Multiset.cons_coe,← Multiset.singleton_add] at h
      simpa only [add_comm] using h
    have hcancel : (u.pending : Multiset (Delivery n)) = (later : Multiset (Delivery n)) :=
      add_right_cancel hqcast
    exact Quotient.exact hcancel

/-- The complete two-train birth queue has exactly two legal boundary states
at 160. The queue alternative is coupled to whether source 160 is fresh. -/
theorem Execution.birth_queue_at_second_train {n θ ε route born u} (e : @Execution n θ route born u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hp : p ≠ 1)
    (ha : ∀ q, born.aux i q = .ready)
    (hq : born.pending = sourceTrain i p 0 8 16 ++ sourceTrain i p 160 8 16)
    (hr : ∀ i t, route i t = []) (ht : u.time = 160) :
    (u.raw i p = none ∧ u.pending.Perm (sourceTrain i p 160 8 16)) ∨
      (u.raw i p = some u.time ∧ u.pending.Perm (sourceTrain i p 168 8 15)) := by
  obtain ⟨prep⟩ := e.birth_low_two_trains_prefix hborn hb i p hp ha hq hr (by rw [ht]; norm_num)
  have hpending := prep.span.pending_perm_of_prefix _ _ hq (by rw [prep.calendar]) hr
  have htrain : sourceTrain i p 160 8 16 = ⟨i,p,160⟩ :: sourceTrain i p 168 8 15 := by
    simpa only [show (160 : ℝ) + 8 = 168 by norm_num] using sourceTrain_succ i p 160 8 15
  have hq' : prep.state.pending.Perm (⟨i,p,160⟩ :: sourceTrain i p 168 8 15) := by
    rw [← htrain]
    exact hpending
  have hlater : ∀ d ∈ sourceTrain i p 168 8 15, u.time < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    rw [ht]
    change (160 : ℝ) < 168 + 8 * k.val
    linarith
  have h := prep.continuation.tail.terminal_source_queue ⟨i,p,160⟩ (sourceTrain i p 168 8 15)
    hq' ht.symm hlater (prep.train.raw_finished p) hr
  simpa only [← htrain] using h

/-- At each old cell, birth retains exactly its pending tokens and changes only
its index type. Newborn source tokens cannot enter that old-cell projection. -/
theorem BirthStep.old_cell_pending {n s u} (birth : @BirthStep n s u) (i : Fin n) :
    u.pending.filter (fun d => d.cell = i.castSucc) =
      (s.pending.filter (fun d => d.cell = i)).map liftDelivery := by
  classical
  have hnew : birth.sources.filter (fun d => d.cell = i.castSucc) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    simp only [decide_eq_true_eq]
    intro hi
    have hcell := birth.source_cell d hd
    exact (ne_of_lt i.castSucc_lt_last) (hi.symm.trans hcell)
  rw [birth.pending,List.filter_append,hnew,List.append_nil]
  simp only [List.filter_map,Function.comp_def,liftDelivery,Fin.castSucc_inj]

/-- A one-cell source train remains the exact old-cell pending multiset after
birth, even when the newborn has an independent source queue. -/
theorem BirthStep.old_cell_source_train_perm {n s u} (birth : @BirthStep n s u)
    (i : Fin n) (p : Port) (start gap : ℝ) (count : ℕ)
    (hq : s.pending.Perm (sourceTrain i p start gap count)) :
    (u.pending.filter (fun d => d.cell = i.castSucc)).Perm (sourceTrain i.castSucc p start gap count) := by
  classical
  have hfilter : s.pending.filter (fun d => d.cell = i) = s.pending := by
    apply List.filter_eq_self.mpr
    intro d hd
    have hm := hq.mem_iff.mp hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hm
    exact decide_eq_true rfl
  rw [birth.old_cell_pending i,hfilter]
  have h := hq.map liftDelivery
  simpa only [sourceTrain,List.map_ofFn,Function.comp_def,liftDelivery] using h

/-- Both legal queue/raw alternatives at 160 survive the actual birth event. -/
theorem StagedExecution.source_queue_at_birth {n θ fresh ε routeBefore routeAfter born u}
    (e : @StagedExecution n θ fresh routeBefore routeAfter born u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hp : p ≠ 1)
    (ha : ∀ q, born.aux i q = .ready)
    (hq : born.pending = sourceTrain i p 0 8 16 ++ sourceTrain i p 160 8 16)
    (hr : ∀ i t, routeBefore i t = []) (ht : e.beforeBirth.time = 160) :
    (e.afterBirth.raw i.castSucc p = none ∧
      (e.afterBirth.pending.filter (fun d => d.cell = i.castSucc)).Perm (sourceTrain i.castSucc p 160 8 16)) ∨
    (e.afterBirth.raw i.castSucc p = some e.afterBirth.time ∧
      (e.afterBirth.pending.filter (fun d => d.cell = i.castSucc)).Perm (sourceTrain i.castSucc p 168 8 15)) := by
  rcases e.before.birth_queue_at_second_train hborn hb i p hp ha hq hr ht with ⟨hraw,hpending⟩ | ⟨hraw,hpending⟩
  · left
    refine ⟨?_,e.birth.old_cell_source_train_perm i p 160 8 16 hpending⟩
    rw [e.birth.old_raw]
    exact hraw
  · right
    refine ⟨?_,e.birth.old_cell_source_train_perm i p 168 8 15 hpending⟩
    rw [e.birth.old_raw,e.birth.time_unchanged]
    exact hraw

end KernelR.Hybrid
