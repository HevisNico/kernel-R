import KernelR.HybridStagedTeaching
/-! Actual queue closure at the end of A-to-B teaching, retaining B's future sources. -/
namespace KernelR.Hybrid

/-- Newborn sources are exactly the pending queue projected to the new cell.
Old tokens retain their cast indices and cannot enter that projection. -/
theorem BirthStep.new_cell_pending {n s u} (birth : @BirthStep n s u) :
    u.pending.filter (fun d => d.cell = Fin.last n) = birth.sources := by
  classical
  have hold : (s.pending.map liftDelivery).filter (fun d => d.cell = Fin.last n) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hd
    exact fun h => (ne_of_lt old.cell.castSucc_lt_last) (of_decide_eq_true h)
  have hnew : birth.sources.filter (fun d => d.cell = Fin.last n) = birth.sources := by
    apply List.filter_eq_self.mpr
    intro d hd
    exact decide_eq_true (birth.source_cell d hd)
  rw [birth.pending,List.filter_append,hold,hnew,List.nil_append]

/-- A future terminal queue cannot retain a token whose source or actual
routing provenance is strictly before the endpoint. -/
theorem Execution.cell_pending_empty_strict {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hf : PendingFuture u)
    (hs : ∀ d ∈ s.pending, d.cell = i → d.due < u.time)
    (hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2,
      d.cell = i → d.due < u.time) : u.pending.filter (fun d => d.cell = i) = [] := by
  classical
  apply List.filter_eq_nil_iff.mpr
  intro d hd
  simp only [decide_eq_true_eq]
  intro hc
  have hfuture := hf d hd
  rcases e.pending_provenance d hd with h | ⟨event,he,hroute⟩
  · exact not_lt_of_ge hfuture (hs d h hc)
  · exact not_lt_of_ge hfuture (hr event he d hroute hc)

/-- Once all routed tokens to a cell have arrived, its remaining source
multiset is exactly the one it had initially. Other cells are not projected out
of the physical execution. -/
theorem Execution.cell_pending_perm_of_routed_balance {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hd : (e.cellDeliveries i).Perm (e.issuedTo i)) :
    (u.pending.filter (fun d => d.cell = i)).Perm (s.pending.filter (fun d => d.cell = i)) := by
  classical
  have hb := congrArg (Multiset.filter (fun d : Delivery n => d.cell = i)) e.token_balance
  simp only [Multiset.filter_add,Multiset.filter_coe] at hb
  have hdel : (e.cellDeliveries i : Multiset (Delivery n)) = (e.issuedTo i : Multiset (Delivery n)) :=
    Quot.sound hd
  change (u.pending.filter (fun d => d.cell = i) : Multiset (Delivery n)) +
      (e.cellDeliveries i : Multiset (Delivery n)) =
    (s.pending.filter (fun d => d.cell = i) : Multiset (Delivery n)) +
      (e.issuedTo i : Multiset (Delivery n)) at hb
  rw [hdel] at hb
  have h : (u.pending.filter (fun d => d.cell = i) : Multiset (Delivery n)) =
      (s.pending.filter (fun d => d.cell = i) : Multiset (Delivery n)) := add_right_cancel hb
  exact Quotient.exact h

structure TeachingQueueClosure {θ fresh routeBefore routeAfter born u}
    (e : @StagedExecution 1 θ fresh routeBefore routeAfter born u) : Prop where
  a_empty : u.pending.filter (fun d => d.cell = 0) = []
  b_sources : (u.pending.filter (fun d => d.cell = 1)).Perm e.birth.sources

/-- The source queues needed for the feedback epoch follow from the actual
teaching execution. No received calendar, physical case word or count is
supplied. The statement only uses queue/clock facts, so it needs no additional
fabrication or mode premises. -/
theorem StagedExecution.teaching_queue_closure {θ fresh routeBefore born u}
    (forward backward : ℝ → ℝ)
    (e : @StagedExecution 1 θ fresh routeBefore (reciprocalEntryRouter forward backward) born u)
    (hborn : BirthState born)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (hbefore : ∀ i t, routeBefore i t = [])
    (hend : u.time = 3199 / 10)
    (hsources : ∀ d ∈ e.birth.sources, 320 ≤ d.due)
    (hforward : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hbackward : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) :
    TeachingQueueClosure e := by
  have hcausal := reciprocalEntryRouter.causal forward backward
    (fun t => by linarith [(hforward t).1]) (fun t => by linarith [(hbackward t).1])
  have hbeforeCausal : CausalRouter routeBefore := by simp [CausalRouter,hbefore]
  have hinitial : PendingFuture born := by
    intro d hd
    rw [hqueue] at hd
    rw [hborn.1]
    rcases List.mem_append.mp hd with hd | hd
    all_goals obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd; dsimp; positivity
  have hpf : PendingFuture u := e.pending_future hbeforeCausal hcausal hinitial
  have htime : ∀ event ∈ e.after.ledger.emissions, event.2 < 320 := by
    intro event he
    have h := (e.after.emission_time_bounds event he).2
    rw [hend] at h
    linarith
  have hclosed : ∀ event ∈ e.after.ledger.emissions,
      ∀ d ∈ reciprocalEntryRouter forward backward event.1 event.2, d.cell ≠ 0 := by
    intro event he
    exact reciprocalEntryRouter.closed_to_a forward backward event.1 (htime event he)
  have hsourceA : ∀ d ∈ e.afterBirth.pending, d.cell = 0 → d.due < u.time := by
    intro d hd hc
    rw [e.birth.pending] at hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hd
      have hsource : old ∈ born.pending := by
        rcases e.before.pending_provenance old hold with h | ⟨event,he,hroute⟩
        · exact h
        · simp only [hbefore,List.not_mem_nil] at hroute
      rw [hqueue] at hsource
      rw [hend]
      rcases List.mem_append.mp hsource with hs | hs
      all_goals
        obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hs
        have hk : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
        dsimp [liftDelivery]
        linarith
    · have hnew := e.birth.source_cell d hd
      have hne : (0 : Fin 2) ≠ Fin.last 1 := by decide
      exact False.elim (hne (hc.symm.trans hnew))
  have hemptyA : u.pending.filter (fun d => d.cell = 0) = [] :=
    e.after.cell_pending_empty_strict 0 hpf hsourceA
      (fun event he d hd hc => False.elim (hclosed event he d hd hc))
  have hnew : e.afterBirth.pending.filter (fun d => d.cell = 1) = e.birth.sources :=
    e.birth.new_cell_pending
  have hsourceB : ∀ d ∈ e.afterBirth.pending, d.cell = 1 → u.time < d.due := by
    intro d hd hc
    have hm : d ∈ e.afterBirth.pending.filter (fun d => d.cell = 1) := by
      simp only [List.mem_filter,decide_eq_true_eq]
      exact ⟨hd,hc⟩
    rw [hnew] at hm
    rw [hend]
    linarith [hsources d hm]
  have hroutedB : ∀ event ∈ e.after.ledger.emissions,
      ∀ d ∈ reciprocalEntryRouter forward backward event.1 event.2, d.cell = 1 → d.due < u.time := by
    intro event he d hd _
    rw [reciprocalEntryRouter.before_reverse forward backward event.1 (htime event he)] at hd
    unfold Contact.route at hd
    split_ifs at hd with h
    · simp only [List.mem_singleton] at hd
      subst d
      have hg : event.2 < 310 := h.2.2
      change event.2 + forward event.2 < u.time
      rw [hend]
      linarith [(hforward event.2).2]
    · contradiction
  have hdel := e.after.cell_deliveries_perm_issued 1 hpf hsourceB hroutedB
  have hremain := e.after.cell_pending_perm_of_routed_balance 1 hdel
  rw [hnew] at hremain
  exact ⟨hemptyA,hremain⟩

end KernelR.Hybrid
