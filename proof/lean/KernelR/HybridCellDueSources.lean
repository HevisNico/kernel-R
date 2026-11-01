import KernelR.HybridCellSources
import KernelR.HybridEvents
/-! Strict source prefixes at one receiving cell, retaining all other traffic. -/
namespace KernelR.Hybrid

/-- Only routes from actual emissions matter for receiving-cell conservation. -/
theorem Execution.cell_due_routed_empty {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n)
    (hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ i) :
    (e.ledger.emissions.flatMap (fun event => route event.1 event.2)).filter
      (fun d => d.cell = i) = [] := by
  classical
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d hd
  have hm : d ∈ e.ledger.emissions.flatMap (fun event => route event.1 event.2) ∧ d.cell = i := by
    simpa only [List.mem_filter,decide_eq_true_eq] using hd
  obtain ⟨event,he,hroute⟩ := List.mem_flatMap.mp hm.1
  exact hr event he d hroute hm.2

/-- Strictly past source tokens at the receiving cell have all arrived. Later
sources and every other cell's traffic remain in the supplied execution. -/
theorem Execution.cell_deliveries_due_prefix {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (past later : List (Delivery n))
    (hq : (s.pending.filter (fun d => d.cell = i)).Perm (past ++ later))
    (hpast : ∀ d ∈ past, d.due < u.time) (hlater : ∀ d ∈ later, u.time < d.due)
    (hf : PendingFuture u)
    (hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ i) :
    (e.cellDeliveries i).Perm past := by
  classical
  have his := e.cell_due_routed_empty i hr
  have hb := congrArg (Multiset.filter (fun d : Delivery n => d.cell = i)) e.token_balance
  simp only [Multiset.filter_add,Multiset.filter_coe,his,Multiset.coe_nil,add_zero] at hb
  have hfilt := congrArg (Multiset.filter (fun d : Delivery n => d.due < u.time)) hb
  simp only [Multiset.filter_add,Multiset.filter_coe] at hfilt
  have hp : (u.pending.filter (fun d => d.cell = i)).filter (fun d => d.due < u.time) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    obtain ⟨hd,hlt⟩ := List.mem_filter.mp hd
    obtain ⟨hd,_⟩ := List.mem_filter.mp hd
    exact not_lt_of_ge (hf d hd) (of_decide_eq_true hlt)
  have h₁ : past.filter (fun d => d.due < u.time) = past := by
    apply List.filter_eq_self.mpr
    intro d hd
    exact decide_eq_true (hpast d hd)
  have h₂ : later.filter (fun d => d.due < u.time) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    simpa only [decide_eq_true_eq] using not_lt_of_ge (hlater d hd).le
  have hsources : ((s.pending.filter (fun d => d.cell = i)).filter
      (fun d => d.due < u.time)).Perm past := by
    simpa only [List.filter_append,h₁,h₂,List.append_nil] using hq.filter (fun d => d.due < u.time)
  have he : (e.cellDeliveries i).filter (fun d => d.due < u.time) = e.cellDeliveries i := by
    apply List.filter_eq_self.mpr
    intro d hd
    have hm : d ∈ e.deliveries ∧ d.cell = i := by
      simpa only [Execution.cellDeliveries,List.mem_filter,decide_eq_true_eq] using hd
    rcases e.delivery_provenance d hm.1 with hs | ⟨event,he,hroute⟩
    · have hs' : d ∈ s.pending.filter (fun d => d.cell = i) := by
        simpa only [List.mem_filter,decide_eq_true_eq] using And.intro hs hm.2
      have hs'' := hq.mem_iff.mp hs'
      rcases List.mem_append.mp hs'' with h | h
      · exact decide_eq_true (hpast d h)
      · exact False.elim (not_lt_of_ge (e.delivery_time_bounds d hm.1).2 (hlater d h))
    · exact False.elim (hr event he d hroute hm.2)
  change ((u.pending.filter (fun d => d.cell = i)).filter (fun d => d.due < u.time) : Multiset (Delivery n)) +
    ((e.cellDeliveries i).filter (fun d => d.due < u.time) : Multiset (Delivery n)) = _ at hfilt
  rw [hp,he] at hfilt
  simp only [Multiset.coe_nil,zero_add] at hfilt
  exact (Quotient.exact hfilt).trans hsources

/-- At one receiving slot, the strict source prefix also has its exact order. -/
theorem Execution.cell_deliveries_due_prefix_exact {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (past later : List (Delivery n))
    (hq : (s.pending.filter (fun d => d.cell = i)).Perm (past ++ later))
    (hpast : ∀ d ∈ past, d.due < u.time) (hlater : ∀ d ∈ later, u.time < d.due)
    (hf : PendingFuture u)
    (hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ i)
    (hslot : ∀ d ∈ past, d.cell = i ∧ d.port = p)
    (horder : past.Pairwise (fun d f => d.due ≤ f.due)) : e.cellDeliveries i = past := by
  have hp := e.cell_deliveries_due_prefix i past later hq hpast hlater hf hr
  apply List.Perm.eq_of_pairwise (le := fun d f : Delivery n => d.due ≤ f.due)
    ?_ (e.deliveries_chronological.filter _) horder hp
  intro a b ha hb hab hba
  have hsa := hslot a (hp.mem_iff.mp ha)
  have hsb := hslot b hb
  have ht := le_antisymm hab hba
  cases a
  cases b
  simp_all

/-- Conservation retains all later receiving-cell sources with multiplicity.
No conclusion is made about the queue at any other cell. -/
theorem Execution.cell_pending_perm_of_prefix {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (past later : List (Delivery n))
    (hq : (s.pending.filter (fun d => d.cell = i)).Perm (past ++ later))
    (hd : (e.cellDeliveries i).Perm past)
    (hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ i) :
    (u.pending.filter (fun d => d.cell = i)).Perm later := by
  classical
  have his := e.cell_due_routed_empty i hr
  have hb := congrArg (Multiset.filter (fun d : Delivery n => d.cell = i)) e.token_balance
  simp only [Multiset.filter_add,Multiset.filter_coe,his,Multiset.coe_nil,add_zero] at hb
  have hsource : (s.pending.filter (fun d => d.cell = i) : Multiset (Delivery n)) =
      (past : Multiset (Delivery n)) + (later : Multiset (Delivery n)) := by
    calc
      _ = ((past ++ later : List (Delivery n)) : Multiset (Delivery n)) := Quot.sound hq
      _ = _ := (Multiset.coe_add past later).symm
  have hdel : (e.cellDeliveries i : Multiset (Delivery n)) = (past : Multiset (Delivery n)) := Quot.sound hd
  change (u.pending.filter (fun d => d.cell = i) : Multiset (Delivery n)) +
    (e.cellDeliveries i : Multiset (Delivery n)) = _ at hb
  rw [hsource,hdel] at hb
  have h : (u.pending.filter (fun d => d.cell = i) : Multiset (Delivery n)) =
      (later : Multiset (Delivery n)) := by
    apply add_right_cancel (b := (past : Multiset (Delivery n)))
    calc
      _ = (past : Multiset (Delivery n)) + (later : Multiset (Delivery n)) := hb
      _ = _ := add_comm _ _
  exact Quotient.exact h

end KernelR.Hybrid
