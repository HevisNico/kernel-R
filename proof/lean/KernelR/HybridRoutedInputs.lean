import KernelR.HybridCellSources
import KernelR.HybridEvents
/-! Actual routed input calendars from emitted tokens, retaining future sources. -/
namespace KernelR.Hybrid
open Set

/-- Tokens routed to one cell by the actual emission ledger. -/
noncomputable def Execution.issuedTo {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) : List (Delivery n) :=
  (e.ledger.emissions.flatMap (fun event => route event.1 event.2)).filter (fun d => d.cell = i)

/-- Strictly past routed inputs have all arrived in any execution reaching the
endpoint. Future external sources at the same receiving cell are retained. -/
theorem Execution.cell_deliveries_perm_issued {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hf : PendingFuture u)
    (hs : ∀ d ∈ s.pending, d.cell = i → u.time < d.due)
    (hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2,
      d.cell = i → d.due < u.time) : (e.cellDeliveries i).Perm (e.issuedTo i) := by
  classical
  have hp : (u.pending.filter (fun d => d.cell = i)).filter (fun d => d.due < u.time) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    have hm : d ∈ u.pending ∧ d.cell = i := by simpa only [List.mem_filter,decide_eq_true_eq] using hd
    simpa only [decide_eq_true_eq] using not_lt_of_ge (hf d hm.1)
  have hsource : (s.pending.filter (fun d => d.cell = i)).filter (fun d => d.due < u.time) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    have hm : d ∈ s.pending ∧ d.cell = i := by simpa only [List.mem_filter,decide_eq_true_eq] using hd
    simpa only [decide_eq_true_eq] using not_lt_of_ge (hs d hm.1 hm.2).le
  have hdel : (e.cellDeliveries i).filter (fun d => d.due < u.time) = e.cellDeliveries i := by
    apply List.filter_eq_self.mpr
    intro d hd
    have hm : d ∈ e.deliveries ∧ d.cell = i := by simpa only [cellDeliveries,List.mem_filter,decide_eq_true_eq] using hd
    rcases e.delivery_provenance d hm.1 with h | ⟨event,he,hroute⟩
    · exact False.elim (not_lt_of_ge (e.delivery_time_bounds d hm.1).2 (hs d h hm.2))
    · exact decide_eq_true (hr event he d hroute hm.2)
  have his : (e.issuedTo i).filter (fun d => d.due < u.time) = e.issuedTo i := by
    apply List.filter_eq_self.mpr
    intro d hd
    have hm : d ∈ e.ledger.emissions.flatMap (fun event => route event.1 event.2) ∧ d.cell = i := by
      simpa only [issuedTo,List.mem_filter,decide_eq_true_eq] using hd
    obtain ⟨event,he,hroute⟩ := List.mem_flatMap.mp hm.1
    exact decide_eq_true (hr event he d hroute hm.2)
  have hcell := congrArg (Multiset.filter (fun d : Delivery n => d.cell = i)) e.token_balance
  simp only [Multiset.filter_add,Multiset.filter_coe] at hcell
  have hbefore := congrArg (Multiset.filter (fun d : Delivery n => d.due < u.time)) hcell
  simp only [Multiset.filter_add,Multiset.filter_coe] at hbefore
  change ((u.pending.filter (fun d => d.cell = i)).filter (fun d => d.due < u.time) : Multiset (Delivery n)) +
      ((e.cellDeliveries i).filter (fun d => d.due < u.time) : Multiset (Delivery n)) =
    ((s.pending.filter (fun d => d.cell = i)).filter (fun d => d.due < u.time) : Multiset (Delivery n)) +
      ((e.issuedTo i).filter (fun d => d.due < u.time) : Multiset (Delivery n)) at hbefore
  rw [hp,hsource,hdel,his] at hbefore
  simp only [Multiset.coe_nil,zero_add] at hbefore
  exact Quotient.exact hbefore

/-- Ordered one-port wire tokens fix every actual receiving-cell delivery.
Other destinations, their source queues and their traffic remain unrestricted. -/
theorem Execution.cell_routed_exact {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (hf : PendingFuture u)
    (hs : ∀ d ∈ s.pending, d.cell = i → u.time < d.due)
    (hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2,
      d.cell = i → d.due < u.time)
    (hslot : ∀ d ∈ e.issuedTo i, d.port = p)
    (horder : (e.issuedTo i).Pairwise (fun d f => d.due ≤ f.due)) :
    e.cellDeliveries i = e.issuedTo i := by
  have hp := e.cell_deliveries_perm_issued i hf hs hr
  apply List.Perm.eq_of_pairwise (le := fun d f : Delivery n => d.due ≤ f.due)
    ?_ (e.deliveries_chronological.filter _) horder hp
  intro a b ha hb hab hba
  have hsa : a ∈ e.issuedTo i := hp.mem_iff.mp ha
  have hca : a.cell = i := by simpa only [issuedTo,List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp hsa).2
  have hcb : b.cell = i := by simpa only [issuedTo,List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp hb).2
  have hpa := hslot a hsa
  have hpb := hslot b hb
  have ht := le_antisymm hab hba
  cases a
  cases b
  simp_all

end KernelR.Hybrid
