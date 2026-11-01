import KernelR.HybridCellInputs
/-! Exact receiving-cell source calendars with routes and future tokens at other cells. -/
namespace KernelR.Hybrid
open Set

/-- No token due at this horizon remains at the receiving cell. Other cells'
future pending tokens and outgoing routes are retained. -/
theorem Execution.cell_pending_empty {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (T : ℝ) (hc : CompleteThrough e T)
    (hs : ∀ d ∈ s.pending, d.cell = i → d.due ≤ T)
    (hr : ∀ j t, t ∈ Icc s.time u.time → ∀ d ∈ route j t, d.cell ≠ i) :
    u.pending.filter (fun d => d.cell = i) = [] := by
  classical
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d hd
  have hm : d ∈ u.pending ∧ d.cell = i := by simpa only [List.mem_filter,decide_eq_true_eq] using hd
  have hfuture := hc.2.2 d hm.1
  rcases e.pending_provenance d hm.1 with h | ⟨event,he,hroute⟩
  · exact not_lt_of_ge (hs d h hm.2) hfuture
  · exact hr event.1 event.2 (e.emission_time_bounds event he) d hroute hm.2

/-- Exact token conservation at one cell does not require globally empty routing. -/
theorem Execution.cell_deliveries_perm_sources {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (T : ℝ) (hc : CompleteThrough e T)
    (hs : ∀ d ∈ s.pending, d.cell = i → d.due ≤ T)
    (hr : ∀ j t, t ∈ Icc s.time u.time → ∀ d ∈ route j t, d.cell ≠ i) :
    (e.cellDeliveries i).Perm (s.pending.filter (fun d => d.cell = i)) := by
  classical
  have hp := e.cell_pending_empty i T hc hs hr
  have his : (e.ledger.emissions.flatMap (fun event => route event.1 event.2)).filter
      (fun d => d.cell = i) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have hm : d ∈ e.ledger.emissions.flatMap (fun event => route event.1 event.2) ∧ d.cell = i := by
      simpa only [List.mem_filter,decide_eq_true_eq] using hd
    obtain ⟨event,he,hdroute⟩ := List.mem_flatMap.mp hm.1
    exact hr event.1 event.2 (e.emission_time_bounds event he) d hdroute hm.2
  have hf := congrArg (Multiset.filter (fun d : Delivery n => d.cell = i)) e.token_balance
  simp only [Multiset.filter_add,Multiset.filter_coe] at hf
  rw [hp,his] at hf
  simp only [Multiset.coe_nil,zero_add,add_zero] at hf
  exact Quotient.exact hf

theorem Execution.cell_sources_exact {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (T : ℝ) (hc : CompleteThrough e T)
    (hs : ∀ d ∈ s.pending, d.cell = i → d.due ≤ T)
    (hr : ∀ j t, t ∈ Icc s.time u.time → ∀ d ∈ route j t, d.cell ≠ i)
    (hslot : ∀ d ∈ s.pending, d.cell = i → d.port = p)
    (horder : (s.pending.filter (fun d => d.cell = i)).Pairwise (fun d f => d.due ≤ f.due)) :
    e.cellDeliveries i = s.pending.filter (fun d => d.cell = i) := by
  classical
  have hp := e.cell_deliveries_perm_sources i T hc hs hr
  apply List.Perm.eq_of_pairwise (le := fun d f : Delivery n => d.due ≤ f.due)
    ?_ (e.deliveries_chronological.filter _) horder hp
  intro a b ha hb hab hba
  have hsa : a ∈ s.pending ∧ a.cell = i := by
    simpa only [List.mem_filter,decide_eq_true_eq] using hp.mem_iff.mp ha
  have hsb : b ∈ s.pending ∧ b.cell = i := by
    simpa only [List.mem_filter,decide_eq_true_eq] using hb
  have hpa := hslot a hsa.1 hsa.2
  have hpb := hslot b hsb.1 hsb.2
  have ht := le_antisymm hab hba
  cases a
  cases b
  simp_all

end KernelR.Hybrid
