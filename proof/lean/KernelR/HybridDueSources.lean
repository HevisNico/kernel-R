import KernelR.HybridArrivals
import KernelR.HybridEvents
/-! Actual source prefixes without deleting future pending tokens. -/
namespace KernelR.Hybrid
open Set

/-- Every source strictly before the terminal date has been consumed. A token
at that date may still be pending, so the cutoff is deliberately strict. -/
theorem Execution.deliveries_before_perm_sources {n θ route s u} (e : @Execution n θ route s u)
    (hf : PendingFuture u) (hr : ∀ i t, route i t = []) :
    (e.deliveries.filter (fun d => d.due < u.time)).Perm
      (s.pending.filter (fun d => d.due < u.time)) := by
  classical
  have hp : u.pending.filter (fun d => d.due < u.time) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have hm : d ∈ u.pending ∧ d.due < u.time := by
      simpa only [List.mem_filter,decide_eq_true_eq] using hd
    exact not_lt_of_ge (hf d hm.1) hm.2
  have his : e.ledger.emissions.flatMap (fun event => route event.1 event.2) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun event _ => hr event.1 event.2)
  have hb := congrArg (Multiset.filter (fun d : Delivery n => d.due < u.time)) e.token_balance
  simp only [Multiset.filter_add,Multiset.filter_coe,hp,his,
    Multiset.coe_nil,zero_add,add_zero] at hb
  exact Quotient.exact hb

/-- A source queue may retain arbitrary later inputs. No completeness condition
or prescribed pulse cases are needed to identify the strictly past prefix. -/
theorem Execution.deliveries_due_prefix {n θ route s u} (e : @Execution n θ route s u)
    (past later : List (Delivery n)) (hq : s.pending = past ++ later)
    (hpast : ∀ d ∈ past, d.due < u.time) (hlater : ∀ d ∈ later, u.time < d.due)
    (hf : PendingFuture u) (hr : ∀ i t, route i t = []) : e.deliveries.Perm past := by
  classical
  have hp : s.pending.filter (fun d => d.due < u.time) = past := by
    rw [hq,List.filter_append]
    have h₁ : past.filter (fun d => d.due < u.time) = past := by
      apply List.filter_eq_self.mpr
      intro d hd
      exact decide_eq_true (hpast d hd)
    have h₂ : later.filter (fun d => d.due < u.time) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro d hd
      simpa only [decide_eq_true_eq] using not_lt_of_ge (hlater d hd).le
    rw [h₁,h₂,List.append_nil]
  have he : e.deliveries.filter (fun d => d.due < u.time) = e.deliveries := by
    apply List.filter_eq_self.mpr
    intro d hd
    rcases e.delivery_provenance d hd with hs | ⟨event,he,hroute⟩
    · rw [hq] at hs
      rcases List.mem_append.mp hs with h | h
      · exact decide_eq_true (hpast d h)
      · exact False.elim (not_lt_of_ge (e.delivery_time_bounds d hd).2 (hlater d h))
    · simp only [hr,List.not_mem_nil] at hroute
  simpa only [hp,he] using e.deliveries_before_perm_sources hf hr

/-- After consuming an exact source prefix, conservation retains every later
pending token, including multiplicities. Queue order is not inferred here. -/
theorem Execution.pending_perm_of_prefix {n θ route s u} (e : @Execution n θ route s u)
    (past later : List (Delivery n)) (hq : s.pending = past ++ later)
    (hd : e.deliveries.Perm past) (hr : ∀ i t, route i t = []) : u.pending.Perm later := by
  have his : e.ledger.emissions.flatMap (fun event => route event.1 event.2) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun event _ => hr event.1 event.2)
  have hdel : (e.deliveries : Multiset (Delivery n)) = (past : Multiset (Delivery n)) :=
    Quot.sound hd
  have hb := e.token_balance
  rw [hq,hdel,his] at hb
  simp only [← Multiset.coe_add,Multiset.coe_nil,add_zero] at hb
  have h : (u.pending : Multiset (Delivery n)) = (later : Multiset (Delivery n)) := by
    apply add_right_cancel (b := (past : Multiset (Delivery n)))
    calc
      _ = (past : Multiset (Delivery n)) + (later : Multiset (Delivery n)) := hb
      _ = _ := add_comm _ _
  exact Quotient.exact h

/-- Chronology fixes the prefix order when its tokens share a receiving slot. -/
theorem Execution.deliveries_due_prefix_exact {n θ route s u} (e : @Execution n θ route s u)
    (past later : List (Delivery n)) (hq : s.pending = past ++ later)
    (hpast : ∀ d ∈ past, d.due < u.time) (hlater : ∀ d ∈ later, u.time < d.due)
    (hf : PendingFuture u) (hr : ∀ i t, route i t = [])
    (i : Fin n) (p : Port) (hslot : ∀ d ∈ past, d.cell = i ∧ d.port = p)
    (horder : past.Pairwise (fun d f => d.due ≤ f.due)) : e.deliveries = past := by
  have hp := e.deliveries_due_prefix past later hq hpast hlater hf hr
  apply List.Perm.eq_of_pairwise (le := fun d f : Delivery n => d.due ≤ f.due)
    ?_ e.deliveries_chronological horder hp
  intro a b ha hb hab hba
  have hsa := hslot a (hp.mem_iff.mp ha)
  have hsb := hslot b hb
  have ht := le_antisymm hab hba
  cases a
  cases b
  simp_all

end KernelR.Hybrid
