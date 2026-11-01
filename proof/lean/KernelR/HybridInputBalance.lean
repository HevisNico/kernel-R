import KernelR.HybridInputs
import Mathlib.Data.List.Sort

/-! Exact multiset token conservation and actual ordered source delivery times. -/
namespace KernelR.Hybrid
open Set MeasureTheory

/-- Exact token conservation retains multiplicities, including duplicated
source or routed tokens. The queue is a list but conservation is a multiset. -/
theorem Jump.token_balance {n route s u} (j : @Jump n route s u) :
    (u.pending : Multiset (Delivery n)) + (j.deliveries : Multiset (Delivery n)) =
      (s.pending : Multiset (Delivery n)) +
        (j.ledger.emissions.flatMap (fun event => route event.1 event.2) : Multiset (Delivery n)) := by
  cases j <;> simp_all [Jump.deliveries, Jump.ledger, Ledger.zero, setMain, setAux, setRaw,
    ← Multiset.coe_add, List.flatMap_cons, List.flatMap_nil]
  all_goals rw [← Multiset.cons_coe, ← Multiset.singleton_add]
  all_goals ac_rfl

theorem Move.token_balance {n θ route s u} (m : @Move n θ route s u) :
    (u.pending : Multiset (Delivery n)) + (m.deliveries : Multiset (Delivery n)) =
      (s.pending : Multiset (Delivery n)) +
        (m.ledger.emissions.flatMap (fun event => route event.1 event.2) : Multiset (Delivery n)) := by
  cases m with
  | flow f => simp [Move.deliveries, Move.ledger, Flow.ledger, f.queue_fixed]
  | jump j => exact j.token_balance

theorem Execution.token_balance {n θ route s u} (e : @Execution n θ route s u) :
    (u.pending : Multiset (Delivery n)) + (e.deliveries : Multiset (Delivery n)) =
      (s.pending : Multiset (Delivery n)) +
        (e.ledger.emissions.flatMap (fun event => route event.1 event.2) : Multiset (Delivery n)) := by
  induction e with
  | nil => simp [deliveries, ledger, Ledger.zero]
  | @cons s v u move rest ih =>
    have hm := move.token_balance
    simp only [deliveries, ledger, Ledger.add, List.flatMap_append, ← Multiset.coe_add]
    calc
      _ = (u.pending : Multiset (Delivery n)) + (rest.deliveries : Multiset (Delivery n)) +
          (move.deliveries : Multiset (Delivery n)) := by ac_rfl
      _ = ((v.pending : Multiset (Delivery n)) +
          (rest.ledger.emissions.flatMap (fun event => route event.1 event.2) : Multiset (Delivery n))) +
          (move.deliveries : Multiset (Delivery n)) := by rw [ih]
      _ = ((v.pending : Multiset (Delivery n)) + (move.deliveries : Multiset (Delivery n))) +
          (rest.ledger.emissions.flatMap (fun event => route event.1 event.2) : Multiset (Delivery n)) := by ac_rfl
      _ = _ := by rw [hm]; ac_rfl

theorem Execution.pending_empty_of_sources_due {n θ route s u} (e : @Execution n θ route s u)
    (T : ℝ) (hc : CompleteThrough e T)
    (hs : ∀ d ∈ s.pending, d.due ≤ T) (hr : ∀ i t, route i t = []) : u.pending = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d hd
  have hfuture := hc.2.2 d hd
  rcases e.pending_provenance d hd with h | ⟨event,hev,hroute⟩
  · exact not_lt_of_ge (hs d h) hfuture
  · simp only [hr, List.not_mem_nil] at hroute

theorem Execution.deliveries_perm_sources {n θ route s u} (e : @Execution n θ route s u)
    (T : ℝ) (hc : CompleteThrough e T)
    (hs : ∀ d ∈ s.pending, d.due ≤ T) (hr : ∀ i t, route i t = []) :
    e.deliveries.Perm s.pending := by
  have hp := e.pending_empty_of_sources_due T hc hs hr
  have hissued : e.ledger.emissions.flatMap (fun event => route event.1 event.2) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun event _ => hr event.1 event.2)
  have hb := e.token_balance
  simp only [hp,hissued,Multiset.coe_nil,zero_add,add_zero] at hb
  exact Quotient.exact hb

theorem Execution.deliveries_chronological {n θ route s u} (e : @Execution n θ route s u) :
    e.deliveries.Pairwise (fun d f => d.due ≤ f.due) := by
  induction e with
  | nil => simp [deliveries]
  | cons move rest ih =>
    apply List.pairwise_append.mpr
    refine ⟨?_,ih,?_⟩
    · cases move with
      | flow f => simp [Move.deliveries]
      | jump j => cases j <;> simp [Move.deliveries,Jump.deliveries]
    · intro d hd f hf
      rw [move.delivery_due d hd]
      exact move.time_monotone.trans (rest.delivery_time_bounds f hf).1

def Execution.arrivalTimes {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) (p : Port) : List ℝ :=
  (e.deliveries.filter (fun d => d.cell = i ∧ d.port = p)).map Delivery.due

theorem Execution.arrivalTimes_chronological {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) : (e.arrivalTimes i p).Pairwise (· ≤ ·) :=
  List.pairwise_map.mpr (e.deliveries_chronological.filter _)

theorem Execution.arrival_times_exact {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (T : ℝ) (hc : CompleteThrough e T)
    (hs : ∀ d ∈ s.pending, d.due ≤ T) (hr : ∀ i t, route i t = [])
    (horder : ((s.pending.filter (fun d => d.cell = i ∧ d.port = p)).map Delivery.due).Pairwise (· ≤ ·)) :
    e.arrivalTimes i p = (s.pending.filter (fun d => d.cell = i ∧ d.port = p)).map Delivery.due := by
  exact (e.deliveries_perm_sources T hc hs hr |>.filter _ |>.map _).eq_of_pairwise'
    (e.arrivalTimes_chronological i p) horder

end KernelR.Hybrid
