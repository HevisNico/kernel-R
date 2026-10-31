import KernelR.HybridPrefix
import KernelR.HybridEvents

/-! Provenance of actual queued and delivered tokens. Input isolation is derived
from the initial queue and routes of actual emissions, not a supplied case word. -/
namespace KernelR.Hybrid

def Jump.deliveries {n route s u} (j : @Jump n route s u) : List (Delivery n) :=
  match j with | .arrive _ d _ _ _ _ _ => [d] | _ => []

def Move.deliveries {n θ route s u} : @Move n θ route s u → List (Delivery n)
  | .flow _ => []
  | .jump j => j.deliveries

def Execution.deliveries {n θ route s u} : @Execution n θ route s u → List (Delivery n)
  | .nil _ => []
  | .cons step rest => step.deliveries ++ rest.deliveries

theorem Jump.pending_provenance {n route s u} (j : @Jump n route s u) (d : Delivery n)
    (hd : d ∈ u.pending) :
    d ∈ s.pending ∨ ∃ event ∈ j.ledger.emissions, d ∈ route event.1 event.2 := by
  cases j <;> simp_all [Jump.ledger, Ledger.zero, setMain, setAux, setRaw]
  all_goals tauto

theorem Move.pending_provenance {n θ route s u} (m : @Move n θ route s u) (d : Delivery n)
    (hd : d ∈ u.pending) :
    d ∈ s.pending ∨ ∃ event ∈ m.ledger.emissions, d ∈ route event.1 event.2 := by
  cases m with
  | flow f => exact Or.inl (by simpa only [f.queue_fixed] using hd)
  | jump j => exact j.pending_provenance d hd

theorem Execution.pending_provenance {n θ route s u} (e : @Execution n θ route s u) (d : Delivery n)
    (hd : d ∈ u.pending) :
    d ∈ s.pending ∨ ∃ event ∈ e.ledger.emissions, d ∈ route event.1 event.2 := by
  induction e with
  | nil => exact Or.inl hd
  | cons step rest ih =>
    rcases ih hd with hmid | ⟨event, hev, hr⟩
    · rcases step.pending_provenance d hmid with hs | ⟨event, hev, hr⟩
      · exact Or.inl hs
      · exact Or.inr ⟨event, List.mem_append_left _ hev, hr⟩
    · exact Or.inr ⟨event, List.mem_append_right _ hev, hr⟩

theorem Jump.delivery_from_queue {n route s u} (j : @Jump n route s u) (d : Delivery n)
    (hd : d ∈ j.deliveries) : d ∈ s.pending := by
  cases j <;> simp_all [deliveries]

theorem Move.delivery_from_queue {n θ route s u} (m : @Move n θ route s u) (d : Delivery n)
    (hd : d ∈ m.deliveries) : d ∈ s.pending := by
  cases m with
  | flow f => simp [deliveries] at hd
  | jump j => exact j.delivery_from_queue d hd

theorem Execution.delivery_provenance {n θ route s u} (e : @Execution n θ route s u) (d : Delivery n)
    (hd : d ∈ e.deliveries) :
    d ∈ s.pending ∨ ∃ event ∈ e.ledger.emissions, d ∈ route event.1 event.2 := by
  induction e with
  | nil => simp [deliveries] at hd
  | cons step rest ih =>
    rcases List.mem_append.mp hd with hfirst | hrest
    · exact Or.inl (step.delivery_from_queue d hfirst)
    · rcases ih hrest with hmid | ⟨event, hev, hr⟩
      · rcases step.pending_provenance d hmid with hs | ⟨event, hev, hr⟩
        · exact Or.inl hs
        · exact Or.inr ⟨event, List.mem_append_left _ hev, hr⟩
      · exact Or.inr ⟨event, List.mem_append_right _ hev, hr⟩

theorem Execution.deliveries_allowed {n θ route s u} (e : @Execution n θ route s u)
    (allowed : Delivery n → Prop) (hs : ∀ d ∈ s.pending, allowed d)
    (hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, allowed d) :
    ∀ d ∈ e.deliveries, allowed d := by
  intro d hd
  rcases e.delivery_provenance d hd with h | ⟨event, hev, hd⟩
  · exact hs d h
  · exact hr event hev d hd

def NoArrivalAt {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) (p : Port) : Prop :=
  ∀ d ∈ e.deliveries, d.cell ≠ i ∨ d.port ≠ p

theorem Jump.raw_none_of_no_arrival {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port)
    (hr : s.raw i p = none) (hno : ∀ d ∈ j.deliveries, d.cell ≠ i ∨ d.port ≠ p) :
    u.raw i p = none := by
  cases j <;> simp_all [Jump.deliveries, setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]
  all_goals aesop

def Execution.RawAbsent {n θ route s u} (i : Fin n) (p : Port) : @Execution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow _) rest => s.raw i p = none ∧ rest.RawAbsent i p
  | .cons (.jump _) rest => rest.RawAbsent i p

theorem Execution.raw_absent_of_no_arrival {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (hr : s.raw i p = none) (hno : NoArrivalAt e i p) :
    u.raw i p = none ∧ e.RawAbsent i p := by
  induction e with
  | nil => exact ⟨hr, trivial⟩
  | cons step rest ih =>
    have hrest : NoArrivalAt rest i p := fun d hd => hno d (List.mem_append_right _ hd)
    cases step with
    | flow f =>
      have h := ih (by simpa only [f.raw_fixed] using hr) hrest
      exact ⟨h.1, hr, h.2⟩
    | jump j =>
      exact ih (j.raw_none_of_no_arrival i p hr (fun d hd => hno d (List.mem_append_left _ hd))) hrest

theorem Jump.delivery_due {n route s u} (j : @Jump n route s u) (d : Delivery n)
    (hd : d ∈ j.deliveries) : d.due = s.time := by
  cases j <;> simp_all [deliveries]

theorem Move.delivery_due {n θ route s u} (m : @Move n θ route s u) (d : Delivery n)
    (hd : d ∈ m.deliveries) : d.due = s.time := by
  cases m with
  | flow f => simp [deliveries] at hd
  | jump j => exact j.delivery_due d hd

theorem Execution.delivery_time_bounds {n θ route s u} (e : @Execution n θ route s u)
    (d : Delivery n) (hd : d ∈ e.deliveries) : s.time ≤ d.due ∧ d.due ≤ u.time := by
  induction e with
  | nil => simp [deliveries] at hd
  | cons step rest ih =>
    rcases List.mem_append.mp hd with hfirst | hrest
    · rw [step.delivery_due d hfirst]
      exact ⟨le_rfl, step.time_monotone.trans rest.time_monotone⟩
    · exact ⟨step.time_monotone.trans (ih hrest).1, (ih hrest).2⟩

/-- Source and routing dates exclude every new arrival at this cell inside the
window. Queued tokens beyond the window remain explicit. -/
theorem Execution.no_arrival_before_due {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : ∀ d ∈ s.pending, d.cell = i → u.time < d.due)
    (hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2,
      d.cell = i → u.time < d.due) : ∀ p, NoArrivalAt e i p := by
  intro p d hd
  left
  intro hcell
  have htime := (e.delivery_time_bounds d hd).2
  rcases e.delivery_provenance d hd with h | ⟨event, hev, hroute⟩
  · exact (not_lt_of_ge htime) (hs d h hcell)
  · exact (not_lt_of_ge htime) (hr event hev d hroute hcell)

def RawValid {n} (s : Snapshot n) : Prop := ∀ i p origin,
  s.raw i p = some origin → origin ≤ s.time ∧ s.time ≤ origin + 1

theorem BirthState.raw_valid {n s} (hs : @BirthState n s) : RawValid s := by
  intro i p origin hr
  rw [hs.2.1 i p] at hr
  contradiction

theorem Flow.raw_valid {n θ s u} (f : @Flow n θ s u) : RawValid u := by
  intro i p origin hr
  rw [f.raw_fixed] at hr
  have h := f.raw_support i p origin hr
  exact ⟨h.1.trans f.positive.le, h.2⟩

theorem Jump.raw_valid {n route s u} (j : @Jump n route s u) (hs : RawValid s) : RawValid u := by
  intro i p origin hr
  cases j with
  | arrive d before after queue due free =>
    by_cases hc : i = d.cell
    · subst i
      by_cases hp : p = d.port
      · subst p
        have ht : s.time = origin := by simpa [setRaw] using hr
        change origin ≤ s.time ∧ s.time ≤ origin + 1
        rw [ht]
        constructor <;> linarith
      · apply hs d.cell p origin
        simpa [setRaw, hp] using hr
    · apply hs i p origin
      simpa [setRaw, hc] using hr
  | rawEnd k q start active due =>
    by_cases hc : i = k
    · subst i
      by_cases hp : p = q
      · subst p
        simp [setRaw] at hr
      · apply hs k p origin
        simpa [setRaw, hp] using hr
    · apply hs i p origin
      simpa [setRaw, hc] using hr
  | _ => exact hs i p origin hr

theorem Execution.raw_valid {n θ route s u} (e : @Execution n θ route s u)
    (hs : RawValid s) : RawValid u := by
  induction e with
  | nil => exact hs
  | cons step rest ih =>
    apply ih
    cases step with
    | flow f => exact f.raw_valid
    | jump j => exact j.raw_valid hs

theorem Jump.raw_origin_provenance {n route s u} (j : @Jump n route s u) (i : Fin n)
    (p : Port) (origin : ℝ) (hr : u.raw i p = some origin) :
    s.raw i p = some origin ∨ ∃ d ∈ j.deliveries, d.cell = i ∧ d.port = p ∧ d.due = origin := by
  cases j <;> simp_all [Jump.deliveries, setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]
  all_goals aesop

theorem Execution.raw_origin_provenance {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ) (hr : u.raw i p = some origin) :
    s.raw i p = some origin ∨ ∃ d ∈ e.deliveries, d.cell = i ∧ d.port = p ∧ d.due = origin := by
  induction e with
  | nil => exact Or.inl hr
  | cons step rest ih =>
    rcases ih hr with hmid | ⟨d, hd, hc, hp, ht⟩
    · cases step with
      | flow f => exact Or.inl (by simpa only [f.raw_fixed] using hmid)
      | jump j =>
        rcases j.raw_origin_provenance i p origin hmid with h | ⟨d, hd, hc, hp, ht⟩
        · exact Or.inl h
        · exact Or.inr ⟨d, List.mem_append_left _ hd, hc, hp, ht⟩
    · exact Or.inr ⟨d, List.mem_append_right _ hd, hc, hp, ht⟩

theorem Execution.raw_expired_of_no_arrival {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ) (hs : RawValid s) (hr : s.raw i p = some origin)
    (hno : NoArrivalAt e i p) (ht : origin + 1 < u.time) : u.raw i p = none := by
  cases hu : u.raw i p with
  | none => rfl
  | some actual =>
    rcases e.raw_origin_provenance i p actual hu with h | ⟨d, hd, hc, hp, htime⟩
    · have heq : actual = origin := Option.some.inj (h.symm.trans hr)
      have hv := (e.raw_valid hs i p actual hu).2
      rw [heq] at hv
      linarith
    · rcases hno d hd with h | h
      · exact False.elim (h hc)
      · exact False.elim (h hp)

end KernelR.Hybrid
