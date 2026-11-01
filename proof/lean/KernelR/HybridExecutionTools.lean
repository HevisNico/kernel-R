import KernelR.HybridInputs
import KernelR.HybridPhases

/-! Actual flow and snapshot predicates, first state departures, and chronological execution cuts. -/
namespace KernelR.Hybrid
open Set MeasureTheory


def Execution.AllFlows {n θ route s u}
    (P : ∀ {v w : Snapshot n}, Flow θ v w → Prop) : @Execution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => P f ∧ rest.AllFlows P
  | .cons (.jump _) rest => rest.AllFlows P

theorem Execution.allFlows_append {n θ route s v u}
    (segment : @Execution n θ route s v) (rest : Execution θ route v u)
    (P : ∀ {a b : Snapshot n}, Flow θ a b → Prop) :
    (segment.append rest).AllFlows P ↔ segment.AllFlows P ∧ rest.AllFlows P := by
  induction segment with
  | nil => simp [append, AllFlows]
  | cons step tail ih => cases step <;> simp [append, AllFlows, ih, and_assoc]

theorem Execution.allFlows_mono {n θ route s u} (e : @Execution n θ route s u)
    {P Q : ∀ {v w : Snapshot n}, Flow θ v w → Prop}
    (h : ∀ {v w} (f : Flow θ v w), P f → Q f) (hp : e.AllFlows P) : e.AllFlows Q := by
  induction e with
  | nil => trivial
  | cons step rest ih => cases step with
    | flow f => exact ⟨h f hp.1, ih hp.2⟩
    | jump j => exact ih hp

theorem Execution.allFlows_and {n θ route s u} (e : @Execution n θ route s u)
    {P Q : ∀ {v w : Snapshot n}, Flow θ v w → Prop}
    (hp : e.AllFlows P) (hq : e.AllFlows Q) : e.AllFlows (fun f => P f ∧ Q f) := by
  induction e with
  | nil => trivial
  | cons move rest ih => cases move with
    | flow f => exact ⟨⟨hp.1, hq.1⟩, ih hp.2 hq.2⟩
    | jump j => exact ih hp hq


theorem Execution.IsPrefix.append_left {n θ route s v u}
    (segment : @Execution n θ route s v) (rest : Execution θ route v u) :
    (segment.append rest).IsPrefix segment := by
  induction segment with
  | nil => exact .nil _
  | cons move tail ih => exact .step move _ _ (ih rest)

theorem Execution.IsPrefix.all_flows {n θ route s u v}
    {e : @Execution n θ route s u} {cut : Execution θ route s v} (hcut : e.IsPrefix cut)
    (P : ∀ {a b : Snapshot n}, Flow θ a b → Prop)
    (hprefix : ∀ {a b} (f : Flow θ a b) {t : ℝ} (ht : a.time < t) (hend : t ≤ b.time),
      P f → P (f.prefix ht hend)) (hp : e.AllFlows P) : cut.AllFlows P := by
  induction hcut with
  | nil => trivial
  | flowCut f rest ht hend => exact ⟨hprefix f ht hend hp.1, trivial⟩
  | step move rest cut hcut ih => cases move with
    | flow f => exact ⟨hp.1, ih hp.2⟩
    | jump j => exact ih hp

theorem Execution.allFlows_time_bounds {n θ route s u} (e : @Execution n θ route s u) :
    e.AllFlows (fun {v w} _ => ∀ t ∈ Icc v.time w.time, s.time ≤ t ∧ t ≤ u.time) := by
  induction e with
  | nil => trivial
  | cons move rest ih => cases move with
    | flow f =>
      refine ⟨fun t ht => ⟨ht.1, ht.2.trans rest.time_monotone⟩, ?_⟩
      exact rest.allFlows_mono (fun _ hg t ht => ⟨f.positive.le.trans (hg t ht).1, (hg t ht).2⟩) ih
    | jump j => simpa only [AllFlows, j.time_unchanged] using ih

theorem Execution.zero_duration_continuous {n θ route s u} (e : @Execution n θ route s u)
    (ht : u.time = s.time) : u.x = s.x := by
  induction e with
  | nil => rfl
  | cons move rest ih => cases move with
    | flow f => exact False.elim (by have h := rest.time_monotone; linarith [f.positive])
    | jump j => simpa only [j.physical_continuous] using ih (by simpa only [j.time_unchanged] using ht)

theorem Jump.raw_departure {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port)
    (origin : ℝ) (hs : s.raw i p = some origin) (hu : u.raw i p ≠ some origin) :
    s.time = origin + 1 ∧ u.raw i p = none := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Execution.raw_no_overrun {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ)
    (hm : e.ConstantFlows (fun v => v.raw i p) (some origin)) (ht : s.time ≤ origin + 1) :
    u.time ≤ origin + 1 := by
  induction e with
  | nil => exact ht
  | cons move rest ih => cases move with
    | flow f => exact ih hm.2 (f.raw_support i p origin hm.1).2
    | jump j => exact ih hm (by simpa only [j.time_unchanged] using ht)

structure RawDeparture {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ) where
  beforeEnd : Snapshot n
  afterEnd : Snapshot n
  span : Execution θ route s beforeEnd
  exit : Jump route beforeEnd afterEnd
  rest : Execution θ route afterEnd u
  reconstruct : e = span.append (.cons (.jump exit) rest)
  flows : span.ConstantFlows (fun v => v.raw i p) (some origin)
  raw_before : beforeEnd.raw i p = some origin
  raw_after : afterEnd.raw i p = none
  date : beforeEnd.time = origin + 1

theorem Execution.raw_end_completion {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ) (hr : s.raw i p = some origin)
    (hs : s.time ≤ origin + 1) (ht : origin + 1 < u.time) :
    Nonempty (RawDeparture e i p origin) := by
  rcases e.first_change (fun v => v.raw i p) (some origin)
    (fun f => congrFun (congrFun f.raw_fixed i) p) hr with h | ⟨v,w,segment,exit,rest,he,hm,hv,hw⟩
  · exact False.elim (not_lt_of_ge (e.raw_no_overrun i p origin h.2 hs) ht)
  · have hg := exit.raw_departure i p origin hv hw
    exact ⟨⟨v,w,segment,exit,rest,he,hm,hv,hg.2,hg.1⟩⟩
theorem Jump.raw_allowed_of_no_arrival {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) (origin : ℝ)
    (hs : s.raw i p = none ∨ s.raw i p = some origin)
    (hno : ∀ d ∈ j.deliveries, d.cell ≠ i ∨ d.port ≠ p) :
    u.raw i p = none ∨ u.raw i p = some origin := by
  cases hu : u.raw i p with
  | none => exact Or.inl rfl
  | some t =>
    rcases j.raw_origin_provenance i p t hu with h | ⟨d,hd,hc,hp,_⟩
    · rcases hs with hn | hs
      · rw [hn] at h; contradiction
      · rw [hs] at h; exact Or.inr (congrArg some (Option.some.inj h).symm)
    · rcases hno d hd with h | h
      · exact False.elim (h hc)
      · exact False.elim (h hp)

theorem Execution.raw_allowed_of_no_arrival {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ)
    (hs : s.raw i p = none ∨ s.raw i p = some origin) (hno : NoArrivalAt e i p) :
    (u.raw i p = none ∨ u.raw i p = some origin) ∧
      e.AllFlows (fun {v _w} _ => v.raw i p = none ∨ v.raw i p = some origin) := by
  induction e with
  | nil => exact ⟨hs, trivial⟩
  | cons move rest ih =>
    have hrest : NoArrivalAt rest i p := fun d hd => hno d (List.mem_append_right _ hd)
    cases move with
    | flow f =>
      have h := ih (by simpa only [f.raw_fixed] using hs) hrest
      exact ⟨h.1, hs, h.2⟩
    | jump j => exact ih (j.raw_allowed_of_no_arrival i p origin hs
        (fun d hd => hno d (List.mem_append_left _ hd))) hrest

theorem Execution.raw_absent_allFlows {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (h : e.RawAbsent i p) :
    e.AllFlows (fun {v _w} _ => v.raw i p = none) := by
  induction e with
  | nil => trivial
  | cons move rest ih => cases move with
    | flow f => exact ⟨h.1, ih h.2⟩
    | jump j => exact ih h

theorem Execution.allFlows_forall {n θ route s u α} (e : @Execution n θ route s u)
    (P : α → ∀ {v w : Snapshot n}, Flow θ v w → Prop)
    (h : ∀ a, e.AllFlows (P a)) : e.AllFlows (fun f => ∀ a, P a f) := by
  induction e with
  | nil => trivial
  | cons move rest ih => cases move with
    | flow f => exact ⟨fun a => (h a).1, ih (fun a => (h a).2)⟩
    | jump j => exact ih h

def Execution.AllStates {n θ route s u} (P : Snapshot n → Prop) : @Execution n θ route s u → Prop
  | .nil _ => P s
  | .cons _ rest => P s ∧ rest.AllStates P

theorem Execution.allStates_initial {n θ route s u} (e : @Execution n θ route s u)
    {P : Snapshot n → Prop} (h : e.AllStates P) : P s := by
  cases e <;> simp_all [AllStates]

theorem Execution.allStates_final {n θ route s u} (e : @Execution n θ route s u)
    {P : Snapshot n → Prop} (h : e.AllStates P) : P u := by
  induction e with
  | nil => exact h
  | cons move rest ih => exact ih h.2

theorem Execution.allStates_main_flows {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (mode : MainMode) (h : e.AllStates (fun v => v.main i = mode)) :
    e.MainFlows i mode := by
  induction e with
  | nil => trivial
  | cons move rest ih => cases move with
    | flow f => exact ⟨h.1, ih h.2⟩
    | jump j => exact ih h.2

theorem Execution.allStates_append {n θ route s v u}
    (segment : @Execution n θ route s v) (rest : Execution θ route v u)
    (P : Snapshot n → Prop) :
    (segment.append rest).AllStates P ↔ segment.AllStates P ∧ rest.AllStates P := by
  induction segment with
  | nil => exact ⟨fun h => ⟨rest.allStates_initial h,h⟩,fun h => h.2⟩
  | cons move tail ih => simp only [append,AllStates,ih,and_assoc]

theorem Execution.allStates_aux_flows {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (mode : AuxMode) (h : e.AllStates (fun v => v.aux i p = mode)) :
    e.AuxFlows i p mode := by
  induction e with
  | nil => trivial
  | cons move rest ih => cases move with
    | flow f => exact ⟨h.1,ih h.2⟩
    | jump j => exact ih h.2

theorem Execution.allStates_raw_valid {n θ route s u} (e : @Execution n θ route s u)
    (hs : RawValid s) : e.AllStates RawValid := by
  induction e with
  | nil => exact hs
  | cons move rest ih =>
    refine ⟨hs,ih ?_⟩
    cases move with
    | flow f => exact f.raw_valid
    | jump j => exact j.raw_valid hs

theorem Execution.raw_allowed_states {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ)
    (hs : s.raw i p = none ∨ s.raw i p = some origin) (hno : NoArrivalAt e i p) :
    e.AllStates (fun v => v.raw i p = none ∨ v.raw i p = some origin) := by
  induction e with
  | nil => exact hs
  | cons move rest ih =>
    refine ⟨hs,ih ?_ (fun d hd => hno d (List.mem_append_right _ hd))⟩
    cases move with
    | flow f => simpa only [f.raw_fixed] using hs
    | jump j =>
      exact j.raw_allowed_of_no_arrival i p origin hs
        (fun d hd => hno d (List.mem_append_left _ hd))

/-- Strong first-departure extraction records all discrete snapshots, including
zero-time interleavings and the terminal state. -/
theorem Execution.first_state_change {n θ route s u α} [DecidableEq α]
    (e : @Execution n θ route s u) (observe : Snapshot n → α) (value : α)
    (hfixed : ∀ {v w}, Flow θ v w → observe w = observe v) (hs : observe s = value) :
    e.AllStates (fun v => observe v = value) ∨
    ∃ (v w : Snapshot n) (segment : Execution θ route s v) (exit : Jump route v w)
      (rest : Execution θ route w u),
      e = segment.append (.cons (.jump exit) rest) ∧
      segment.AllStates (fun v => observe v = value) ∧ observe v = value ∧ observe w ≠ value := by
  induction e with
  | nil => exact Or.inl hs
  | @cons s v u move rest ih =>
    by_cases hv : observe v = value
    · rcases ih hv with h | ⟨a,b,segment,exit,tail,he,hp,ha,hb⟩
      · exact Or.inl ⟨hs,h⟩
      · exact Or.inr ⟨a,b,.cons move segment,exit,tail,by simp only [append,he],⟨hs,hp⟩,ha,hb⟩
    · cases move with
      | flow f => exact False.elim (hv ((hfixed f).trans hs))
      | jump j => exact Or.inr ⟨s,v,.nil s,j,rest,rfl,hs,hs,hv⟩

theorem Jump.no_emission_of_ready_states {n route s u} (j : @Jump n route s u)
    (i : Fin n) (hs : s.main i = .ready) (hu : u.main i = .ready) :
    j.ledger.emissions.filter (fun event => event.1 = i) = [] := by
  cases j <;> simp_all [Jump.ledger, Ledger.zero, setMain, setAux, setRaw, Function.update_apply]
  all_goals aesop

theorem Execution.no_emissions_of_ready_states {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (h : e.AllStates (fun v => v.main i = .ready)) : e.emissionTimes i = [] := by
  have hfilter : e.ledger.emissions.filter (fun event => event.1 = i) = [] := by
    induction e with
    | nil => rfl
    | cons move rest ih =>
      have hrest := ih h.2
      change (move.ledger.emissions ++ rest.ledger.emissions).filter _ = []
      rw [List.filter_append, hrest, List.append_nil]
      cases move with
      | flow f => rfl
      | jump j => exact j.no_emission_of_ready_states i h.1 (rest.allStates_initial h.2)
  simp only [Execution.emissionTimes, hfilter, List.map_nil]

end KernelR.Hybrid
