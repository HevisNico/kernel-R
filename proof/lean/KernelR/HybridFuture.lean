import KernelR.HybridEventBudget

/-! Physical building blocks for an indefinitely repeatable learned regime.
Silence is constructed from the ODEs. A future-source queue extension preserves
an existing execution; it neither chooses a pulse-case word nor asserts that a
trained cell can serve its next input. -/
namespace KernelR.Hybrid
open MeasureTheory Set

/-- A candidate learned section. The bounds on the active gain and recovery
include the slow protocol's learned values. Reachability is a separate theorem. -/
structure LearnedRest {n} (θ : Fin n → Parameters) (active : Fin n → Port)
    (s : Snapshot n) : Prop where
  main : ∀ i, s.main i = .ready
  aux : ∀ i p, s.aux i p = .ready
  raw : ∀ i p, s.raw i p = none
  pending : s.pending = []
  charge : ∀ i, s.x i .q = 1 / 10
  sensor : ∀ i p, |s.x i (.m p) - 1 / 40| ≤ 1 / 100000
  reserve : ∀ i, 50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100
  gain : ∀ i, 9 / 5 ≤ Real.exp (s.x i (.z (active i))) ∧
    Real.exp (s.x i (.z (active i))) ≤ 19 / 10
  cap : ∀ i p, s.x i (.z p) ≤ Real.log ((θ i).cap p)
  recovery : ∀ i, 17 / 100 ≤ s.x i .b ∧ s.x i .b ≤ 1 / 5

noncomputable def idleValues {n} (s : Snapshot n) (t : ℝ) : Values n :=
  fun i c => match c with
    | .m p => 1 / 40 + (s.x i (.m p) - 1 / 40) * Real.exp (-(1 / 2) * (t - s.time))
    | .energy => 100 + (s.x i .energy - 100) * Real.exp (-10 * (t - s.time))
    | _ => s.x i c

noncomputable def idleAt {n} (s : Snapshot n) (t : ℝ) : Snapshot n :=
  { s with time := t, x := idleValues s t }

theorem idleValues_initial {n} (s : Snapshot n) : idleValues s s.time = s.x := by
  funext i c
  cases c <;> simp [idleValues]

theorem idleValues_sensor {n θ active s} (h : @LearnedRest n θ active s)
    {t : ℝ} (ht : s.time ≤ t) (i : Fin n) (p : Port) :
    |idleValues s t i (.m p) - 1 / 40| ≤ 1 / 100000 := by
  have he : Real.exp (-(1 / 2 : ℝ) * (t - s.time)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hmul := mul_le_mul (h.sensor i p) he (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 1/100000)
  simpa [idleValues, abs_mul, abs_of_pos (Real.exp_pos _)] using hmul

theorem idleValues_reserve {n θ active s} (h : @LearnedRest n θ active s)
    {t : ℝ} (ht : s.time ≤ t) (i : Fin n) :
    50 ≤ idleValues s t i .energy ∧ idleValues s t i .energy ≤ 100 := by
  have hp := (Real.exp_pos (-10 * (t - s.time))).le
  have he : Real.exp (-10 * (t - s.time)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hi := h.reserve i
  dsimp [idleValues]
  constructor <;> nlinarith

theorem idleValues_derivative {n θ active s} (h : @LearnedRest n θ active s)
    (i : Fin n) (c : Coord) (t : ℝ) :
    HasDerivAt (fun v => idleValues s v i c) (field θ s (idleValues s t) t i c) t := by
  cases c with
  | q => simpa [idleValues, field, h.main, h.charge, drive, current, h.raw]
      using hasDerivAt_const t (s.x i .q)
  | z p => simpa [idleValues, field, errorAct, h.aux]
      using hasDerivAt_const t (s.x i (.z p))
  | b => simpa [idleValues, field, markAct, h.main]
      using hasDerivAt_const t (s.x i .b)
  | m p =>
    have hd := (((((hasDerivAt_id t).sub_const s.time).const_mul (-(1/2:ℝ))).exp).const_mul
      (s.x i (.m p) - 1/40)).const_add (1/40)
    convert hd using 1
    · rfl
    · simp [field, h.aux, current, h.raw, idleValues]
      ring
  | energy =>
    have hd := (((((hasDerivAt_id t).sub_const s.time).const_mul (-10:ℝ)).exp).const_mul
      (s.x i .energy - 100)).const_add 100
    convert hd using 1
    · rfl
    · simp [field, work, drive, current, h.raw, h.main, h.aux, errorAct, markAct, idleValues]
      ring

theorem idleValues_field_continuous {n θ active s} (h : @LearnedRest n θ active s)
    (i : Fin n) (c : Coord) : Continuous (fun t => field θ s (idleValues s t) t i c) := by
  cases c <;> simp [field, h.main, h.aux, h.charge, drive, current, h.raw,
    work, errorAct, markAct, idleValues] <;> fun_prop

noncomputable def learnedIdleFlow {n θ active s} (h : @LearnedRest n θ active s)
    {T : ℝ} (hT : s.time < T) : Flow θ s (idleAt s T) where
  positive := hT
  path := idleValues s
  initial := idleValues_initial s
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := by intros i c; cases c <;> dsimp [idleValues] <;> fun_prop
  integrable := fun i c => (idleValues_field_continuous h i c).intervalIntegrable _ _
  mark_integrable := by intros; simp [markAct, h.main]
  integral_eq := by
    intro t ht i c
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => idleValues_derivative h i c v)
      ((idleValues_field_continuous h i c).intervalIntegrable s.time t)
    rw [idleValues_initial] at he
    linarith
  guards := by
    intro t ht
    constructor
    · intro i; norm_num [h.main, idleValues, h.charge]
    · intro i p
      have hm := (abs_le.mp (idleValues_sensor h ht.1 i p)).2
      simpa [h.aux] using (show idleValues s t i (.m p) < 1 by linarith)
  raw_support := by intros; simp_all [h.raw]
  pending_urgent := by intros; simp_all [h.pending]

theorem LearnedRest.idle {n θ active s} (h : @LearnedRest n θ active s)
    {T : ℝ} (hT : s.time ≤ T) : LearnedRest θ active (idleAt s T) where
  main := h.main
  aux := h.aux
  raw := h.raw
  pending := h.pending
  charge := h.charge
  sensor := idleValues_sensor h hT
  reserve := idleValues_reserve h hT
  gain := h.gain
  cap := h.cap
  recovery := h.recovery

theorem LearnedRest.no_jump {n θ active s route} (h : @LearnedRest n θ active s)
    (u : Snapshot n) : IsEmpty (Jump route s u) := by
  constructor
  intro j
  have hm (i : Fin n) (p : Port) : s.x i (.m p) < 1 := by
    have hh := (abs_le.mp (h.sensor i p)).2
    linarith
  cases j <;> simp_all [h.main, h.aux, h.raw, h.pending, h.charge]
  all_goals rename_i i p guard; exact (ne_of_lt (hm i p)) guard

theorem learned_idle_complete {n θ active s route} (h : @LearnedRest n θ active s)
    {T : ℝ} (hT : s.time ≤ T) :
    ∃ e : Execution θ route s (idleAt s T),
      CompleteThrough e T ∧ LearnedRest θ active (idleAt s T) ∧
      e.ledger.emissions = [] := by
  have hrest := h.idle hT
  by_cases he : s.time = T
  · have hat : idleAt s T = s := by
      rw [← he]; unfold idleAt; rw [idleValues_initial]
    subst T
    rw [hat]
    exact ⟨.nil s, ⟨rfl, h.no_jump, by simp [h.pending]⟩, h, rfl⟩
  · let f := learnedIdleFlow h (lt_of_le_of_ne hT he)
    exact ⟨.cons (.flow f) (.nil _),
      ⟨rfl, hrest.no_jump, by simp [idleAt, h.pending]⟩, hrest, rfl⟩

def Execution.append {n θ route s u v} (e : @Execution n θ route s u)
    (f : Execution θ route u v) : Execution θ route s v :=
  match e with
  | .nil _ => f
  | .cons step rest => .cons step (rest.append f)

theorem Execution.append_ledger {n θ route s u v} (e : @Execution n θ route s u)
    (f : Execution θ route u v) : (e.append f).ledger = e.ledger.add f.ledger := by
  induction e with
  | nil => simp [append, ledger, Ledger.zero, Ledger.add]
  | cons step rest ih =>
    simp only [append, ledger, ih, Ledger.add, add_assoc, List.append_assoc]

/-- Future sources are prepended because fire appends routed deliveries. No
sorting convention is used by operational delivery. -/
def withFuture {n} (s : Snapshot n) (future : List (Delivery n)) : Snapshot n :=
  { s with pending := future ++ s.pending }

noncomputable def Flow.withFuture {n θ s u} (f : @Flow n θ s u)
    (future : List (Delivery n)) (hf : ∀ d ∈ future, u.time ≤ d.due) :
    Flow θ (Hybrid.withFuture s future) (Hybrid.withFuture u future) where
  positive := f.positive
  path := f.path
  initial := f.initial
  final := f.final
  main_fixed := f.main_fixed
  aux_fixed := f.aux_fixed
  raw_fixed := f.raw_fixed
  queue_fixed := by simp [Hybrid.withFuture, f.queue_fixed]
  continuous := f.continuous
  integrable := f.integrable
  mark_integrable := f.mark_integrable
  integral_eq := f.integral_eq
  guards := f.guards
  raw_support := f.raw_support
  pending_urgent := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hf d hd
    · exact f.pending_urgent d hd

def Jump.withOneFuture {n route s u} (j : @Jump n route s u) (token : Delivery n) :
    Jump route (Hybrid.withFuture s [token]) (Hybrid.withFuture u [token]) := by
  cases j with
  | fire i mode guard => exact Jump.fire _ i mode guard
  | fastEnd i mode guard => exact Jump.fastEnd _ i mode guard
  | reopen i mode guard => exact Jump.reopen _ i mode guard
  | mark i p mode guard => exact Jump.mark _ i p mode guard
  | silent i p mode guard => exact Jump.silent _ i p mode guard
  | error i p mode guard => exact Jump.error _ i p mode guard
  | auxReady i p mode guard => exact Jump.auxReady _ i p mode guard
  | arrive d before after queue due free =>
    exact Jump.arrive _ d (token :: before) after (congrArg (List.cons token) queue) due free
  | rawEnd i p origin active due => exact Jump.rawEnd _ i p origin active due

noncomputable def Jump.withFuture {n route s u} (j : @Jump n route s u) :
    (future : List (Delivery n)) → Jump route (Hybrid.withFuture s future) (Hybrid.withFuture u future)
  | [] => j
  | token :: rest => (j.withFuture rest).withOneFuture token

theorem Jump.withFuture_ledger {n route s u} (j : @Jump n route s u) (future : List (Delivery n)) :
    (j.withFuture future).ledger = j.ledger := by
  have hone {a b : Snapshot n} (k : Jump route a b) (d : Delivery n) :
      (k.withOneFuture d).ledger = k.ledger := by cases k <;> rfl
  induction future with
  | nil => rfl
  | cons d rest ih => exact (hone _ d).trans ih

noncomputable def Execution.withFuture {n θ route s u} (e : @Execution n θ route s u)
    (future : List (Delivery n)) (hf : ∀ d ∈ future, u.time ≤ d.due) :
    Execution θ route (Hybrid.withFuture s future) (Hybrid.withFuture u future) := by
  induction e with
  | nil => exact .nil _
  | cons step rest ih =>
    cases step with
    | flow f => exact .cons (.flow (f.withFuture future
        (fun d hd => (rest.time_monotone).trans (hf d hd)))) (ih hf)
    | jump j => exact .cons (.jump (j.withFuture future)) (ih hf)

theorem Execution.withFuture_ledger {n θ route s u} (e : @Execution n θ route s u)
    (future : List (Delivery n)) (hf : ∀ d ∈ future, u.time ≤ d.due) :
    (e.withFuture future hf).ledger = e.ledger := by
  induction e with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | flow f => simpa [Execution.withFuture, ledger, Move.ledger, Flow.ledger, Flow.withFuture,
        errorAct, markAct, Hybrid.withFuture] using congrArg (Ledger.add f.ledger) (ih hf)
    | jump j =>
      have hj := j.withFuture_ledger future
      simpa [Execution.withFuture, ledger, Move.ledger, hj] using
        congrArg (Ledger.add j.ledger) (ih hf)

/-- Strict section interiors, unfinished raw supports and strictly future
tokens rule out every one of the nine physical jump constructors. -/
theorem no_jump_interior {n route s} (hg : @BeforeGuards n s s.x)
    (hr : ∀ i p origin, s.raw i p = some origin → s.time < origin+1)
    (hp : ∀ d ∈ s.pending, s.time < d.due) (u : Snapshot n) : IsEmpty (Jump route s u) := by
  constructor
  intro j
  cases j with
  | fire i mode guard | fastEnd i mode guard | reopen i mode guard =>
    have hh := hg.1 i
    simp_all
  | mark i p mode guard | silent i p mode guard | error i p mode guard | auxReady i p mode guard =>
    have hh := hg.2 i p
    simp_all
  | arrive d before after queue due free =>
    have hh := hp d (by rw [queue]; simp)
    linarith
  | rawEnd i p origin active due =>
    have hh := hr i p origin active
    linarith

theorem Flow.interior_saturated {n θ route s u} (f : @Flow n θ s u)
    {T : ℝ} (hT : T ∈ Set.Ico s.time u.time) :
    (∀ v, IsEmpty (Jump route (f.at T) v)) ∧ ∀ d ∈ (f.at T).pending, T < d.due := by
  have hp : ∀ d ∈ (f.at T).pending, T < d.due :=
    fun d hd => hT.2.trans_le (f.pending_urgent d hd)
  refine ⟨no_jump_interior (s := f.at T) (f.guards T hT) ?_ hp, hp⟩
  intro i p origin hraw
  exact hT.2.trans_le (f.raw_support i p origin hraw).2

theorem Flow.complete_prefix {n θ route s u} (f : @Flow n θ s u)
    {T : ℝ} (hT : T ∈ Set.Ico s.time u.time) :
    ∃ (v : Snapshot n) (e : Execution θ route s v), CompleteThrough e T := by
  have hs := f.interior_saturated (route := route) hT
  have hex : Nonempty (Execution θ route s (f.at T)) := by
    by_cases he : T = s.time
    · have hat : f.at T = s := by dsimp [Flow.at]; rw [he, f.initial]
      rw [hat]
      exact ⟨.nil s⟩
    · exact ⟨.cons (.flow (f.prefix (lt_of_le_of_ne hT.1 (Ne.symm he)) hT.2.le)) (.nil _)⟩
  obtain ⟨e⟩ := hex
  exact ⟨f.at T, e, rfl, hs⟩

/-- A complete finite execution can be cut at any earlier horizon, consuming
all zero-time events there. Merely choosing a flow endpoint would not suffice. -/
theorem Execution.complete_prefix {n θ route s u} (e : @Execution n θ route s u)
    (T : ℝ) : CompleteThrough e u.time → s.time ≤ T → T ≤ u.time →
    ∃ (v : Snapshot n) (segment : Execution θ route s v), CompleteThrough segment T := by
  induction e with
  | nil s =>
    intro hc hleft hright
    have he : T = s.time := le_antisymm hright hleft
    subst T
    exact ⟨s, .nil s, hc⟩
  | @cons s middle u step rest ih =>
    intro hc hleft hright
    by_cases he : T < middle.time
    · cases step with
      | flow f => exact f.complete_prefix ⟨hleft, he⟩
      | jump j => rw [j.time_unchanged] at he; exact False.elim (not_lt_of_ge hleft he)
    · obtain ⟨v, segment, hp⟩ := ih hc (le_of_not_gt he) hright
      exact ⟨v, .cons step segment, hp⟩

end KernelR.Hybrid
