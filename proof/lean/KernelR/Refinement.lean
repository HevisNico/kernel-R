import KernelR.Hybrid
import KernelR.Chain.Refinement

/-! Exact physical ledger identities. These theorems quantify over admissible
finite executions, but do not assert existence for the certified protocol. -/
namespace KernelR.Hybrid
open MeasureTheory

structure Ledger (n : ℕ) where
  error : Fin n → Port → ℝ
  mark : Fin n → Port → ℝ
  recovery : Fin n → ℝ
  emissions : List (Fin n × ℝ)
  issued : ℕ
  delivered : ℕ
noncomputable def Ledger.zero {n} : Ledger n := ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, [], 0, 0⟩
noncomputable def Ledger.add {n} (l r : Ledger n) : Ledger n :=
  ⟨fun i p => l.error i p + r.error i p, fun i p => l.mark i p + r.mark i p,
   fun i => l.recovery i + r.recovery i,
   l.emissions ++ r.emissions, l.issued + r.issued, l.delivered + r.delivered⟩
noncomputable def Flow.ledger {n θ s u} (f : @Flow n θ s u) : Ledger n :=
  ⟨fun i p => ∫ t in s.time..u.time, errorAct θ s (f.path t) i p,
   fun i p => ∫ t in s.time..u.time, markAct θ s (f.path t) i p,
   fun i => ∫ t in s.time..u.time, ∑ p : Port, markAct θ s (f.path t) i p,
   [], 0, 0⟩
noncomputable def Jump.ledger {n route s u} (j : @Jump n route s u) : Ledger n := by
  cases j
  case fire i _ _ => exact ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, [(i, s.time)], (route i s.time).length, 0⟩
  case arrive => exact { Ledger.zero with delivered := 1 }
  all_goals exact Ledger.zero
noncomputable def Move.ledger {n θ route s u} : @Move n θ route s u → Ledger n
  | .flow f => f.ledger
  | .jump j => j.ledger
noncomputable def Execution.ledger {n θ route s u} : @Execution n θ route s u → Ledger n
  | .nil _ => Ledger.zero
  | .cons step rest => step.ledger.add rest.ledger

theorem Jump.physical_continuous {n route s u} (j : @Jump n route s u) : u.x = s.x := by
  cases j <;> rfl

theorem Jump.time_unchanged {n route s u} (j : @Jump n route s u) : u.time = s.time := by
  cases j <;> rfl

theorem Jump.no_actuation {n route s u} (j : @Jump n route s u) :
    (∀ i p, j.ledger.error i p = 0) ∧ (∀ i, j.ledger.recovery i = 0) := by
  cases j <;> exact ⟨fun _ _ => rfl, fun _ => rfl⟩

theorem Flow.gain_balance {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port) :
    u.x i (.z p) = s.x i (.z p) + f.ledger.error i p := by
  have h := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i (.z p)
  simpa only [f.final, field, Flow.ledger] using h

theorem Flow.recovery_balance {n θ s u} (f : @Flow n θ s u) (i : Fin n) :
    u.x i .b = s.x i .b + f.ledger.recovery i := by
  have h := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i .b
  simpa only [f.final, field, Flow.ledger] using h

theorem Move.gain_balance {n θ route s u} (m : @Move n θ route s u) (i : Fin n) (p : Port) :
    u.x i (.z p) = s.x i (.z p) + m.ledger.error i p := by
  cases m with
  | flow f => exact f.gain_balance i p
  | jump j => simp only [Move.ledger, j.physical_continuous, j.no_actuation.1, add_zero]

theorem Move.recovery_balance {n θ route s u} (m : @Move n θ route s u) (i : Fin n) :
    u.x i .b = s.x i .b + m.ledger.recovery i := by
  cases m with
  | flow f => exact f.recovery_balance i
  | jump j => simp only [Move.ledger, j.physical_continuous, j.no_actuation.2, add_zero]

theorem Jump.queue_balance {n route s u} (j : @Jump n route s u) :
    u.pending.length + j.ledger.delivered = s.pending.length + j.ledger.issued := by
  cases j <;> simp_all [Jump.ledger, Ledger.zero, setMain, setAux, setRaw, List.length_append, Nat.add_assoc]

theorem Move.queue_balance {n θ route s u} (m : @Move n θ route s u) :
    u.pending.length + m.ledger.delivered = s.pending.length + m.ledger.issued := by
  cases m with
  | flow f => simp [Move.ledger, Flow.ledger, f.queue_fixed]
  | jump j => exact j.queue_balance

theorem Execution.gain_balance {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) : u.x i (.z p) = s.x i (.z p) + e.ledger.error i p := by
  induction e with
  | nil => simp [Execution.ledger, Ledger.zero]
  | cons step rest ih =>
    rw [ih, step.gain_balance i p]
    simp only [Execution.ledger, Ledger.add]; ring

theorem Execution.recovery_balance {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) : u.x i .b = s.x i .b + e.ledger.recovery i := by
  induction e with
  | nil => simp [Execution.ledger, Ledger.zero]
  | cons step rest ih =>
    rw [ih, step.recovery_balance i]
    simp only [Execution.ledger, Ledger.add]; ring

theorem Execution.queue_balance {n θ route s u} (e : @Execution n θ route s u) :
    u.pending.length + e.ledger.delivered = s.pending.length + e.ledger.issued := by
  induction e with
  | nil => simp [Execution.ledger, Ledger.zero]
  | cons step rest ih =>
    have h := step.queue_balance
    simp only [Execution.ledger, Ledger.add]
    omega

theorem Execution.time_monotone {n θ route s u} (e : @Execution n θ route s u) :
    s.time ≤ u.time := by
  induction e with
  | nil => exact le_rfl
  | cons step rest ih =>
    apply le_trans _ ih
    cases step with
    | flow f => exact f.positive.le
    | jump j => exact j.time_unchanged.ge

/-- No inferred full dose at a saturated gain cap, regardless of ERROR charge. -/
theorem errorAct_cap_closed {n θ s x} (i : Fin n) (p : Port)
    (h : Real.log ((θ i).cap p) ≤ x i (.z p)) : errorAct θ s x i p = 0 := by
  simp [errorAct, not_lt.mpr h]
theorem errorAct_energy_closed {n θ s x} (i : Fin n) (p : Port)
    (h : x i .energy ≤ 0) : errorAct θ s x i p = 0 := by
  simp [errorAct, not_lt.mpr h]
theorem markAct_cap_closed {n θ s x} (i : Fin n) (p : Port)
    (h : 11 / 10 ≤ x i .b) : markAct θ s x i p = 0 := by
  simp [markAct, not_lt.mpr h]
theorem markAct_energy_closed {n θ s x} (i : Fin n) (p : Port)
    (h : x i .energy ≤ 0) : markAct θ s x i p = 0 := by
  simp [markAct, not_lt.mpr h]

theorem partial_error_example :
    8 * ((7 / 100 : ℝ) - 1 / 40) = 9 / 25 ∧
    8 * ((7 / 100 : ℝ) - 1 / 40) ≠ 3 / 5 := by norm_num
/-- Open exposure is an explicit physical premise here. The protocol theorem
must derive it; this predicate does not establish that chronology. -/
def ErrorOpen {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port) : Prop :=
  s.aux i p = .error ∧ s.main i = .ready ∧
  ∀ t ∈ Set.Icc s.time u.time, 0 < f.path t i .energy ∧
    f.path t i (.z p) < Real.log ((θ i).cap p)

theorem Flow.error_charge_balance {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (ho : ErrorOpen f i p) :
    f.ledger.error i p = 8 * (s.x i (.m p) - u.x i (.m p)) := by
  have hc := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i (.m p)
  rw [f.final] at hc
  have he : (∫ t in s.time..u.time, errorAct θ s (f.path t) i p) =
      -8 * (∫ t in s.time..u.time, field θ s (f.path t) t i (.m p)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le f.positive.le] at ht
    simp [errorAct, ho.1, ho.2.1, (ho.2.2 t ht).1, (ho.2.2 t ht).2,
      field, auxDrain]
    ring
  change (∫ t in s.time..u.time, errorAct θ s (f.path t) i p) = _
  rw [he]; linarith

theorem Flow.full_error_of_open_endpoints {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (p : Port) (ho : ErrorOpen f i p)
    (hs : s.x i (.m p) = 1 / 10) (hu : u.x i (.m p) = 1 / 40) :
    f.ledger.error i p = 3 / 5 := by
  rw [f.error_charge_balance i p ho, hs, hu]; norm_num

/-- Gate exposure on each flow is still a premise, never a recorded case label. -/
def Execution.ErrorExposed {n θ route s u} (i : Fin n) (p : Port) :
    @Execution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => ErrorOpen f i p ∧ rest.ErrorExposed i p
  | .cons (.jump _) rest => rest.ErrorExposed i p

theorem Execution.error_charge_balance {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (ho : e.ErrorExposed i p) :
    e.ledger.error i p = 8 * (s.x i (.m p) - u.x i (.m p)) := by
  induction e with
  | nil => simp [Execution.ledger, Ledger.zero]
  | cons step rest ih =>
    cases step with
    | flow f =>
      have hf := f.error_charge_balance i p ho.1
      have hr := ih ho.2
      simp only [Execution.ledger, Move.ledger, Ledger.add]
      linarith
    | jump j =>
      have hr := ih ho
      simp only [Execution.ledger, Move.ledger, Ledger.add, j.no_actuation.1, zero_add]
      rw [hr, j.physical_continuous]

/-- Full ERROR dose across legal zero-time interleavings, conditional on exposure. -/
theorem Execution.full_error_of_open_endpoints {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (ho : e.ErrorExposed i p) (hs : s.x i (.m p) = 1 / 10)
    (hu : u.x i (.m p) = 1 / 40) : e.ledger.error i p = 3 / 5 := by
  rw [e.error_charge_balance i p ho, hs, hu]; norm_num

/-- Reopening the main admission does not delete any unfinished raw current. -/
theorem reopen_preserves_raw {n} (s : Snapshot n) (i : Fin n) :
    (setMain s i .ready).raw = s.raw := rfl

theorem canonical_raw_tail_positive {origin t : ℝ}
    (h₁ : origin ≤ t) (h₂ : t < origin + 1) : 0 < pulse origin t := by
  rw [pulse, ite_eq_left ⟨h₁, h₂⟩]
  exact mul_pos (Real.log_pos (by norm_num)) (Real.exp_pos _)

noncomputable def Flow.markIntegral {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (p : Port) : ℝ :=
  ∫ t in s.time..u.time, markAct θ s (f.path t) i p

def MarkOpen {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port) : Prop :=
  s.aux i p = .mark ∧ s.main i ≠ .ready ∧
  ∀ t ∈ Set.Icc s.time u.time, 0 < f.path t i .energy ∧ f.path t i .b < 11 / 10

theorem Flow.mark_charge_balance {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (ho : MarkOpen f i p) :
    f.markIntegral i p = (1 / 2) * (s.x i (.m p) - u.x i (.m p)) := by
  have hc := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i (.m p)
  rw [f.final] at hc
  have he : (∫ t in s.time..u.time, markAct θ s (f.path t) i p) =
      -(1 / 2) * (∫ t in s.time..u.time, field θ s (f.path t) t i (.m p)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le f.positive.le] at ht
    simp [markAct, ho.1, ho.2.1, (ho.2.2 t ht).1, (ho.2.2 t ht).2, field, auxDrain]
    ring
  change (∫ t in s.time..u.time, markAct θ s (f.path t) i p) = _
  rw [he]; linarith

theorem Flow.full_mark_of_open_endpoints {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (p : Port) (ho : MarkOpen f i p)
    (hs : s.x i (.m p) = 1) (hu : u.x i (.m p) = 4 / 5) :
    f.markIntegral i p = 1 / 10 := by
  rw [f.mark_charge_balance i p ho, hs, hu]; norm_num

/-- Recovery includes all ports; isolating a single port requires this premise. -/
theorem Flow.recovery_of_only_mark {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (p : Port)
    (h : ∀ t ∈ Set.uIcc s.time u.time, ∀ j, j ≠ p → markAct θ s (f.path t) i j = 0) :
    f.ledger.recovery i = f.markIntegral i p := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact Finset.sum_eq_single p (fun j _ hj => h t ht j hj) (by simp)

/-- A nonempty, progressing witness for any positive number of cells without
sources. It does not establish existence for a training protocol. -/
noncomputable def resting {n : ℕ} (t : ℝ) : Snapshot n :=
  ⟨t, (fun _ c => match c with
    | .q => 1 / 10 | .m _ => 1 / 40 | .z _ => 0 | .b => 2 / 25 | .energy => 100),
   fun _ => .ready, fun _ _ => .ready, fun _ _ => none, []⟩

theorem resting_field {n} (θ : Fin n → Parameters) (s t : ℝ) (i : Fin n) (c : Coord) :
    field θ (resting s) (resting s).x t i c = 0 := by
  cases c <;> simp [field, resting, drive, current, work, errorAct, markAct]

noncomputable def restingFlow {n} (θ : Fin n → Parameters) {T : ℝ} (hT : 0 < T) :
    Flow θ (resting 0) (resting T) where
  positive := hT
  path := fun _ => (resting 0).x
  initial := rfl
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := fun _ _ => continuousOn_const
  integrable := by intros; simp only [resting_field]; exact intervalIntegrable_const
  mark_integrable := by intros; simp [markAct, resting]
  integral_eq := by intros; simp [resting_field]
  guards := by intros; constructor <;> intros <;> norm_num [BeforeGuards, resting]
  raw_support := by intros; simp_all [resting]
  pending_urgent := by intros; simp_all [resting]

theorem resting_no_jump {n route T u} : IsEmpty (@Jump n route (resting T) u) := by
  constructor
  intro j
  cases j <;> simp_all [resting]

/-- A complete positive-duration execution exists for the silent protocol. -/
theorem resting_complete_exists {n} (θ : Fin n → Parameters) (route : Router n)
    {T : ℝ} (hT : 0 < T) :
    ∃ e : Execution θ route (resting 0) (resting T), CompleteThrough e T := by
  refine ⟨.cons (.flow (restingFlow θ hT)) (.nil _), rfl, ?_, ?_⟩
  · intro u; exact resting_no_jump
  · simp [resting]

/-- A nominal READY birth with no sources. Unlike `resting`, its log-gains
belong to the declared birth family. -/
noncomputable def birthResting {n : ℕ} (t : ℝ) : Snapshot n :=
  ⟨t, (fun _ c => match c with
    | .q => 1 / 10 | .m _ => 1 / 40 | .z p => Real.log (nominalGain p)
    | .b => 2 / 25 | .energy => 100),
   fun _ => .ready, fun _ _ => .ready, fun _ _ => none, []⟩

theorem birthResting_birth {n} : BirthState (birthResting (n := n) 0) := by
  refine ⟨rfl, fun _ _ => rfl, ?_⟩
  intro i
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · norm_num [birthResting]
  · norm_num [birthResting]
  · norm_num [birthResting]
  · intro p
    refine ⟨?_, Or.inl ?_⟩
    · change Real.log (nominalGain p) - 1 / 100000 ≤ Real.log (nominalGain p) ∧
        Real.log (nominalGain p) ≤ Real.log (nominalGain p) + 1 / 100000
      constructor <;> linarith
    · norm_num [birthResting]

theorem birthResting_field {n} (θ : Fin n → Parameters) (s t : ℝ)
    (i : Fin n) (c : Coord) : field θ (birthResting s) (birthResting s).x t i c = 0 := by
  cases c <;> simp [field, birthResting, drive, current, work, errorAct, markAct]

noncomputable def birthRestingFlow {n} (θ : Fin n → Parameters) {T : ℝ} (hT : 0 < T) :
    Flow θ (birthResting 0) (birthResting T) where
  positive := hT
  path := fun _ => (birthResting 0).x
  initial := rfl
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := fun _ _ => continuousOn_const
  integrable := by intros; simp only [birthResting_field]; exact intervalIntegrable_const
  mark_integrable := by intros; simp [markAct, birthResting]
  integral_eq := by intros; simp [birthResting_field]
  guards := by intros; constructor <;> intros <;> norm_num [BeforeGuards, birthResting]
  raw_support := by intros; simp_all [birthResting]
  pending_urgent := by intros; simp_all [birthResting]

theorem birthResting_no_jump {n route T u} : IsEmpty (@Jump n route (birthResting T) u) := by
  constructor
  intro j
  cases j <;> simp_all [birthResting]

/-- A complete positive-duration silent execution starts in the actual birth
family. This is a concrete witness, not existence for the training protocols
or for every member of the birth family. -/
theorem birth_resting_complete_exists {n} (θ : Fin n → Parameters) (route : Router n)
    {T : ℝ} (hT : 0 < T) :
    ∃ e : Execution θ route (birthResting 0) (birthResting T),
      BirthState (birthResting (n := n) 0) ∧ CompleteThrough e T := by
  refine ⟨.cons (.flow (birthRestingFlow θ hT)) (.nil _), birthResting_birth, rfl, ?_, ?_⟩
  · intro u; exact birthResting_no_jump
  · simp [birthResting]

/-- Two compatible simultaneous guards admit both zero-duration orders.
No priority between a main firing and an auxiliary MARK is imposed. -/
theorem simultaneous_fire_mark_orders {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : s.main i = .ready) (hq : s.x i .q = 1)
    (ha : s.aux i p = .ready) (hx : s.x i (.m p) = 1) :
    Nonempty (Execution θ (fun _ _ => []) s (setAux (setMain s i .fast) i p .mark)) ∧
    Nonempty (Execution θ (fun _ _ => []) s (setMain (setAux s i p .mark) i .fast)) := by
  have fire : Jump (fun _ _ => []) s (setMain s i .fast) := by
    simpa [setMain, setAux] using (Jump.fire (route := fun _ _ => []) s i hm hq)
  have mark : Jump (fun _ _ => []) s (setAux s i p .mark) := Jump.mark s i p ha hx
  constructor
  · exact ⟨.cons (.jump fire) (.cons (.jump (Jump.mark _ i p ha hx)) (.nil _))⟩
  · have hf : Jump (fun _ _ => []) (setAux s i p .mark)
        (setMain (setAux s i p .mark) i .fast) := by
      simpa [setMain, setAux] using (Jump.fire (route := fun _ _ => []) (setAux s i p .mark) i hm hq)
    exact ⟨.cons (.jump mark) (.cons (.jump hf) (.nil _))⟩

/-- The finite signal is extracted from actual fire jumps, including their exact
count. The default time beyond the count is irrelevant padding. -/
noncomputable def Execution.emissionTimes {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) : List ℝ :=
  (e.ledger.emissions.filter (fun event => event.1 = i)).map Prod.snd

noncomputable def Execution.signal {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) : KernelR.Chain.Signal :=
  ⟨(e.emissionTimes i).length, fun k => (e.emissionTimes i)[k]?.getD 0⟩

theorem Execution.signal_count {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) :
    (e.signal i).count = (e.emissionTimes i).length := rfl

/-- This exposes both outstanding obligations for the physical packet theorem:
exact event count and correspondence of every actual emission date. -/
theorem Execution.hasPacket_of_emission_witness {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) {m L J}
    (packet : KernelR.Chain.Packet m L J)
    (hc : (e.emissionTimes i).length = m + L)
    (ht : ∀ k, k < m + L → (e.signal i).time k = packet.actual k) :
    KernelR.Chain.HasPacket (e.signal i) m L J := ⟨hc, packet, ht⟩

theorem Flow.recovery_sum_marks {n θ s u} (f : @Flow n θ s u) (i : Fin n) :
    f.ledger.recovery i = ∑ p : Port, f.ledger.mark i p := by
  exact intervalIntegral.integral_finsetSum (fun p _ => f.mark_integrable i p)

theorem Jump.recovery_sum_marks {n route s u} (j : @Jump n route s u) (i : Fin n) :
    j.ledger.recovery i = ∑ p : Port, j.ledger.mark i p := by
  cases j <;> simp [Jump.ledger, Ledger.zero]

theorem Execution.recovery_sum_marks {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) : e.ledger.recovery i = ∑ p : Port, e.ledger.mark i p := by
  induction e with
  | nil => simp [Execution.ledger, Ledger.zero]
  | cons step rest ih =>
    have hm : step.ledger.recovery i = ∑ p : Port, step.ledger.mark i p := by
      cases step with
      | flow f => exact f.recovery_sum_marks i
      | jump j => exact j.recovery_sum_marks i
    simp only [Execution.ledger, Ledger.add, Finset.sum_add_distrib]
    rw [hm, ih]

def Execution.MarkExposed {n θ route s u} (i : Fin n) (p : Port) :
    @Execution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => MarkOpen f i p ∧ rest.MarkExposed i p
  | .cons (.jump _) rest => rest.MarkExposed i p

theorem Jump.no_mark_actuation {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port) :
    j.ledger.mark i p = 0 := by cases j <;> rfl

theorem Execution.mark_charge_balance {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (ho : e.MarkExposed i p) :
    e.ledger.mark i p = (1 / 2) * (s.x i (.m p) - u.x i (.m p)) := by
  induction e with
  | nil => simp [Execution.ledger, Ledger.zero]
  | cons step rest ih =>
    cases step with
    | flow f =>
      have hf := f.mark_charge_balance i p ho.1
      have hr := ih ho.2
      change f.ledger.mark i p = _ at hf
      simp only [Execution.ledger, Move.ledger, Ledger.add]
      linarith
    | jump j =>
      have hr := ih ho
      simp only [Execution.ledger, Move.ledger, Ledger.add, j.no_mark_actuation, zero_add]
      rw [hr, j.physical_continuous]

theorem Execution.full_mark_of_open_endpoints {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (ho : e.MarkExposed i p) (hs : s.x i (.m p) = 1)
    (hu : u.x i (.m p) = 4 / 5) : e.ledger.mark i p = 1 / 10 := by
  rw [e.mark_charge_balance i p ho, hs, hu]; norm_num

end KernelR.Hybrid
