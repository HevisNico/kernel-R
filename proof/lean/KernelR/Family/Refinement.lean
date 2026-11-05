import KernelR.Family.Model

/-! Parametric physical ledger and exact transfer identities.

Adapted from KernelR/Refinement.lean (Nicolas Breuillaud, CC BY 4.0).
All constants remain symbolic. No numerical protocol, fabrication box, or
existence premise is used to derive a transfer on an actually exposed phase.
-/
namespace KernelR.Family
open KernelR.Hybrid MeasureTheory Set
variable {cfg : Constants}

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
noncomputable def Flow.ledger {n θ s u} (f : @Flow n cfg θ s u) : Ledger n :=
  ⟨fun i p => ∫ t in s.time..u.time, errorAct cfg θ s (f.path t) i p,
   fun i p => ∫ t in s.time..u.time, markAct cfg θ s (f.path t) i p,
   fun i => ∫ t in s.time..u.time, ∑ p : Port, markAct cfg θ s (f.path t) i p,
   [], 0, 0⟩
noncomputable def Jump.ledger {n route s u} (j : @Jump n cfg route s u) : Ledger n := by
  cases j
  case fire i _ _ => exact ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, [(i, s.time)], (route i s.time).length, 0⟩
  case arrive => exact { Ledger.zero with delivered := 1 }
  all_goals exact Ledger.zero
noncomputable def Move.ledger {n θ route s u} : @Move n cfg θ route s u → Ledger n
  | .flow f => f.ledger
  | .jump j => j.ledger
noncomputable def Execution.ledger {n θ route s u} : @Execution n cfg θ route s u → Ledger n
  | .nil _ => Ledger.zero
  | .cons step rest => step.ledger.add rest.ledger

theorem Jump.no_actuation {n route s u} (j : @Jump n cfg route s u) :
    (∀ i p, j.ledger.error i p = 0) ∧ (∀ i, j.ledger.recovery i = 0) := by
  cases j <;> exact ⟨fun _ _ => rfl, fun _ => rfl⟩

theorem Flow.gain_balance {n θ s u} (f : @Flow n cfg θ s u) (i : Fin n) (p : Port) :
    u.x i (.z p) = s.x i (.z p) + f.ledger.error i p := by
  have h := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i (.z p)
  simpa only [f.final, field, Flow.ledger] using h

theorem Flow.recovery_balance {n θ s u} (f : @Flow n cfg θ s u) (i : Fin n) :
    u.x i .b = s.x i .b + f.ledger.recovery i := by
  have h := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i .b
  simpa only [f.final, field, Flow.ledger] using h

theorem Move.gain_balance {n θ route s u} (m : @Move n cfg θ route s u) (i : Fin n) (p : Port) :
    u.x i (.z p) = s.x i (.z p) + m.ledger.error i p := by
  cases m with
  | flow f => exact f.gain_balance i p
  | jump j => simp only [Move.ledger, j.physical_continuous, j.no_actuation.1, add_zero]

theorem Move.recovery_balance {n θ route s u} (m : @Move n cfg θ route s u) (i : Fin n) :
    u.x i .b = s.x i .b + m.ledger.recovery i := by
  cases m with
  | flow f => exact f.recovery_balance i
  | jump j => simp only [Move.ledger, j.physical_continuous, j.no_actuation.2, add_zero]

theorem Execution.gain_balance {n θ route s u} (e : @Execution n cfg θ route s u)
    (i : Fin n) (p : Port) : u.x i (.z p) = s.x i (.z p) + e.ledger.error i p := by
  induction e with
  | nil => simp [Execution.ledger, Ledger.zero]
  | cons step rest ih =>
    rw [ih, step.gain_balance i p]
    simp only [Execution.ledger, Ledger.add]; ring

theorem Execution.recovery_balance {n θ route s u} (e : @Execution n cfg θ route s u)
    (i : Fin n) : u.x i .b = s.x i .b + e.ledger.recovery i := by
  induction e with
  | nil => simp [Execution.ledger, Ledger.zero]
  | cons step rest ih =>
    rw [ih, step.recovery_balance i]
    simp only [Execution.ledger, Ledger.add]; ring

def ErrorOpen {n θ s u} (f : @Flow n cfg θ s u) (i : Fin n) (p : Port) : Prop :=
  s.aux i p = .error ∧ s.main i = .ready ∧
  ∀ t ∈ Set.Icc s.time u.time, 0 < f.path t i .energy ∧
    f.path t i (.z p) < Real.log ((θ i).cap p)

theorem Flow.error_charge_balance {n θ s u} (f : @Flow n cfg θ s u) (i : Fin n) (p : Port)
    (ho : ErrorOpen f i p) :
    f.ledger.error i p = cfg.gainFactor * (s.x i (.m p) - u.x i (.m p)) := by
  have hc := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i (.m p)
  rw [f.final] at hc
  have he : (∫ t in s.time..u.time, errorAct cfg θ s (f.path t) i p) =
      -cfg.gainFactor * (∫ t in s.time..u.time, field cfg θ s (f.path t) t i (.m p)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le f.positive.le] at ht
    simp [errorAct, ho.1, ho.2.1, (ho.2.2 t ht).1, (ho.2.2 t ht).2,
      field, auxDrain]
    ring
  change (∫ t in s.time..u.time, errorAct cfg θ s (f.path t) i p) = _
  rw [he]; linear_combination cfg.gainFactor * hc

/-- The affine charge/gain relation holds at every observation time inside
an exposed ERROR flow, including cuts strictly inside the phase. -/
theorem Flow.error_affine_invariant {n θ s u} (f : @Flow n cfg θ s u)
    (i : Fin n) (p : Port) (exposed : ErrorOpen f i p)
    {t : ℝ} (ht : t ∈ Icc s.time u.time) :
    f.path t i (.z p) + cfg.gainFactor * f.path t i (.m p) =
      s.x i (.z p) + cfg.gainFactor * s.x i (.m p) := by
  have hm := f.integral_eq t ht i (.m p)
  have hz := f.integral_eq t ht i (.z p)
  change f.path t i (.z p) = s.x i (.z p) +
    ∫ v in s.time..t, errorAct cfg θ s (f.path v) i p at hz
  have he : (∫ v in s.time..t, errorAct cfg θ s (f.path v) i p) =
      -cfg.gainFactor * (∫ v in s.time..t, field cfg θ s (f.path v) v i (.m p)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le ht.1] at hv
    have hwhole : v ∈ Icc s.time u.time := ⟨hv.1, hv.2.trans ht.2⟩
    simp [errorAct, exposed.1, exposed.2.1, (exposed.2.2 v hwhole).1,
      (exposed.2.2 v hwhole).2, field, auxDrain]
    ring
  rw [he] at hz
  linear_combination hz + cfg.gainFactor * hm

theorem Flow.full_error_of_open_endpoints {n θ s u} (f : @Flow n cfg θ s u)
    (i : Fin n) (p : Port) (ho : ErrorOpen f i p)
    (hs : s.x i (.m p) = cfg.errorLevel) (hu : u.x i (.m p) = cfg.auxRest) :
    f.ledger.error i p = cfg.errorDose := by
  rw [f.error_charge_balance i p ho, hs, hu]; rfl

/-- Gate exposure on each flow is still a premise, never a recorded case label. -/
def Execution.ErrorExposed {n θ route s u} (i : Fin n) (p : Port) :
    @Execution n cfg θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => ErrorOpen f i p ∧ rest.ErrorExposed i p
  | .cons (.jump _) rest => rest.ErrorExposed i p

theorem Execution.error_charge_balance {n θ route s u} (e : @Execution n cfg θ route s u)
    (i : Fin n) (p : Port) (ho : e.ErrorExposed i p) :
    e.ledger.error i p = cfg.gainFactor * (s.x i (.m p) - u.x i (.m p)) := by
  induction e with
  | nil => simp [Execution.ledger, Ledger.zero]
  | cons step rest ih =>
    cases step with
    | flow f =>
      have hf := f.error_charge_balance i p ho.1
      have hr := ih ho.2
      simp only [Execution.ledger, Move.ledger, Ledger.add]
      rw [hf, hr]
      ring
    | jump j =>
      have hr := ih ho
      simp only [Execution.ledger, Move.ledger, Ledger.add, j.no_actuation.1, zero_add]
      rw [hr, j.physical_continuous]

/-- Full ERROR dose across legal zero-time interleavings, conditional on exposure. -/
theorem Execution.full_error_of_open_endpoints {n θ route s u}
    (e : @Execution n cfg θ route s u) (i : Fin n) (p : Port)
    (ho : e.ErrorExposed i p) (hs : s.x i (.m p) = cfg.errorLevel)
    (hu : u.x i (.m p) = cfg.auxRest) : e.ledger.error i p = cfg.errorDose := by
  rw [e.error_charge_balance i p ho, hs, hu]; rfl

noncomputable def Flow.markIntegral {n θ s u} (f : @Flow n cfg θ s u)
    (i : Fin n) (p : Port) : ℝ :=
  ∫ t in s.time..u.time, markAct cfg θ s (f.path t) i p

def MarkOpen {n θ s u} (f : @Flow n cfg θ s u) (i : Fin n) (p : Port) : Prop :=
  s.aux i p = .mark ∧ s.main i ≠ .ready ∧
  ∀ t ∈ Set.Icc s.time u.time, 0 < f.path t i .energy ∧ f.path t i .b < cfg.recoveryCap

theorem Flow.mark_charge_balance {n θ s u} (f : @Flow n cfg θ s u) (i : Fin n) (p : Port)
    (ho : MarkOpen f i p) :
    f.markIntegral i p = cfg.recoveryFactor * (s.x i (.m p) - u.x i (.m p)) := by
  have hc := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i (.m p)
  rw [f.final] at hc
  have he : (∫ t in s.time..u.time, markAct cfg θ s (f.path t) i p) =
      -cfg.recoveryFactor * (∫ t in s.time..u.time, field cfg θ s (f.path t) t i (.m p)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le f.positive.le] at ht
    simp [markAct, ho.1, ho.2.1, (ho.2.2 t ht).1, (ho.2.2 t ht).2, field, auxDrain]
    ring
  change (∫ t in s.time..u.time, markAct cfg θ s (f.path t) i p) = _
  rw [he]; linear_combination cfg.recoveryFactor * hc

theorem Flow.full_mark_of_open_endpoints {n θ s u} (f : @Flow n cfg θ s u)
    (i : Fin n) (p : Port) (ho : MarkOpen f i p)
    (hs : s.x i (.m p) = cfg.auxThreshold) (hu : u.x i (.m p) = cfg.markExit) :
    f.markIntegral i p = cfg.markDose := by
  rw [f.mark_charge_balance i p ho, hs, hu]; rfl

theorem Flow.recovery_sum_marks {n θ s u} (f : @Flow n cfg θ s u) (i : Fin n) :
    f.ledger.recovery i = ∑ p : Port, f.ledger.mark i p := by
  exact intervalIntegral.integral_finsetSum (fun p _ => f.mark_integrable i p)

theorem Jump.recovery_sum_marks {n route s u} (j : @Jump n cfg route s u) (i : Fin n) :
    j.ledger.recovery i = ∑ p : Port, j.ledger.mark i p := by
  cases j <;> simp [Jump.ledger, Ledger.zero]

theorem Execution.recovery_sum_marks {n θ route s u} (e : @Execution n cfg θ route s u)
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
    @Execution n cfg θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => MarkOpen f i p ∧ rest.MarkExposed i p
  | .cons (.jump _) rest => rest.MarkExposed i p

theorem Jump.no_mark_actuation {n route s u} (j : @Jump n cfg route s u) (i : Fin n) (p : Port) :
    j.ledger.mark i p = 0 := by cases j <;> rfl

theorem Execution.mark_charge_balance {n θ route s u} (e : @Execution n cfg θ route s u)
    (i : Fin n) (p : Port) (ho : e.MarkExposed i p) :
    e.ledger.mark i p = cfg.recoveryFactor * (s.x i (.m p) - u.x i (.m p)) := by
  induction e with
  | nil => simp [Execution.ledger, Ledger.zero]
  | cons step rest ih =>
    cases step with
    | flow f =>
      have hf := f.mark_charge_balance i p ho.1
      have hr := ih ho.2
      change f.ledger.mark i p = _ at hf
      simp only [Execution.ledger, Move.ledger, Ledger.add]
      rw [hf, hr]
      ring
    | jump j =>
      have hr := ih ho
      simp only [Execution.ledger, Move.ledger, Ledger.add, j.no_mark_actuation, zero_add]
      rw [hr, j.physical_continuous]

theorem Execution.full_mark_of_open_endpoints {n θ route s u}
    (e : @Execution n cfg θ route s u) (i : Fin n) (p : Port)
    (ho : e.MarkExposed i p) (hs : s.x i (.m p) = cfg.auxThreshold)
    (hu : u.x i (.m p) = cfg.markExit) : e.ledger.mark i p = cfg.markDose := by
  rw [e.mark_charge_balance i p ho, hs, hu]; rfl


/-- Predicate on every continuous segment of the actual trace. -/
def Execution.AllFlows {n θ route s u}
    (P : ∀ {v w : Snapshot n}, Flow cfg θ v w → Prop) :
    @Execution n cfg θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => P f ∧ rest.AllFlows P
  | .cons (.jump _) rest => rest.AllFlows P

/-- Predicate on all actual boundary states of a finite execution. -/
def Execution.AllStates {n θ route s u} (P : Snapshot n → Prop) :
    @Execution n cfg θ route s u → Prop
  | .nil _ => P s
  | .cons _ rest => P s ∧ rest.AllStates P

/-- The exact affine invariant remains available on partial exposed ERROR traces. -/
theorem Execution.error_affine_invariant {n θ route s u}
    (e : @Execution n cfg θ route s u) (i : Fin n) (p : Port)
    (exposed : e.ErrorExposed i p) :
    u.x i (.z p) + cfg.gainFactor * u.x i (.m p) =
      s.x i (.z p) + cfg.gainFactor * s.x i (.m p) := by
  rw [e.gain_balance i p, e.error_charge_balance i p exposed]
  ring

theorem Jump.mark_entry_guard {n route s u} (j : @Jump n cfg route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p ≠ .mark) (hu : u.aux i p = .mark) : u.x i (.m p) = cfg.auxThreshold := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]
  all_goals (split_ifs at *; simp_all)

theorem Jump.mark_departure_guard {n route s u} (j : @Jump n cfg route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p = .mark) (hu : u.aux i p ≠ .mark) : s.x i (.m p) = cfg.markExit := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.silent_entry_guard {n route s u} (j : @Jump n cfg route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p ≠ .silent) (hu : u.aux i p = .silent) : u.x i (.m p) = cfg.markExit := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]
  all_goals (split_ifs at *; simp_all)

theorem Jump.silent_departure_guard {n route s u} (j : @Jump n cfg route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p = .silent) (hu : u.aux i p ≠ .silent) : s.x i (.m p) = cfg.errorLevel := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.error_entry_guard {n route s u} (j : @Jump n cfg route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p ≠ .error) (hu : u.aux i p = .error) : u.x i (.m p) = cfg.errorLevel := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]
  all_goals (split_ifs at *; simp_all)

theorem Jump.error_departure_guard {n route s u} (j : @Jump n cfg route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p = .error) (hu : u.aux i p ≠ .error) : s.x i (.m p) = cfg.auxRest := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem guarded_error_dose {n θ route before s u after}
    (entry : @Jump n cfg route before s) (e : @Execution n cfg θ route s u)
    (exit : Jump cfg route u after) (i : Fin n) (p : Port)
    (hbefore : before.aux i p ≠ .error) (hs : s.aux i p = .error)
    (hu : u.aux i p = .error) (hafter : after.aux i p ≠ .error)
    (ho : e.ErrorExposed i p) : e.ledger.error i p = cfg.errorDose :=
  e.full_error_of_open_endpoints i p ho (entry.error_entry_guard i p hbefore hs)
    (exit.error_departure_guard i p hu hafter)

theorem guarded_mark_dose {n θ route before s u after}
    (entry : @Jump n cfg route before s) (e : @Execution n cfg θ route s u)
    (exit : Jump cfg route u after) (i : Fin n) (p : Port)
    (hbefore : before.aux i p ≠ .mark) (hs : s.aux i p = .mark)
    (hu : u.aux i p = .mark) (hafter : after.aux i p ≠ .mark)
    (ho : e.MarkExposed i p) : e.ledger.mark i p = cfg.markDose :=
  e.full_mark_of_open_endpoints i p ho (entry.mark_entry_guard i p hbefore hs)
    (exit.mark_departure_guard i p hu hafter)


end KernelR.Family
