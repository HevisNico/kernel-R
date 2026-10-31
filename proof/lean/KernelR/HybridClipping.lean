import KernelR.HybridWork

/-! Charge budgets with the actual actuator gates, including partial and clipped
doses. Strict headroom is a consequence of these budgets when it is available. -/
namespace KernelR.Hybrid
open MeasureTheory Set

theorem integral_nonpos_on {g : ℝ → ℝ} {s u : ℝ} (hsu : s ≤ u)
    (hg : ∀ t ∈ Icc s u, g t ≤ 0) : (∫ t in s..u, g t) ≤ 0 := by
  have h : 0 ≤ ∫ t in s..u, -g t := intervalIntegral.integral_nonneg hsu (fun t ht => neg_nonneg.mpr (hg t ht))
  rw [intervalIntegral.integral_neg] at h
  linarith

noncomputable def protectedFloor : AuxMode → ℝ
  | .ready => 0 | .mark => 4 / 5 | .silent => 1 / 10 | .error => 1 / 40

theorem Flow.protected_aux_floor {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (hm : s.aux i p ≠ .ready) :
    ∀ t ∈ Icc s.time u.time, protectedFloor (s.aux i p) ≤ f.path t i (.m p) := by
  have h := continuous_bound_from_Ico f.positive (f.continuous i (.m p)).neg (cap := -protectedFloor (s.aux i p)) (by
    intro t ht
    have hg := (f.guards t ht).2 i p
    cases ha : s.aux i p <;> simp_all [protectedFloor]
    all_goals linarith)
  intro t ht
  have hh : -f.path t i (.m p) ≤ -protectedFloor (s.aux i p) := h t ht
  linarith

theorem Execution.protected_aux_floor {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (mode : AuxMode) (hne : mode ≠ .ready)
    (hm : e.AuxFlows i p mode) (hi : protectedFloor mode ≤ s.x i (.m p)) :
    protectedFloor mode ≤ u.x i (.m p) := by
  induction e with
  | nil => exact hi
  | @cons s v u step rest ih =>
    cases step with
    | flow f =>
      apply ih hm.2
      have h := f.protected_aux_floor i p (by rw [hm.1]; exact hne) v.time ⟨f.positive.le, le_rfl⟩
      have hmode : s.aux i p = mode := hm.1
      simpa only [f.final, hmode] using h
    | jump j => exact ih hm (by simpa only [j.physical_continuous] using hi)

theorem Flow.error_act_upper {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hm : s.aux i p = .error)
    (t : ℝ) (ht : t ∈ Icc s.time u.time) :
    errorAct θ s (f.path t) i p ≤ 8 * (θ i).le p * f.path t i (.m p) := by
  unfold errorAct
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg (by norm_num) (hb.rates_positive i p).2.2.le)
      (f.protected_aux_positive i p (by simp [hm]) ht).le

/-- Closing either actuator gate can reduce ERROR dose but cannot create more
than eight times the actual lost auxiliary charge. -/
theorem Flow.error_gain_budget {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hm : s.aux i p = .error) :
    u.x i (.z p) + 8 * u.x i (.m p) ≤ s.x i (.z p) + 8 * s.x i (.m p) := by
  have hI : (∫ t in s.time..u.time,
      field θ s (f.path t) t i (.z p) + 8 * field θ s (f.path t) t i (.m p)) ≤ 0 := by
    apply integral_nonpos_on f.positive.le
    intro t ht
    have hu := f.error_act_upper hb i p hm t ht
    simp only [field, hm, reduceCtorEq, ite_false, auxDrain]
    linarith
  rw [intervalIntegral.integral_add (f.integrable i (.z p)) ((f.integrable i (.m p)).const_mul 8),
    intervalIntegral.integral_const_mul] at hI
  have hz := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i (.z p)
  have hx := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i (.m p)
  rw [f.final] at hz hx
  linarith

theorem Execution.error_gain_budget {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hm : e.AuxFlows i p .error) :
    u.x i (.z p) + 8 * u.x i (.m p) ≤ s.x i (.z p) + 8 * s.x i (.m p) := by
  induction e with
  | nil => exact le_rfl
  | cons step rest ih =>
    cases step with
    | flow f => exact (ih hm.2).trans (f.error_gain_budget hb i p hm.1)
    | jump j => simpa only [j.physical_continuous] using ih hm

theorem Flow.error_gain_budget_on {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hm : s.aux i p = .error) :
    ∀ t ∈ Icc s.time u.time,
      f.path t i (.z p) ≤ s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) := by
  intro t ht
  have hfloor := f.protected_aux_floor i p (by simp [hm]) t ht
  simp only [hm, protectedFloor] at hfloor
  rcases ht.1.eq_or_lt with heq | hlt
  · rw [← heq, f.initial]
    have hstart := f.protected_aux_floor i p (by simp [hm]) s.time ⟨le_rfl, f.positive.le⟩
    rw [f.initial, hm, protectedFloor] at hstart
    linarith
  · have h := (f.prefix hlt ht.2).error_gain_budget hb i p hm
    change f.path t i (.z p) + 8 * f.path t i (.m p) ≤ _ at h
    linarith

/-- Strict gain exposure is derived from actual remaining charge and a checked
headroom inequality. Positive reserve still comes from reachability. -/
theorem Flow.error_cap_open_of_headroom {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hm : s.aux i p = .error)
    (hh : s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p)) :
    ∀ t ∈ Icc s.time u.time, f.path t i (.z p) < Real.log ((θ i).cap p) :=
  fun t ht => (f.error_gain_budget_on hb i p hm t ht).trans_lt hh

/-- Real headroom for the low initial gain after at most 12/5 logarithmic gain
increase. This arithmetic fact does not assume or establish a dose count. -/
theorem PhysicalBox.low_gain_headroom {n θ ε} (hb : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    Real.log (3 / 10) + 1 / 100000 + 12 / 5 < Real.log ((θ i).cap p) := by
  have hc : (18 / 5 : ℝ) ≤ (θ i).cap p := by
    have h := (hb.2 i p).1.1
    linarith [hb.epsilon_bounds.2]
  have hlc := Real.log_le_log (by norm_num : (0 : ℝ) < 18 / 5) hc
  have hid : Real.log (18 / 5) - Real.log (3 / 10) = Real.log (12 : ℝ) := by
    rw [← Real.log_div (by norm_num : (18 / 5 : ℝ) ≠ 0) (by norm_num : (3 / 10 : ℝ) ≠ 0)]
    norm_num
  have h12 : Real.log (12 : ℝ) = 2 * Real.log 4 - Real.log (4 / 3) := by
    rw [show (12 : ℝ) = 4 ^ 2 / (4 / 3) by norm_num,
      Real.log_div (by norm_num : (4 ^ 2 : ℝ) ≠ 0) (by norm_num : (4 / 3 : ℝ) ≠ 0), Real.log_pow]
    norm_num
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
  linarith [KernelR.log_four_bounds.1]

theorem Flow.mark_act_upper {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hm : s.aux i p = .mark)
    (t : ℝ) (ht : t ∈ Icc s.time u.time) :
    markAct θ s (f.path t) i p ≤ (1 / 2) * (θ i).lm p * f.path t i (.m p) := by
  unfold markAct
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg (by norm_num) (hb.rates_positive i p).1.le)
      (f.protected_aux_positive i p (by simp [hm]) ht).le

/-- A per-port MARK contribution stays partial when a main or cap gate closes.
Other ports are still present in the global recovery balance. -/
theorem Flow.mark_charge_upper {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hm : s.aux i p = .mark) :
    f.ledger.mark i p ≤ (s.x i (.m p) - u.x i (.m p)) / 2 := by
  have hI : (∫ t in s.time..u.time,
      markAct θ s (f.path t) i p + (1 / 2) * field θ s (f.path t) t i (.m p)) ≤ 0 := by
    apply integral_nonpos_on f.positive.le
    intro t ht
    have hu := f.mark_act_upper hb i p hm t ht
    simp only [field, hm, reduceCtorEq, ite_false, auxDrain]
    linarith
  rw [intervalIntegral.integral_add (f.mark_integrable i p) ((f.integrable i (.m p)).const_mul (1 / 2)),
    intervalIntegral.integral_const_mul] at hI
  have hx := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i (.m p)
  rw [f.final] at hx
  change (∫ t in s.time..u.time, markAct θ s (f.path t) i p) ≤ _
  linarith

theorem Execution.mark_charge_upper {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hm : e.AuxFlows i p .mark) :
    e.ledger.mark i p ≤ (s.x i (.m p) - u.x i (.m p)) / 2 := by
  induction e with
  | nil => simp [ledger, Ledger.zero]
  | cons step rest ih =>
    cases step with
    | flow f =>
      have hf := f.mark_charge_upper hb i p hm.1
      have hr := ih hm.2
      simp only [ledger, Move.ledger, Ledger.add]
      linarith
    | jump j =>
      have hr := ih hm
      cases j <;> simpa only [ledger, Move.ledger, Ledger.add, Jump.ledger, Ledger.zero, zero_add, setMain, setAux, setRaw] using hr

end KernelR.Hybrid
