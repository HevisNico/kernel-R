import KernelR.HybridResponseBounds
import KernelR.HybridPulseSpans
import KernelR.HybridAuxCycle

/-! Actual sensor triggering from a received canonical pulse. The coarse real
bounds below are proved directly, without stored interval-enclosure premises. -/
namespace KernelR.Hybrid
open Set

theorem PhysicalBox.input_gain_lower {n θ ε} (hb : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    (31 : ℝ) ≤ (θ i).inputGain p := by
  have hr : 0 < response (1 / 50) := lt_of_lt_of_le (by norm_num) sensor_response_lower
  have hu : response (1 / 50) ≤ (7 / 250 : ℝ) :=
    (response_upper (by norm_num)).trans (by linarith [a_coarse_bounds.2])
  have hn : (975 / 28 : ℝ) ≤ (1 - 1 / 40) / response (1 / 50) :=
    (le_div_iff₀ hr).mpr (by nlinarith)
  have he : 0 ≤ 1 - ε := by linarith [hb.epsilon_bounds.2]
  have hm := mul_le_mul_of_nonneg_right hn he
  have hl := (hb.2 i p).2.2.2.2.1
  nlinarith [hb.epsilon_bounds.2]

theorem response_sensor_deadline : (33 / 1000 : ℝ) ≤ response (1 / 40) := by
  have ha : (69 / 50 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have he : (193 / 200 : ℝ) ≤ Real.exp (-a * (1 / 40)) := by
    linarith [Real.add_one_le_exp (-a * (1 / 40)), a_coarse_bounds.2]
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ a * (1 / 40) by linarith)
  nlinarith [response_lower_bound (1 / 40)]

theorem auxPulse_above_at_deadline {initial amplitude start : ℝ}
    (hi : 1 / 40 - 1 / 100000 ≤ initial) (ha : 31 ≤ amplitude) :
    1 < auxPulse initial amplitude start (start + 1 / 40) := by
  have he : Real.exp (-(1 / 2 : ℝ) * (1 / 40)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hr : -(1 / 100000 : ℝ) ≤ (initial - 1 / 40) * Real.exp (-(1 / 2) * (1 / 40)) := by
    have h := mul_le_mul_of_nonneg_right (show -(1 / 100000 : ℝ) ≤ initial - 1 / 40 by linarith)
      (Real.exp_pos (-(1 / 2 : ℝ) * (1 / 40))).le
    nlinarith
  have hp := mul_le_mul_of_nonneg_left response_sensor_deadline (show 0 ≤ amplitude by linarith)
  rw [auxPulse_formula]
  norm_num only [add_sub_cancel_left] at *
  nlinarith

theorem auxPulse_below_before_early {initial amplitude start t : ℝ}
    (hi : initial ≤ 1 / 40 + 1 / 100000) (ha : amplitude ≤ 60)
    (ht : start ≤ t) (hu : t ≤ start + 1 / 100) : auxPulse initial amplitude start t < 1 := by
  have hd : 0 ≤ t - start := by linarith
  have hr := decay_upper (show initial - 1 / 40 ≤ (1 / 100000 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hh := mul_le_mul_of_nonneg_left (response_upper hd) (show (0 : ℝ) ≤ 60 by norm_num)
  have htime := mul_le_mul_of_nonneg_left (show t - start ≤ (1 / 100 : ℝ) by linarith)
    (show 0 ≤ 60 * a by linarith [a_coarse_bounds.1])
  rw [auxPulse_formula]
  nlinarith [a_coarse_bounds.2]

theorem auxUpper_le_one (mode : AuxMode) : auxUpper mode ≤ 1 := by
  cases mode <;> norm_num [auxUpper]

/-- A READY sensor span cannot reach 1/40 time units after a newly received pulse.
The proof cuts an existing flow at that date and contradicts its charge bound. -/
theorem Execution.aux_ready_no_overrun {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hr : s.raw i p = some s.time) (hm : e.AuxFlows i p .ready)
    (hx : 1 / 40 - 1 / 100000 ≤ s.x i (.m p)) : u.time < s.time + 1 / 40 := by
  by_contra h
  obtain ⟨v, cut, hp, hv⟩ := e.prefix_at (s.time + 1 / 40) (by linarith) (le_of_not_gt h)
  have hsol := cut.aux_ready_pulse_solution i p s.time hr (by rw [hv]; linarith) (hp.aux_flows i p .ready hm)
  have hbound := ((cut.upper_region hb hi i).2.2 p).trans (auxUpper_le_one _)
  have hcross := auxPulse_above_at_deadline hx (hb.input_gain_lower i p) (start := s.time)
  rw [hv] at hsol
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at hsol
  linarith

theorem Jump.ready_aux_departure {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p = .ready) (hu : u.aux i p ≠ .ready) :
    s.x i (.m p) = 1 ∧ u.aux i p = .mark := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

structure SensorTrigger {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) (p : Port) where
  beforeMark : Snapshot n
  afterMark : Snapshot n
  span : Execution θ route s beforeMark
  entry : Jump route beforeMark afterMark
  rest : Execution θ route afterMark u
  reconstruct : e = span.append (.cons (.jump entry) rest)
  flows : span.AuxFlows i p .ready
  ready_before : beforeMark.aux i p = .ready
  mark_after : afterMark.aux i p = .mark
  charge : afterMark.x i (.m p) = 1
  early : s.time + 1 / 100 < afterMark.time
  deadline : afterMark.time < s.time + 1 / 40

/-- Trigger existence and its physical bracket are derived from the raw pulse,
the fabrication family and the rest band, with no expected event supplied. -/
theorem Execution.sensor_trigger {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hs : s.aux i p = .ready) (hr : s.raw i p = some s.time)
    (hx : 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (ht : s.time + 1 / 40 ≤ u.time) : Nonempty (SensorTrigger e i p) := by
  rcases e.first_aux_change i p .ready hs with h | ⟨v, w, segment, entry, rest, he, hm, hv, hw⟩
  · exact False.elim (not_lt_of_ge ht (e.aux_ready_no_overrun hb hi i p hr h.2 hx.1))
  · have hguard := entry.ready_aux_departure i p hv hw
    have hlate := segment.aux_ready_no_overrun hb hi i p hr hm hx.1
    have hsol := segment.aux_ready_pulse_solution i p s.time hr (by linarith) hm
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at hsol
    have hearly : s.time + 1 / 100 < v.time := by
      by_contra h
      have hupper := auxPulse_below_before_early hx.2 (hb.coarse_upper i p).2.2.2.2
        segment.time_monotone (le_of_not_gt h)
      rw [← hsol, hguard.1] at hupper
      exact (lt_irrefl 1) hupper
    exact ⟨⟨v, w, segment, entry, rest, he, hm, hv, hguard.2,
      by rw [entry.physical_continuous, hguard.1],
      by rw [entry.time_unchanged]; exact hearly,
      by rw [entry.time_unchanged]; exact hlate⟩⟩

structure SensorCycle {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) (p : Port) where
  trigger : SensorTrigger e i p
  phases : AuxCycle trigger.rest i p
  error_starts_late : s.time + 99 / 100 < phases.silentPhase.afterExit.time
  ready_after_raw : s.time + 1 < phases.errorPhase.afterExit.time
  ready_deadline : phases.errorPhase.afterExit.time < s.time + 419 / 300

/-- A complete received-pulse sensor cycle, with a late ERROR start and READY
after the raw end but before the real 419/300 deadline. The actual trace is
selected from e; no recorded case, phase count or event date is assumed. -/
theorem Execution.sensor_cycle {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hs : s.aux i p = .ready) (hr : s.raw i p = some s.time)
    (hx : 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (ht : s.time + 419 / 300 ≤ u.time) : Nonempty (SensorCycle e i p) := by
  obtain ⟨trigger⟩ := e.sensor_trigger hb hi i p hs hr hx (by linarith)
  obtain ⟨phases⟩ := trigger.rest.aux_cycle_completion hb i p trigger.mark_after trigger.charge
    (by linarith [trigger.deadline, hb.aux_cycle_duration_upper i p])
  have hm : auxRemaining θ trigger.afterMark i p .mark = Real.log (5 / 4) / (θ i).lm p := by
    norm_num [auxRemaining, protectedFloor, auxRate, trigger.charge]
  have hs' : auxRemaining θ phases.markPhase.afterExit i p .silent = Real.log 8 / (θ i).ls p := by
    norm_num [auxRemaining, protectedFloor, auxRate, phases.markPhase.after_charge]
  have herr : phases.silentPhase.afterExit.time = trigger.afterMark.time +
      Real.log (5 / 4) / (θ i).lm p + Real.log 8 / (θ i).ls p := by
    rw [phases.silentPhase.after_time, phases.markPhase.after_time, hm, hs']
  refine ⟨⟨trigger, phases, ?_, ?_, ?_⟩⟩
  · rw [herr]
    rcases hb.aux_durations_lower i p with ⟨hm, hs, he⟩
    linarith [trigger.early]
  · rw [phases.completion_date]
    linarith [trigger.early, hb.aux_cycle_duration_lower i p]
  · rw [phases.completion_date]
    linarith [trigger.deadline, hb.aux_cycle_duration_upper i p]

end KernelR.Hybrid
