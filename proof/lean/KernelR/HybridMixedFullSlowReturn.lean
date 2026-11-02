import KernelR.HybridSlowMarkReturn

namespace KernelR.Hybrid
open Set

structure MixedFullSlowReturn {n θ route s u i p} {e : @Execution n θ route s u}
    (pulse : ShortMarkPulse e i p) extends ShortMarkReturn pulse where
  after_forty_three : s.time + 43 / 100 < returnPhase.afterReturn.time
  before_deadline : returnPhase.afterReturn.time < s.time + 99 / 100

/-- These deliberately broad local state bands suffice for the first mixed
case in all three cells; no previous firing date or cadence word is required. -/
theorem ShortMarkPulse.mixed_full_slow_return {n θ ε route s u i p}
    {e : @Execution n θ route s u} (pulse : ShortMarkPulse e i p)
    (hb : PhysicalBox θ ε) (hv : RawValid s)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (hq : 59 / 500 ≤ s.x i .q ∧ s.x i .q ≤ 71 / 500)
    (hbRange : 27999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 28001 / 100000) :
    Nonempty (MixedFullSlowReturn pulse) := by
  have hf := pulse.mark_head_facts hb hv ha hr ho hno
  have hB : 0 < s.x i .b + 1 / 10 := by linarith [hbRange.1]
  have hqin : 0 < s.x i .q := by linarith [hq.1]
  have hsol := pulse.cycle.markHead.slow_solution i
    (pulse.cycle.markHead.allStates_main_flows i .slow hf.1)
  have hImax := pulse.cycle.markHead.accumulatedRecovery_upper i (by linarith [hbRange.2])
  have hIbound : pulse.cycle.markHead.accumulatedRecovery i ≤ 11 / 200 := by
    linarith [pulse.cycle.mark_ends_early hb]
  have hIpos := pulse.cycle.markHead.accumulatedRecovery_nonnegative hb i (by linarith [hbRange.1])
  have hqmark : 1 / 10 < pulse.cycle.phases.markPhase.afterExit.x i .q := by
    have he := Real.add_one_le_exp (-pulse.cycle.markHead.accumulatedRecovery i)
    have hp := mul_le_mul_of_nonneg_right hq.1
      (Real.exp_pos (-pulse.cycle.markHead.accumulatedRecovery i)).le
    rw [← hsol] at hp
    nlinarith
  have hqmarkUpper : pulse.cycle.phases.markPhase.afterExit.x i .q ≤ 71 / 500 := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hIpos)
    have hp := mul_le_mul_of_nonneg_left he hqin.le
    rw [← hsol] at hp
    nlinarith [hq.2]
  have hlogUpper : Real.log (71 / 50 : ℝ) < 177 / 500 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 177 / 500) 4
    norm_num [Finset.sum_range_succ] at hh ⊢
    linarith
  have hlogMark : Real.log (pulse.cycle.phases.markPhase.afterExit.x i .q / (1 / 10)) < 177 / 500 := by
    apply lt_of_le_of_lt (Real.log_le_log (by positivity) (show
      pulse.cycle.phases.markPhase.afterExit.x i .q / (1 / 10) ≤ (71 / 50 : ℝ) by linarith)) hlogUpper
  have hquot : Real.log (pulse.cycle.phases.markPhase.afterExit.x i .q / (1 / 10)) /
      (s.x i .b + 1 / 10) < 94 / 100 := by
    apply (div_lt_iff₀ hB).2
    nlinarith [hbRange.1]
  have hdelay := pulse.mark_return_delay hb hv ha hr ho hno hB hqin (by linarith)
  have hdate : (Real.log (s.x i .q / (1 / 10)) +
      Cadence.markDeficit (pulse.cycle.trigger.afterMark.time - s.time) ((θ i).lm p)) /
        (s.x i .b + 1 / 10) < 99 / 100 := by
    linarith [pulse.cycle.mark_ends_early hb]
  obtain ⟨ret⟩ := pulse.slow_return_before_error hb hv ha hr ho hno hB hqmark hdate
  have hJ : 0 ≤ Cadence.markDeficit (pulse.cycle.trigger.afterMark.time - s.time) ((θ i).lm p) := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
    have hd : 0 ≤ ((1 / 10 : ℝ) - (2 / 5) * Real.log (5 / 4)) / (θ i).lm p := by
      apply div_nonneg _ (hb.rates_positive i p).1.le
      linarith
    dsimp [Cadence.markDeficit]
    linarith [pulse.cycle.trigger.early]
  have hlogLower : (18 / 109 : ℝ) ≤ Real.log (59 / 50 : ℝ) := by
    have hh := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 50)
    norm_num at hh ⊢
    exact hh
  have hlogInput : (18 / 109 : ℝ) ≤ Real.log (s.x i .q / (1 / 10)) := by
    apply hlogLower.trans (Real.log_le_log (by norm_num) ?_)
    linarith [hq.1]
  have hhalf : s.time + 43 / 100 < ret.returnPhase.afterReturn.time := by
    by_contra hn
    have hfrac : (Real.log (s.x i .q / (1 / 10)) +
        Cadence.markDeficit (pulse.cycle.trigger.afterMark.time - s.time) ((θ i).lm p)) /
          (s.x i .b + 1 / 10) ≤ 43 / 100 := by
      linarith [ret.date]
    have hh := (div_le_iff₀ hB).mp hfrac
    linarith [hbRange.2]
  exact ⟨⟨ret,hhalf,by linarith [ret.date]⟩⟩

end KernelR.Hybrid
