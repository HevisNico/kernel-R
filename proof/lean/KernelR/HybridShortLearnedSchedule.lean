import KernelR.HybridFirstLearnedFireExistence
import KernelR.HybridPreparedSlowReturn
import KernelR.HybridPulseBounds

/-! Short physical firing and prepared return clocks for the true current
charge and gain. These bounds do not supply an execution or a pulse outcome. -/
namespace KernelR.Hybrid
open Set

/-- A conservative rational lower bound on the actual response at .7. -/
theorem response_seven_tenths_lower : (251 / 500 : ℝ) ≤ response (7 / 10) := by
  have hhead : (88 / 125 : ℝ) ≤ Real.exp (-(7 / 20 : ℝ)) := by
    have h := Real.exp_bound (x := -(7 / 20 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have htail : Real.exp (-a * (7 / 10)) ≤ (381 / 1000 : ℝ) := by
    have hupper : Real.exp (-(483 / 500 : ℝ)) ≤ 381 / 1000 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 483 / 500) 6
      norm_num [Finset.sum_range_succ] at h
      rw [Real.exp_neg,inv_eq_one_div]
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      linarith
    apply (Real.exp_le_exp.mpr ?_).trans hupper
    have ha : (69 / 50 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
    linarith
  have hden : 0 < a - 1 / 2 := by linarith [a_coarse_bounds.1]
  have hratio : (14 / 9 : ℝ) ≤ a / (a - 1 / 2) :=
    (le_div_iff₀ hden).mpr (by linarith [a_coarse_bounds.2])
  have hdiff : (323 / 1000 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ) * (7 / 10)) - Real.exp (-a * (7 / 10)) := by
    norm_num only [show -(1 / 2 : ℝ) * (7 / 10) = -(7 / 20 : ℝ) by norm_num]
    linarith
  have hprod := mul_le_mul hratio hdiff (by norm_num : (0 : ℝ) ≤ 323 / 1000)
    (div_nonneg (by linarith [a_coarse_bounds.1]) hden.le)
  change _ ≤ response (7 / 10 : ℝ) at hprod
  norm_num at hprod
  linarith

/-- Every current gain at least 1.8 has crossed by .7, even at the smallest
allowed READY residual charge. The gain and charge are not reset. -/
theorem readyPulse_learned_by_seven_tenths {initial amplitude start : ℝ}
    (hq : 1 / 10 - 1 / 100000 ≤ initial) (hg : 9 / 5 ≤ amplitude) :
    1 < readyPulse initial amplitude start (start + 7 / 10) := by
  have he : Real.exp (-(7 / 20 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hepos : 0 ≤ Real.exp (-(7 / 20 : ℝ)) := (Real.exp_pos _).le
  have hcarry := mul_le_mul_of_nonneg_right hq hepos
  have hrpos : 0 ≤ response (7 / 10 : ℝ) := response_nonnegative (by norm_num)
  have hgain := mul_le_mul_of_nonneg_right hg hrpos
  have hresponse := mul_le_mul_of_nonneg_left response_seven_tenths_lower (by norm_num : (0 : ℝ) ≤ 9 / 5)
  simp only [readyPulse,add_sub_cancel_left]
  norm_num only [show -(1 / 2 : ℝ) * (7 / 10) = -(7 / 20 : ℝ) by norm_num]
  nlinarith

/-- The stronger deadline follows from the actual threshold root and strict
monotonicity on its existing firing bracket. -/
theorem FirstLearnedFire.deadline_seven_tenths {n θ route s i p}
    (c : @FirstLearnedFire n θ route s i p)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 7 / 50)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 11 / 5) :
    c.latency < 7 / 10 := by
  by_contra hn
  have hlate : (7 / 10 : ℝ) ≤ c.latency := le_of_not_gt hn
  have hm := (readyPulse_strictMono (start := s.time) hq.2 hg.1).monotoneOn
    (show s.time + 7 / 10 ∈ Icc s.time (s.time + 9 / 10) by constructor <;> linarith)
    (show s.time + c.latency ∈ Icc s.time (s.time + 9 / 10) by constructor <;> linarith [c.early,c.deadline])
    (show s.time + 7 / 10 ≤ s.time + c.latency by linarith)
  rw [c.response_root] at hm
  exact not_lt_of_ge hm (readyPulse_learned_by_seven_tenths hq.1 hg.1)

theorem FirstLearnedFire.date_lt_seven_tenths {n θ route s i p}
    (c : @FirstLearnedFire n θ route s i p)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 7 / 50)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 11 / 5) :
    c.final.time < s.time + 7 / 10 := by
  rw [c.date]
  linarith [c.deadline_seven_tenths hq hg]

theorem prepared_slow_log_duration_lt_fiftyone_tenths {b : ℝ}
    (hb : 17999 / 100000 ≤ b) : Real.log (5 / 2 : ℝ) / b < 51 / 10 := by
  have hbpos : 0 < b := by linarith
  apply (div_lt_iff₀ hbpos).mpr
  linarith [KernelR.log_recovery_bounds.2]

theorem preparedSlowDuration_lt_fiftyone_tenths {n} (s : Snapshot n) (i : Fin n)
    (hq : s.x i .q = 1 / 4)
    (hb : 17999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 18001 / 100000) :
    slowReopenDuration s i < 51 / 10 := by
  have hform : slowReopenDuration s i = Real.log (5 / 2 : ℝ) / s.x i .b := by
    norm_num [slowReopenDuration,hq]
  rw [hform]
  exact prepared_slow_log_duration_lt_fiftyone_tenths hb.1

/-- This is the own-recovery main return clock, to be used when constructing
its actual guarded return. No later READY state is postulated here. -/
theorem FirstLearnedFire.prepared_return_clock_lt_sixtyeight_tenths {n θ route s i p}
    (c : @FirstLearnedFire n θ route s i p)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 7 / 50)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 11 / 5)
    {b : ℝ} (hb : 17999 / 100000 ≤ b) :
    c.final.time + 1 + Real.log (5 / 2 : ℝ) / b < s.time + 34 / 5 := by
  rw [c.date]
  linarith [c.deadline_seven_tenths hq hg,prepared_slow_log_duration_lt_fiftyone_tenths hb]

end KernelR.Hybrid
