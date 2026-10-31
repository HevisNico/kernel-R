import KernelR.HybridSensor

/-! Direct real bounds for silent and learned main-cell pulse responses. -/
namespace KernelR.Hybrid
open Set MeasureTheory


theorem response_global_upper {t : ℝ} (ht : 0 ≤ t) : response t ≤ 3 / 4 := by
  by_cases hshort : t ≤ 1
  · exact response_raw_window_upper ht hshort
  · have hc : ContinuousOn response (Icc 1 t) :=
      fun x _ => (response_derivative x).continuousAt.continuousWithinAt
    apply image_le_of_deriv_right_lt_deriv_boundary' hc
      (fun x _ => (response_derivative x).hasDerivWithinAt)
      (B := fun _ => 3 / 4) (B' := fun _ => 0)
      (response_raw_window_upper (by norm_num) le_rfl) continuousOn_const
      (fun x _ => hasDerivWithinAt_const x _ _) _ ⟨le_of_not_ge hshort, le_rfl⟩
    intro x hx hboundary
    have he : Real.exp (-a * x) ≤ 1 / 4 := by
      rw [← exp_neg_a]
      apply Real.exp_le_exp.mpr
      nlinarith [a_coarse_bounds.1, hx.1]
    rw [hboundary]
    nlinarith [a_coarse_bounds.1, a_coarse_bounds.2]

theorem readyPulse_silent_window {initial amplitude start t : ℝ}
    (hi : initial ≤ 3 / 25) (ha : amplitude ≤ 7 / 6) (ht : start ≤ t) :
    readyPulse initial amplitude start t < 1 := by
  have hd : 0 ≤ t - start := sub_nonneg.mpr ht
  have hcarry := decay_upper (show initial - 1 / 10 ≤ (1 / 50 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hu := mul_le_mul_of_nonneg_left (response_global_upper hd) (by norm_num : (0 : ℝ) ≤ 7 / 6)
  unfold readyPulse
  linarith

theorem readyPulse_emission_not_early {initial amplitude start t : ℝ}
    (hi : initial ≤ 7 / 50) (ha : amplitude ≤ 2)
    (ht : start ≤ t) (hu : t ≤ start + 3 / 10) : readyPulse initial amplitude start t < 1 := by
  have hd : 0 ≤ t - start := sub_nonneg.mpr ht
  have hc := decay_upper (show initial - 1 / 10 ≤ (1 / 25 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hh := mul_le_mul_of_nonneg_left (response_upper hd) (by norm_num : (0 : ℝ) ≤ 2)
  have htime := mul_le_mul_of_nonneg_left (show t - start ≤ (3 / 10 : ℝ) by linarith)
    (show 0 ≤ 2 * a by linarith [a_coarse_bounds.1])
  unfold readyPulse
  nlinarith [a_coarse_bounds.2]

theorem readyPulse_emission_by_deadline {initial amplitude start : ℝ}
    (hi : 1 / 10 - 1 / 100000 ≤ initial) (ha : 9 / 5 ≤ amplitude) :
    1 < readyPulse initial amplitude start (start + 9 / 10) := by
  have he : Real.exp (-(1 / 2 : ℝ) * (9 / 10)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hcarry : -(1 / 100000 : ℝ) ≤ (initial - 1 / 10) * Real.exp (-(1 / 2) * (9 / 10)) := by
    have h := mul_le_mul_of_nonneg_right (show -(1 / 100000 : ℝ) ≤ initial - 1 / 10 by linarith)
      (Real.exp_pos (-(1 / 2 : ℝ) * (9 / 10))).le
    nlinarith
  have hp := mul_le_mul_of_nonneg_left response_emission_deadline (show 0 ≤ amplitude by linarith)
  simp only [readyPulse, add_sub_cancel_left]
  nlinarith

theorem low_gain_tail_upper {z : ℝ} (hz : z ≤ Real.log (3 / 10) + 13 / 10) :
    Real.exp z ≤ 7 / 6 := by
  have hgap : (2 / 25 : ℝ) ≤ a - 13 / 10 := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have hprod : Real.exp (13 / 10 : ℝ) * Real.exp (a - 13 / 10) = 4 := by
    rw [← Real.exp_add]; norm_num [a, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  have hexp : (27 / 25 : ℝ) ≤ Real.exp (a - 13 / 10) := by linarith [Real.add_one_le_exp (a - 13 / 10)]
  have hu : Real.exp (13 / 10 : ℝ) ≤ 35 / 9 := by nlinarith [Real.exp_pos (13 / 10 : ℝ)]
  calc
    Real.exp z ≤ Real.exp (Real.log (3 / 10) + 13 / 10) := Real.exp_le_exp.mpr hz
    _ = (3 / 10 : ℝ) * Real.exp (13 / 10) := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 10)]
    _ ≤ 7 / 6 := by linarith
theorem learned_gain_bounds {z : ℝ}
    (hl : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ z)
    (hu : z ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000) :
    9 / 5 ≤ Real.exp z ∧ Real.exp z ≤ 2 := by
  have hlo : (6 : ℝ) ≤ Real.exp (9 / 5 - 1 / 100000) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 5 - 1 / 100000) 8
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hsmall : Real.exp (21 / 50 : ℝ) ≤ 5 / 3 := by
    have h := Real.exp_bound (x := (21 / 50 : ℝ)) (n := 2) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have hupper : Real.exp (9 / 5 + 1 / 100000 : ℝ) ≤ 20 / 3 := by
    calc
      _ ≤ Real.exp (a + 21 / 50) := Real.exp_le_exp.mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.1])
      _ = 4 * Real.exp (21 / 50) := by rw [Real.exp_add]; norm_num [a, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      _ ≤ _ := by linarith
  constructor
  · have h := Real.exp_le_exp.mpr hl
    rw [show Real.log (3 / 10) + 9 / 5 - 1 / 100000 = Real.log (3 / 10) + (9 / 5 - 1 / 100000) by ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 10)] at h
    linarith
  · have h := Real.exp_le_exp.mpr hu
    rw [show Real.log (3 / 10) + 9 / 5 + 1 / 100000 = Real.log (3 / 10) + (9 / 5 + 1 / 100000) by ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 10)] at h
    linarith

end KernelR.Hybrid
