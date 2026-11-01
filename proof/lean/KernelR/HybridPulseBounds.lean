import KernelR.HybridPulseRoot

/-! Uniform real pulse bounds covering nominal low and fast gains. -/
namespace KernelR.Hybrid

theorem cubic_response_bound {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 ≤ 2 / 5 := by
  by_cases hu : x ≤ 2 / 5
  · nlinarith [pow_nonneg hx 3]
  · have hs := mul_nonneg (sq_nonneg (x - 3 / 5)) (show 0 ≤ x + 6 / 5 by linarith)
    nlinarith

theorem response_uniform_upper {t : ℝ} (ht : 0 ≤ t) : response t ≤ 16 / 25 := by
  have hcube : Real.exp (-(1 / 2 : ℝ) * t) ^ 3 = Real.exp (-(3 / 2 : ℝ) * t) := by
    rw [show -(3 / 2 : ℝ) * t = -(1 / 2) * t + -(1 / 2) * t + -(1 / 2) * t by ring,
      Real.exp_add,Real.exp_add]
    ring
  have hc := cubic_response_bound (Real.exp_pos (-(1 / 2 : ℝ) * t)).le
  rw [hcube] at hc
  have hex : Real.exp (-(3 / 2 : ℝ) * t) ≤ Real.exp (-a * t) :=
    Real.exp_le_exp.mpr (by nlinarith [a_coarse_bounds.2])
  have hi : Real.exp (-(1 / 2 : ℝ) * t) - Real.exp (-a * t) ≤ 2 / 5 := by linarith
  have hnon : 0 ≤ Real.exp (-(1 / 2 : ℝ) * t) - Real.exp (-a * t) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [a_coarse_bounds.1]))
  have hd : 0 < a - 1 / 2 := by linarith [a_coarse_bounds.1]
  have ha : (4 / 3 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have hratio : a / (a - 1 / 2) ≤ 8 / 5 := (div_le_iff₀ hd).mpr (by linarith)
  have h := mul_le_mul hratio hi hnon (by norm_num : (0 : ℝ) ≤ 8 / 5)
  change response t ≤ _ at h
  norm_num at h
  exact h

theorem readyPulse_nominal_silent {initial amplitude start t : ℝ}
    (hi : initial ≤ 7 / 50) (ha : amplitude ≤ 4 / 3) (ht : start ≤ t) :
    readyPulse initial amplitude start t < 1 := by
  have hd := sub_nonneg.mpr ht
  have hc := decay_upper (show initial - 1 / 10 ≤ (1 / 25 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hu := mul_le_mul_of_nonneg_left (response_uniform_upper hd) (by norm_num : (0 : ℝ) ≤ 4 / 3)
  unfold readyPulse
  linarith

theorem fast_nominal_raw_gain_upper {z : ℝ}
    (hz : z ≤ Real.log (6 / 5) + 1 / 1000 + 11 / 125) : Real.exp z ≤ 4 / 3 := by
  have he : Real.exp (9 / 100 : ℝ) ≤ 10 / 9 := by
    have h := Real.exp_bound (x := (9 / 100 : ℝ)) (n := 2) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  calc
    Real.exp z ≤ Real.exp (Real.log (6 / 5) + 9 / 100) := Real.exp_le_exp.mpr (by linarith)
    _ = (6 / 5 : ℝ) * Real.exp (9 / 100) := by rw [Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 6 / 5)]
    _ ≤ _ := by linarith

theorem PhysicalBox.fast_nominal_headroom {n θ ε} (hb : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    Real.log (6 / 5) + 1 / 1000 + 3 / 5 < Real.log ((θ i).cap p) := by
  have hcap : (18 / 5 : ℝ) ≤ (θ i).cap p := by
    have h := (hb.2 i p).1.1
    linarith [hb.epsilon_bounds.2]
  have hc := Real.log_le_log (by norm_num : (0 : ℝ) < 18 / 5) hcap
  have hi : Real.log (18 / 5) - Real.log (6 / 5) = Real.log (3 : ℝ) := by
    rw [← Real.log_div (by norm_num : (18 / 5 : ℝ) ≠ 0) (by norm_num : (6 / 5 : ℝ) ≠ 0)]
    norm_num
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
  linarith [Real.log_two_gt_d9]

theorem response_mid_early_upper {t : ℝ} (ht : 0 ≤ t) (hu : t ≤ 3 / 10) : response t ≤ 7 / 20 := by
  have hs : (13 / 20 : ℝ) ≤ Real.exp (-(21 / 50 : ℝ)) := by
    have h := Real.exp_bound (x := -(21 / 50 : ℝ)) (n := 4) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have he : Real.exp (-(21 / 50 : ℝ)) ≤ Real.exp (-a * t) :=
    Real.exp_le_exp.mpr (by nlinarith [a_coarse_bounds.2])
  linarith [response_le_raw_charge ht]

theorem readyPulse_mid_gain_not_early {initial amplitude start t : ℝ}
    (hi : initial ≤ 7 / 50) (ha : amplitude ≤ 12 / 5)
    (ht : start ≤ t) (hu : t ≤ start + 3 / 10) : readyPulse initial amplitude start t < 1 := by
  have hd := sub_nonneg.mpr ht
  have hc := decay_upper (show initial - 1 / 10 ≤ (1 / 25 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hh := mul_le_mul_of_nonneg_left (response_mid_early_upper hd (by linarith)) (by norm_num : (0 : ℝ) ≤ 12 / 5)
  unfold readyPulse
  linarith

theorem fast_learned_gain_bounds {z : ℝ}
    (hl : Real.log (6 / 5) + 3 / 5 - 1 / 1000 ≤ z)
    (hu : z ≤ Real.log (6 / 5) + 3 / 5 + 1 / 1000) :
    9 / 5 ≤ Real.exp z ∧ Real.exp z ≤ 12 / 5 := by
  have hlo : (1599 / 1000 : ℝ) ≤ Real.exp (3 / 5 - 1 / 1000) := by
    linarith [Real.add_one_le_exp (3 / 5 - 1 / 1000 : ℝ)]
  have hupper : Real.exp (3 / 5 + 1 / 1000 : ℝ) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith [Real.log_two_gt_d9])
      _ = _ := Real.exp_log (by norm_num : (0 : ℝ) < 2)
  constructor
  · have h := Real.exp_le_exp.mpr hl
    rw [show Real.log (6 / 5) + 3 / 5 - 1 / 1000 = Real.log (6 / 5) + (3 / 5 - 1 / 1000) by ring,
      Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 6 / 5)] at h
    linarith
  · have h := Real.exp_le_exp.mpr hu
    rw [show Real.log (6 / 5) + 3 / 5 + 1 / 1000 = Real.log (6 / 5) + (3 / 5 + 1 / 1000) by ring,
      Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 6 / 5)] at h
    linarith

end KernelR.Hybrid
