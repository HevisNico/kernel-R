import KernelR.HybridReady
import KernelR.HybridBounds

/-! Coarse bounds on actual real pulse responses. These replace selected
numerical enclosure premises with direct real proofs. -/
namespace KernelR.Hybrid
open Set

theorem response_nonnegative {t : ℝ} (ht : 0 ≤ t) : 0 ≤ response t := by
  unfold response
  apply mul_nonneg (div_nonneg (by linarith [a_coarse_bounds.1]) (by linarith [a_coarse_bounds.1]))
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  nlinarith [a_coarse_bounds.1]

theorem response_upper {t : ℝ} (ht : 0 ≤ t) : response t ≤ a * t := by
  have hc : ContinuousOn response (Icc 0 t) :=
    fun x _ => (response_derivative x).continuousAt.continuousWithinAt
  apply image_le_of_deriv_right_le_deriv_boundary hc
    (fun x _ => (response_derivative x).hasDerivWithinAt) (B := fun x => a * x)
    (B' := fun _ => a) (by simp [response]) (by fun_prop)
    (fun x _ => by simpa using ((hasDerivAt_id x).const_mul a).hasDerivWithinAt (s := Ici x)) _ ⟨ht, le_rfl⟩
  intro x hx
  have he : Real.exp (-a * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [a_coarse_bounds.1, hx.1])
  nlinarith [response_nonnegative hx.1, a_coarse_bounds.1]

theorem exp_neg_a : Real.exp (-a) = (1 / 4 : ℝ) := by
  norm_num [a, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]

theorem response_le_raw_charge {t : ℝ} (ht : 0 ≤ t) : response t ≤ 1 - Real.exp (-a * t) := by
  have hc : ContinuousOn response (Icc 0 t) :=
    fun x _ => (response_derivative x).continuousAt.continuousWithinAt
  apply image_le_of_deriv_right_le_deriv_boundary hc
    (fun x _ => (response_derivative x).hasDerivWithinAt)
    (B := fun x => 1 - Real.exp (-a * x)) (B' := fun x => a * Real.exp (-a * x))
    (by simp [response]) (by fun_prop) _ _ ⟨ht, le_rfl⟩
  · intro x _
    exact ((((hasDerivAt_id x).const_mul (-a)).exp).const_sub 1).hasDerivWithinAt.congr_deriv (by dsimp; ring)
  · intro x hx
    linarith [response_nonnegative hx.1]

theorem response_raw_window_upper {t : ℝ} (ht : 0 ≤ t) (hu : t ≤ 1) : response t ≤ 3 / 4 := by
  have he : Real.exp (-a) ≤ Real.exp (-a * t) := Real.exp_le_exp.mpr (by nlinarith [a_coarse_bounds.1])
  rw [exp_neg_a] at he
  linarith [response_le_raw_charge ht]

theorem exp_head_lower : (5 / 8 : ℝ) ≤ Real.exp (-(9 / 20 : ℝ)) := by
  have h := Real.exp_bound (x := -(9 / 20 : ℝ)) (n := 4) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith [(abs_sub_le_iff.mp h).2]

theorem exp_head_tail_upper : Real.exp (-a * (9 / 10)) ≤ (303 / 1000 : ℝ) := by
  have h₁ : (271 / 100 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h₂ : (61 / 50 : ℝ) ≤ Real.exp (1 / 5) := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 5)
    norm_num at h
    exact h
  have hprod := mul_le_mul h₁ h₂ (by norm_num : (0 : ℝ) ≤ 61 / 50) (Real.exp_pos _).le
  rw [← Real.exp_add, show (1 : ℝ) + 1 / 5 = 6 / 5 by norm_num] at hprod
  have hsmall : Real.exp (-(6 / 5 : ℝ)) ≤ 303 / 1000 := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith
  apply le_trans _ hsmall
  apply Real.exp_le_exp.mpr
  dsimp [a]
  linarith [KernelR.log_four_bounds.1]

theorem response_emission_deadline : (5001 / 10000 : ℝ) ≤ response (9 / 10) := by
  have hd : 0 < a - 1 / 2 := by linarith [a_coarse_bounds.1]
  have hc : (14 / 9 : ℝ) ≤ a / (a - 1 / 2) :=
    (le_div_iff₀ hd).mpr (by linarith [a_coarse_bounds.2])
  have he : (161 / 500 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ) * (9 / 10)) - Real.exp (-a * (9 / 10)) := by
    rw [show -(1 / 2 : ℝ) * (9 / 10) = -(9 / 20) by norm_num]
    linarith [exp_head_lower, exp_head_tail_upper]
  have h := mul_le_mul hc he (by norm_num : (0 : ℝ) ≤ 161 / 500)
    (div_pos (by linarith [a_coarse_bounds.1]) hd).le
  change _ ≤ response (9 / 10) at h
  linarith

end KernelR.Hybrid
