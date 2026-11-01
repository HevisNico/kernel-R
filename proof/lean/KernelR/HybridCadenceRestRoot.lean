import KernelR.HybridPreparedCalendar
/-! Direct real bounds on each device's own three-dose resting latency. -/
namespace KernelR.Hybrid
open Set

/-- This narrower gain interval is proved from the real exponential, without
assuming membership in the stored cadence certificate. -/
theorem cadence_rest_gain_bounds {z : ℝ}
    (hl : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ z)
    (hu : z ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000) :
    181 / 100 ≤ Real.exp z ∧ Real.exp z ≤ 1817 / 1000 := by
  have hlo : (181 / 30 : ℝ) ≤ Real.exp (9 / 5 - 1 / 100000) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 5 - 1 / 100000) 10
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hhalf : Real.exp (90001 / 100000 : ℝ) ≤ 2461 / 1000 := by
    have h := Real.exp_bound (x := (90001 / 100000 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have hhi : Real.exp (9 / 5 + 1 / 100000 : ℝ) ≤ (2461 / 1000 : ℝ) ^ 2 := by
    calc
      _ ≤ Real.exp ((90001 / 100000 : ℝ) + 90001 / 100000) :=
        Real.exp_le_exp.mpr (by norm_num)
      _ ≤ _ := by
        rw [Real.exp_add]
        nlinarith [(Real.exp_pos (90001 / 100000 : ℝ)).le]
  constructor
  · have h := Real.exp_le_exp.mpr hl
    rw [show Real.log (3 / 10) + 9 / 5 - 1 / 100000 =
      Real.log (3 / 10) + (9 / 5 - 1 / 100000) by ring,
      Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 3 / 10)] at h
    linarith
  · have h := Real.exp_le_exp.mpr hu
    rw [show Real.log (3 / 10) + 9 / 5 + 1 / 100000 =
      Real.log (3 / 10) + (9 / 5 + 1 / 100000) by ring,
      Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 3 / 10)] at h
    norm_num at hhi
    linarith

theorem response_at_sixty_five_upper : response (13 / 20) ≤ 99 / 200 := by
  have hden : 0 < a - 1 / 2 := by linarith [a_coarse_bounds.1]
  have hratio : a / (a - 1 / 2) ≤ (7821 / 5000 : ℝ) :=
    (div_le_iff₀ hden).mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.1])
  have he₁ : Real.exp (-(13 / 40 : ℝ)) ≤ 72253 / 100000 := by
    have h := Real.exp_bound (x := -(13 / 40 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have hexp : (40612 / 100000 : ℝ) ≤ Real.exp (-(9011 / 10000 : ℝ)) := by
    have h := Real.exp_bound (x := -(9011 / 10000 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have he₂ : (40612 / 100000 : ℝ) ≤ Real.exp (-a * (13 / 20)) := by
    apply hexp.trans
    apply Real.exp_le_exp.mpr
    dsimp [a]
    linarith [KernelR.log_four_bounds.2]
  have hdiff : Real.exp (-(13 / 40 : ℝ)) - Real.exp (-a * (13 / 20)) ≤ 31641 / 100000 := by
    linarith
  have hnon : 0 ≤ Real.exp (-(13 / 40 : ℝ)) - Real.exp (-a * (13 / 20)) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    linarith [a_coarse_bounds.1]
  have hp := mul_le_mul hratio hdiff hnon (by norm_num : (0 : ℝ) ≤ 7821 / 5000)
  unfold response
  rw [show -(1 / 2 : ℝ) * (13 / 20) = -(13 / 40) by norm_num]
  linarith

theorem response_at_sixty_six_lower : (199 / 400 : ℝ) ≤ response (33 / 50) := by
  have hden : 0 < a - 1 / 2 := by linarith [a_coarse_bounds.1]
  have hratio : (391 / 250 : ℝ) ≤ a / (a - 1 / 2) :=
    (le_div_iff₀ hden).mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.2])
  have he₁ : (71892 / 100000 : ℝ) ≤ Real.exp (-(33 / 100 : ℝ)) := by
    have h := Real.exp_bound (x := -(33 / 100 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have hexp : Real.exp (-(9149 / 10000 : ℝ)) ≤ 40056 / 100000 := by
    have h := Real.exp_bound (x := -(9149 / 10000 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have he₂ : Real.exp (-a * (33 / 50)) ≤ 40056 / 100000 := by
    apply le_trans ?_ hexp
    apply Real.exp_le_exp.mpr
    dsimp [a]
    linarith [KernelR.log_four_bounds.1]
  have hdiff : (31836 / 100000 : ℝ) ≤ Real.exp (-(33 / 100 : ℝ)) - Real.exp (-a * (33 / 50)) := by
    linarith
  have hp := mul_le_mul hratio hdiff (by norm_num : (0 : ℝ) ≤ 31836 / 100000)
    (div_pos (by linarith [a_coarse_bounds.1]) hden).le
  unfold response
  rw [show -(1 / 2 : ℝ) * (33 / 50) = -(33 / 100) by norm_num]
  linarith

/-- The resting response is strictly below threshold at .65 and strictly above
it at .66 for every own nominal-plus-three-dose gain in the declared band. -/
theorem cadence_rest_response_signs {z : ℝ}
    (hl : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ z)
    (hu : z ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000) :
    readyPulse (1 / 10) (Real.exp z) 0 (13 / 20) < 1 ∧
      1 < readyPulse (1 / 10) (Real.exp z) 0 (33 / 50) := by
  have hg := cadence_rest_gain_bounds hl hu
  constructor
  · have hp := mul_le_mul hg.2 response_at_sixty_five_upper
      (response_nonnegative (by norm_num : (0 : ℝ) ≤ 13 / 20))
      (by norm_num : (0 : ℝ) ≤ 1817 / 1000)
    simp only [readyPulse,sub_self,zero_mul,add_zero,sub_zero]
    linarith
  · have hp := mul_le_mul hg.1 response_at_sixty_six_lower
      (by norm_num : (0 : ℝ) ≤ 199 / 400) (Real.exp_pos z).le
    simp only [readyPulse,sub_self,zero_mul,add_zero,sub_zero]
    linarith

/-- This is the cell's own exact-rest reference. A first emitting input with
positive residual charge is not asserted to have this same latency. -/
theorem restLatency_three_doses_bounds {z : ℝ}
    (hl : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ z)
    (hu : z ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000) :
    13 / 20 < restLatency (Real.exp z) ∧ restLatency (Real.exp z) < 33 / 50 := by
  have hg' := cadence_rest_gain_bounds hl hu
  have hg : 9 / 5 ≤ Real.exp z ∧ Real.exp z ≤ 12 / 5 := ⟨by linarith [hg'.1],by linarith [hg'.2]⟩
  have hs := restLatency_spec hg
  have hm := (readyPulse_strictMono (initial := (1 / 10 : ℝ)) (amplitude := Real.exp z)
    (start := 0) (by norm_num) hg.1).monotoneOn
  have hmem : restLatency (Real.exp z) ∈ Icc 0 (0 + 9 / 10) :=
    ⟨by linarith [hs.1],by linarith [hs.2.1]⟩
  have hsign := cadence_rest_response_signs hl hu
  constructor
  · by_contra hn
    have h := hm hmem (by norm_num : (13 / 20 : ℝ) ∈ Icc 0 (0 + 9 / 10)) (le_of_not_gt hn)
    rw [hs.2.2] at h
    linarith [hsign.1]
  · by_contra hn
    have h := hm (by norm_num : (33 / 50 : ℝ) ∈ Icc 0 (0 + 9 / 10)) hmem (le_of_not_gt hn)
    rw [hs.2.2] at h
    linarith [hsign.2]

end KernelR.Hybrid
