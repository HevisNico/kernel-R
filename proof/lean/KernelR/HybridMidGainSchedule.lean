import KernelR.HybridFirstFireSchedule
import KernelR.HybridPulseBounds

/-! The actual once-trained fast port has gain below 2.2. Its true response
still cannot fire through .4, retaining the real carried initial charge. -/
namespace KernelR.Hybrid
open Set

/-- This bound is tied to the current own log-gain, without replacing it by
an unperturbed nominal gain. -/
theorem fast_learned_gain_sharp_bounds {z : ℝ}
    (hl : Real.log (6 / 5) + 3 / 5 - 1 / 100000 ≤ z)
    (hu : z ≤ Real.log (6 / 5) + 3 / 5 + 1 / 100000) :
    9 / 5 ≤ Real.exp z ∧ Real.exp z ≤ 11 / 5 := by
  have hlow := (fast_learned_gain_bounds (z := z) (by linarith) (by linarith)).1
  have hsmall : Real.exp (601 / 1000 : ℝ) ≤ 11 / 6 := by
    have h := Real.exp_bound (x := (601 / 1000 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have hz : z ≤ Real.log (6 / 5) + (601 / 1000 : ℝ) := by linarith
  have h := Real.exp_le_exp.mpr hz
  rw [Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 6 / 5)] at h
  exact ⟨hlow,by linarith⟩

/-- A rational upper bound at the end of the early firing window. The leak
term is retained; the coarser total-raw-mass comparison is insufficient here. -/
theorem response_four_tenths_upper : response (2 / 5 : ℝ) ≤ 197 / 500 := by
  have hhead : Real.exp (-(1 / 5 : ℝ)) ≤ 41 / 50 := by
    have h := Real.exp_bound (x := -(1 / 5 : ℝ)) (n := 4) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have htail : (571 / 1000 : ℝ) ≤ Real.exp (-a * (2 / 5)) := by
    have hlo : (571 / 1000 : ℝ) ≤ Real.exp (-(14 / 25 : ℝ)) := by
      have h := Real.exp_bound (x := -(14 / 25 : ℝ)) (n := 6) (by norm_num) (by norm_num)
      norm_num [Finset.sum_range_succ] at h
      linarith [(abs_sub_le_iff.mp h).2]
    exact hlo.trans (Real.exp_le_exp.mpr (by nlinarith [a_coarse_bounds.2]))
  have ha : (69 / 50 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have hden : 0 < a - 1 / 2 := by linarith
  have hratio : a / (a - 1 / 2) ≤ (79 / 50 : ℝ) :=
    (div_le_iff₀ hden).mpr (by linarith)
  have hdiff : Real.exp (-(1 / 2 : ℝ) * (2 / 5)) - Real.exp (-a * (2 / 5)) ≤ 249 / 1000 := by
    norm_num only [show -(1 / 2 : ℝ) * (2 / 5) = -(1 / 5 : ℝ) by norm_num]
    linarith
  have hnon : 0 ≤ Real.exp (-(1 / 2 : ℝ) * (2 / 5)) - Real.exp (-a * (2 / 5)) := by
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hprod := mul_le_mul hratio hdiff hnon (by norm_num : (0 : ℝ) ≤ 79 / 50)
  change response (2 / 5 : ℝ) ≤ _ at hprod
  norm_num at hprod
  linarith

theorem readyPulse_mid_four_tenths_endpoint (start : ℝ) :
    readyPulse (7 / 50) (11 / 5) start (start + 2 / 5) ≤ 2499 / 2500 := by
  have hhead : Real.exp (-(1 / 5 : ℝ)) ≤ 41 / 50 := by
    have h := Real.exp_bound (x := -(1 / 5 : ℝ)) (n := 4) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  simp only [readyPulse,add_sub_cancel_left]
  norm_num only [show -(1 / 2 : ℝ) * (2 / 5) = -(1 / 5 : ℝ) by norm_num]
  linarith [response_four_tenths_upper]

/-- The actual response stays below threshold throughout the early window
for the sharp fast-port gain band, including every smaller carried charge. -/
theorem readyPulse_mid_four_tenths_margin {initial amplitude start t : ℝ}
    (hi : initial ≤ 7 / 50) (ha : amplitude ≤ 11 / 5)
    (ht : start ≤ t) (hu : t ≤ start + 2 / 5) :
    readyPulse initial amplitude start t ≤ 2499 / 2500 ∧
      readyPulse initial amplitude start t < 1 := by
  have hresponse := response_nonnegative (sub_nonneg.mpr ht)
  have hinit := readyPulse_mono_initial (amplitude := amplitude) (start := start) (t := t) hi
  have hgain := mul_le_mul_of_nonneg_right ha hresponse
  have henv : readyPulse initial amplitude start t ≤ readyPulse (7 / 50) (11 / 5) start t := by
    unfold readyPulse at hinit ⊢
    linarith
  have hmono : StrictMonoOn (readyPulse (7 / 50) (11 / 5) start) (Icc start (start + 9 / 10)) :=
    readyPulse_strictMono (by norm_num) (by norm_num)
  have hend := hmono.monotoneOn ⟨ht,by linarith⟩ ⟨by linarith,by linarith⟩ hu
  have hbound := henv.trans (hend.trans (readyPulse_mid_four_tenths_endpoint start))
  exact ⟨hbound,by linarith⟩

theorem readyPulse_mid_root_after_four_tenths {initial amplitude start t : ℝ}
    (hi : initial ≤ 7 / 50) (ha : amplitude ≤ 11 / 5) (ht : start ≤ t)
    (hroot : readyPulse initial amplitude start t = 1) : start + 2 / 5 < t := by
  by_contra hn
  have h := (readyPulse_mid_four_tenths_margin hi ha ht (le_of_not_gt hn)).2
  rw [hroot] at h
  exact (lt_irrefl _ h)

end KernelR.Hybrid
