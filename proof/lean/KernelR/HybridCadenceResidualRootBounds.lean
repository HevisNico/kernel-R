import KernelR.HybridCadenceStrongPulse
import KernelR.HybridMidLearnedFire

/-! A genuine first strong cadence response may carry charge up to0.3.
Its own three-dose gain still places its first threshold strictly after0.4. -/
namespace KernelR.Hybrid
open Set

private theorem cadence_residual_exp_head : Real.exp (-(1 / 5 : ℝ)) ≤ 819 / 1000 := by
  have h := Real.exp_bound (x := -(1 / 5 : ℝ)) (n := 4) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith [(abs_sub_le_iff.mp h).1]

private theorem cadence_residual_exp_tail {time : ℝ} (ht : 0 ≤ time) (hu : time ≤ 2 / 5) :
    (573 / 1000 : ℝ) ≤ Real.exp (-a * time) := by
  have he : (573 / 1000 : ℝ) ≤ Real.exp (-(139 / 250 : ℝ)) := by
    have h := Real.exp_bound (x := -(139 / 250 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  apply he.trans
  apply Real.exp_le_exp.mpr
  have ha : a ≤ (139 / 100 : ℝ) := by dsimp [a]; linarith [KernelR.log_four_bounds.2]
  nlinarith

theorem response_cadence_four_tenths_upper : response (2 / 5 : ℝ) ≤ 19311 / 50000 := by
  have ha : (69 / 50 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have hd : 0 < a - 1 / 2 := by linarith
  have hr : a / (a - 1 / 2) ≤ (157 / 100 : ℝ) := (div_le_iff₀ hd).mpr (by linarith)
  have ht := cadence_residual_exp_tail (by norm_num : (0 : ℝ) ≤ 2 / 5) le_rfl
  have hdiff : Real.exp (-(1 / 2 : ℝ) * (2 / 5)) - Real.exp (-a * (2 / 5)) ≤ 123 / 500 := by
    norm_num only [show -(1 / 2 : ℝ) * (2 / 5) = -(1 / 5 : ℝ) by norm_num]
    linarith [cadence_residual_exp_head]
  have hnon : 0 ≤ Real.exp (-(1 / 2 : ℝ) * (2 / 5)) - Real.exp (-a * (2 / 5)) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hp := mul_le_mul hr hdiff hnon (by norm_num : (0 : ℝ) ≤ 157 / 100)
  change response (2 / 5 : ℝ) ≤ _ at hp
  norm_num at hp
  exact hp

theorem readyPulse_cadence_residual_four_tenths_endpoint (start : ℝ) :
    readyPulse (3 / 10) (19 / 10) start (start + 2 / 5) ≤ 499 / 500 := by
  simp only [readyPulse,add_sub_cancel_left]
  norm_num only [show -(1 / 2 : ℝ) * (2 / 5) = -(1 / 5 : ℝ) by norm_num]
  linarith [cadence_residual_exp_head,response_cadence_four_tenths_upper]

private theorem cadence_residual_envelope_strictMono (start : ℝ) :
    StrictMonoOn (readyPulse (3 / 10) (19 / 10) start) (Icc start (start + 2 / 5)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun time _ => (readyPulse_derivative (3 / 10) (19 / 10) start time).continuousAt.continuousWithinAt)
  intro time ht
  have hcc := interior_subset ht
  have htime : 0 ≤ time - start := sub_nonneg.mpr hcc.1
  have hu : time - start ≤ 2 / 5 := by linarith [hcc.2]
  have he : Real.exp (-(1 / 2 : ℝ) * (time - start)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hbound : readyPulse (3 / 10) (19 / 10) start time ≤ 379 / 250 := by
    unfold readyPulse
    linarith [response_uniform_upper htime]
  have ha : (69 / 50 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have hp := mul_le_mul ha (cadence_residual_exp_tail htime hu)
    (by norm_num : (0 : ℝ) ≤ 573 / 1000) (by linarith : 0 ≤ a)
  rw [(readyPulse_derivative (3 / 10) (19 / 10) start time).deriv]
  nlinarith

theorem readyPulse_cadence_residual_four_tenths_margin {initial amplitude start time : ℝ}
    (hi : initial ≤ 3 / 10) (ha : amplitude ≤ 19 / 10)
    (ht : start ≤ time) (hu : time ≤ start + 2 / 5) :
    readyPulse initial amplitude start time ≤ 499 / 500 ∧
      readyPulse initial amplitude start time < 1 := by
  have hinit := readyPulse_mono_initial (amplitude := amplitude) (start := start) (t := time) hi
  have hg := mul_le_mul_of_nonneg_right ha (response_nonnegative (sub_nonneg.mpr ht))
  have henv : readyPulse initial amplitude start time ≤ readyPulse (3 / 10) (19 / 10) start time := by
    unfold readyPulse at hinit ⊢
    linarith
  have hm := (cadence_residual_envelope_strictMono start).monotoneOn
    ⟨ht,hu⟩ ⟨by linarith,le_rfl⟩ hu
  have hbound := henv.trans (hm.trans (readyPulse_cadence_residual_four_tenths_endpoint start))
  exact ⟨hbound,by linarith⟩

theorem readyPulse_cadence_residual_root_after_four_tenths {initial amplitude start time : ℝ}
    (hi : initial ≤ 3 / 10) (ha : amplitude ≤ 19 / 10) (ht : start ≤ time)
    (hroot : readyPulse initial amplitude start time = 1) : start + 2 / 5 < time := by
  by_contra hn
  have h := (readyPulse_cadence_residual_four_tenths_margin hi ha ht (le_of_not_gt hn)).2
  rw [hroot] at h
  exact lt_irrefl _ h

/-- Construct the first actual scalar response root and its strict preceding
guard. The carried charge is retained, and no execution or date is supplied. -/
theorem readyPulse_cadence_residual_first_crossing {initial amplitude start : ℝ}
    (hq : 1 / 10 - 1 / 100000 ≤ initial ∧ initial ≤ 3 / 10)
    (hg : 9 / 5 ≤ amplitude ∧ amplitude ≤ 19 / 10) :
    ∃ latency : ℝ, 2 / 5 < latency ∧ latency < 9 / 10 ∧
      readyPulse initial amplitude start (start + latency) = 1 ∧
      ∀ time ∈ Ico start (start + latency), readyPulse initial amplitude start time < 1 := by
  have hc : Continuous (fun time : ℝ => readyPulse initial amplitude start (start + time)) := by
    unfold readyPulse response
    fun_prop
  obtain ⟨latency,hpos,hend,hroot,hprior⟩ := scalar_first_one_crossing hc
    (by norm_num : (0 : ℝ) < 9 / 10)
    (by rw [add_zero,readyPulse_initial]; linarith [hq.2])
    (readyPulse_emission_by_deadline hq.1 hg.1)
  have hl := readyPulse_cadence_residual_root_after_four_tenths hq.2 hg.2
    (by linarith : start ≤ start + latency) hroot
  refine ⟨latency,by linarith,hend,hroot,?_⟩
  intro time ht
  have h := hprior (time - start) ⟨by linarith [ht.1],by linarith [ht.2]⟩
  simpa only [show start + (time - start) = time by ring] using h

/-- This main contact has positive derivative under the same response bounds. -/
theorem readyPulse_cadence_residual_first_crossing_transversal {initial amplitude start : ℝ}
    (hq : 1 / 10 - 1 / 100000 ≤ initial ∧ initial ≤ 3 / 10)
    (hg : 9 / 5 ≤ amplitude ∧ amplitude ≤ 19 / 10) :
    ∃ latency : ℝ, 2 / 5 < latency ∧ latency < 9 / 10 ∧
      readyPulse initial amplitude start (start + latency) = 1 ∧
      (∀ t ∈ Ico start (start + latency), readyPulse initial amplitude start t < 1) ∧
      0 < deriv (readyPulse initial amplitude start) (start + latency) := by
  obtain ⟨latency, early, deadline, root, prior⟩ :=
    readyPulse_cadence_residual_first_crossing hq hg (start := start)
  refine ⟨latency, early, deadline, root, prior, ?_⟩
  apply readyPulse_transversal_of_later_value (by linarith [hg.1] : 0 ≤ amplitude)
    (show start + latency < start + 9 / 10 by linarith)
  rw [root]
  exact readyPulse_emission_by_deadline hq.1 hg.1

#print axioms readyPulse_cadence_residual_first_crossing_transversal

end KernelR.Hybrid
