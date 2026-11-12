import Training.StopLearningLatency

/-! Separate read windows for last increments up to 3/50. The existing
1/20 results and native execution constructors are unchanged. These
statements assume the ideal response and the stopped-training contract. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

private theorem wide_peak_lower : (55766 / 100000 : ℝ) ≤ response 1 := by
  have half : Real.exp (-(1 / 2 : ℝ)) ∈ Icc (606530 / 1000000 : ℝ) 1 :=
    exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
  unfold response
  rw [mul_one, mul_one, exp_neg_a]
  have product := mul_le_mul response_ratio_bounds.1
    (sub_le_sub_right half.1 (1 / 4)) (by norm_num)
    (by linarith [response_ratio_bounds.1] : 0 ≤ a / (a - 1 / 2))
  linarith

private theorem wide_pair_low : response (59 / 250) ≤ 26236 / 100000 := by
  have slow : Real.exp (-(1 / 2 : ℝ) * (59 / 250)) ≤ 888697 / 1000000 := by
    have h : Real.exp (-(59 / 500 : ℝ)) ∈ Icc (0 : ℝ) (888697 / 1000000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    convert h.2 using 2
    norm_num
  have fast : (720964 / 1000000 : ℝ) ≤ Real.exp (-a * (59 / 250)) := by
    have h : Real.exp (-(138629437 / 100000000 : ℝ) * (59 / 250)) ∈
        Icc (720964 / 1000000 : ℝ) 1 :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    exact h.1.trans (Real.exp_le_exp.mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.2]))
  have nonneg : 0 ≤ Real.exp (-(1 / 2 : ℝ) * (59 / 250)) - Real.exp (-a * (59 / 250)) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith [a_coarse_bounds.1]))
  unfold response
  have product := mul_le_mul response_ratio_bounds.2
    (show Real.exp (-(1 / 2 : ℝ) * (59 / 250)) - Real.exp (-a * (59 / 250)) ≤
      167733 / 1000000 by linarith) nonneg (by norm_num)
  linarith

theorem window_half_wide :
    response (59 / 250) ≤ (1 / 2) * Real.exp (-(3 / 50 : ℝ)) * response 1 ∧
    (1 / 2) * response 1 ≤ response (32 / 125) := by
  have step : Real.exp (-(3 / 50 : ℝ)) ∈ Icc (94176 / 100000 : ℝ) 1 :=
    exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
  have product := mul_le_mul step.1 wide_peak_lower (by norm_num) (Real.exp_pos _).le
  exact ⟨by nlinarith [wide_pair_low], window_half.2⟩

/-- A maximum last dose of 0.06 gives the ideal pair window (0.236, 0.256].
The measured cold dose fits the dose budget; the circuit latency near 0.267
is still outside this ideal window. -/
theorem stopped_pair_read_latency_wide {g₁ g₂ fire t : ℝ} (pos₁ : 0 < g₁) (pos₂ : 0 < g₂)
    (first : StoppedTraining g₁ 1 fire (3 / 50)) (second : StoppedTraining g₂ 1 fire (3 / 50))
    (read : FirstPulseReport (1 / 10) (g₁ + g₂) fire t) :
    t ∈ Ioc (59 / 250 : ℝ) (32 / 125) :=
  stopped_read_latency (by norm_num) (by linarith) (stopped_pair pos₁ pos₂ first second) read
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ window_half_wide.1 window_half_wide.2

theorem stopped_pair_read_skew_wide {g₁ g₂ h₁ h₂ fire fire' t t' : ℝ}
    (pos₁ : 0 < g₁) (pos₂ : 0 < g₂) (pos₃ : 0 < h₁) (pos₄ : 0 < h₂)
    (first : StoppedTraining g₁ 1 fire (3 / 50)) (second : StoppedTraining g₂ 1 fire (3 / 50))
    (third : StoppedTraining h₁ 1 fire' (3 / 50)) (fourth : StoppedTraining h₂ 1 fire' (3 / 50))
    (read : FirstPulseReport (1 / 10) (g₁ + g₂) fire t)
    (read' : FirstPulseReport (1 / 10) (h₁ + h₂) fire' t') :
    |t - t'| < 1 / 50 := by
  obtain ⟨lo, hi⟩ := stopped_pair_read_latency_wide pos₁ pos₂ first second read
  obtain ⟨lo', hi'⟩ := stopped_pair_read_latency_wide pos₃ pos₄ third fourth read'
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The wider pair window still separates offsets 0 and ±0.3 with the
existing 0.1 input stagger and 0.03 differential lag budgets. This is a
date-level consequence, not a construction of delayed circuit executions. -/
theorem wide_pair_dates_decide_lag {readL₁ readL₂ readR₁ readR₂ tfL tfR offset lagL lagR lag₀ : ℝ}
    (leftAfter : readL₁ + 59 / 250 < tfL) (leftBefore : tfL ≤ readL₂ + 32 / 125)
    (rightAfter : readR₁ + 59 / 250 < tfR) (rightBefore : tfR ≤ readR₂ + 32 / 125)
    (leftOrder : readL₁ ≤ readL₂ ∧ readL₂ ≤ readL₁ + 1 / 10)
    (rightOrder : readR₁ ≤ readR₂ ∧ readR₂ ≤ readR₁ + 1 / 10)
    (schedule : readR₁ = readL₁ + offset)
    (offsets : offset = -(3 / 10) ∨ offset = 0 ∨ offset = 3 / 10)
    (leftLag : lag₀ ≤ lagL ∧ lagL ≤ lag₀ + 3 / 100)
    (rightLag : lag₀ ≤ lagR ∧ lagR ≤ lag₀ + 3 / 100) :
    |(tfR + lagR) - (tfL + lagL)| < 3 / 20 ↔ offset = 0 := by
  constructor
  · intro close
    obtain ⟨lo, hi⟩ := abs_lt.mp close
    rcases offsets with h | h | h
    · exfalso; linarith
    · exact h
    · exfalso; linarith
  · intro zero
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

private theorem wide_peak_upper : response 1 ≤ (55767 / 100000 : ℝ) := by
  have half : Real.exp (-(1 / 2 : ℝ)) ∈ Icc (606530 / 1000000 : ℝ) (606531 / 1000000) :=
    exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
  unfold response
  rw [mul_one, mul_one, exp_neg_a]
  have product := mul_le_mul response_ratio_bounds.2
    (sub_le_sub_right half.2 (1 / 4)) (by linarith [half.1]) (by norm_num)
  linarith

private theorem wide_two_thirds_low : response (349 / 1000) ≤ 34952 / 100000 := by
  have slow : Real.exp (-(1 / 2 : ℝ) * (349 / 1000)) ≤ 839877 / 1000000 := by
    have h : Real.exp (-(349 / 2000 : ℝ)) ∈ Icc (0 : ℝ) (839877 / 1000000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    convert h.2 using 2
    norm_num
  have fast : (616426 / 1000000 : ℝ) ≤ Real.exp (-a * (349 / 1000)) := by
    have h : Real.exp (-(138629437 / 100000000 : ℝ) * (349 / 1000)) ∈
        Icc (616426 / 1000000 : ℝ) 1 :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    exact h.1.trans (Real.exp_le_exp.mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.2]))
  have nonneg : 0 ≤ Real.exp (-(1 / 2 : ℝ) * (349 / 1000)) - Real.exp (-a * (349 / 1000)) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith [a_coarse_bounds.1]))
  unfold response
  exact (mul_le_mul response_ratio_bounds.2 (show Real.exp (-(1 / 2 : ℝ) * (349 / 1000)) -
    Real.exp (-a * (349 / 1000)) ≤ 223451 / 1000000 by linarith)
    nonneg (by norm_num)).trans (by norm_num)

private theorem wide_two_thirds_high : (3729 / 10000 : ℝ) ≤ response (77 / 200) := by
  have slow : (82489 / 100000 : ℝ) ≤ Real.exp (-(1 / 2) * (77 / 200)) := by
    have h : Real.exp (-(77 / 400 : ℝ)) ∈ Icc (82489 / 100000 : ℝ) 1 :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    convert h.1 using 2
    norm_num
  have fast : Real.exp (-a * (77 / 200)) ≤ 58642 / 100000 := by
    have h : Real.exp (-(138629436 / 100000000 : ℝ) * (77 / 200)) ∈
        Icc (0 : ℝ) (58642 / 100000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    exact (Real.exp_le_exp.mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.1])).trans h.2
  have ratioNonneg : 0 ≤ a / (a - 1 / 2) :=
    (by norm_num : (0 : ℝ) ≤ 156414 / 100000).trans response_ratio_bounds.1
  unfold response
  exact (by norm_num : (3729 / 10000 : ℝ) ≤ (156414 / 100000) * (23847 / 100000)).trans
    (mul_le_mul response_ratio_bounds.1 (show (23847 / 100000 : ℝ) ≤
      Real.exp (-(1 / 2) * (77 / 200)) - Real.exp (-a * (77 / 200)) by linarith)
      (by norm_num) ratioNonneg)

theorem window_two_thirds_wide :
    response (349 / 1000) ≤ (2 / 3) * Real.exp (-(3 / 50 : ℝ)) * response 1 ∧
    (2 / 3) * response 1 ≤ response (77 / 200) := by
  have step : Real.exp (-(3 / 50 : ℝ)) ∈ Icc (94176 / 100000 : ℝ) 1 :=
    exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
  have product := mul_le_mul step.1 wide_peak_lower (by norm_num) (Real.exp_pos _).le
  exact ⟨by nlinarith [wide_two_thirds_low], by linarith [wide_peak_upper, wide_two_thirds_high]⟩

/-- With weakened training at 2/3 amplitude and a last dose at most 0.06,
the ideal single-port read window is (0.349, 0.385]. -/
theorem stopped_read_latency_two_thirds_wide {gain fire t : ℝ} (gainPos : 0 < gain)
    (stopped : StoppedTraining gain (2 / 3) fire (3 / 50))
    (read : FirstPulseReport (1 / 10) gain fire t) :
    t ∈ Ioc (349 / 1000 : ℝ) (77 / 200) :=
  stopped_read_latency (by norm_num) gainPos stopped read
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    window_two_thirds_wide.1 window_two_thirds_wide.2

theorem stopped_read_skew_two_thirds_wide {gain₁ gain₂ fire₁ fire₂ t₁ t₂ : ℝ}
    (pos₁ : 0 < gain₁) (pos₂ : 0 < gain₂)
    (stopped₁ : StoppedTraining gain₁ (2 / 3) fire₁ (3 / 50))
    (stopped₂ : StoppedTraining gain₂ (2 / 3) fire₂ (3 / 50))
    (read₁ : FirstPulseReport (1 / 10) gain₁ fire₁ t₁)
    (read₂ : FirstPulseReport (1 / 10) gain₂ fire₂ t₂) :
    |t₁ - t₂| < 9 / 250 := by
  obtain ⟨lo, hi⟩ := stopped_read_latency_two_thirds_wide pos₁ stopped₁ read₁
  obtain ⟨lo', hi'⟩ := stopped_read_latency_two_thirds_wide pos₂ stopped₂ read₂
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end RecursiveLearning.Native
