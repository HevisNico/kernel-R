import Coincidence.CoincidenceTiming

/-! The registered benchmark, “Comparators” (constant-current case):

> 2. **Constant-current timed write.** Start at the same ERROR entry.
>    Hold the write current constant for one shared duration D, with
>    a fixed per-device multiplier on current. The timer ends the write
>    independently of the sensor's return to READY. With all gates open,
>    the dose is I times D. Use I = 4 in log-gain units per unit time and
>    D = 0.15 for the nominally matched 0.6 dose. Allow a second comparator
>    to choose the best shared nominal current and
>    duration for the registered worst-case criterion. Require the timer
>    to finish by time 16 on all allowed devices. Keep cap contact in the
>    model and report whether it changes the outcome.

The reduced runner enforces silence during training and positive reserve.
Its effective gain under those conditions is the expression below.
The read uses the same `readyPulse` as the native R latency certificate.
-/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- Gain used by the reduced constant-current readout. The shared dose is
nominal current times duration. Only the cap can truncate an eligible write. -/
noncomputable def timedCurrentGain (dose multiplier cap : ℝ) : ℝ :=
  min cap ((6 / 5) * Real.exp (multiplier * dose))

/-- Exponentiating the capped log-gain update gives the gain in the
registered reduced readout. -/
theorem timedCurrentGain_from_capped_log {dose multiplier cap : ℝ} (capPos : 0 < cap) :
    Real.exp (min (Real.log cap) (Real.log (6 / 5) + multiplier * dose)) =
      timedCurrentGain dose multiplier cap := by
  have write : Real.exp (Real.log (6 / 5) + multiplier * dose) =
      (6 / 5) * Real.exp (multiplier * dose) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 6 / 5)]
  calc
    _ = min (Real.exp (Real.log cap)) (Real.exp (Real.log (6 / 5) + multiplier * dose)) :=
      Real.exp_monotone.map_min
    _ = _ := by rw [Real.exp_log capPos, write, timedCurrentGain]

/-- A report in the reduced read model with frozen gain while the pulse is
live. After the pulse the charge relaxes toward 0.1, below the FIRE guard. -/
structure FirstPulseReport (charge gain threshold latency : ℝ) : Prop where
  live : latency ∈ Icc (0 : ℝ) 1
  hit : readyPulse charge gain 0 latency = threshold
  first : ∀ t ∈ Ico (0 : ℝ) latency, readyPulse charge gain 0 t < threshold

private theorem response_mono_pulse : MonotoneOn response (Icc (0 : ℝ) 1) := by
  apply (show StrictMonoOn response (Icc (0 : ℝ) 1) from ?_).monotoneOn
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun v _ => (response_derivative v).continuousAt.continuousWithinAt)
  intro v hv
  have ht := interior_subset hv
  rw [(response_derivative v).deriv]
  have alo : (69 / 50 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have tail : (1 / 4 : ℝ) ≤ Real.exp (-a * v) := by
    rw [← exp_neg_a]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (show 0 ≤ a by linarith) (sub_nonneg.mpr ht.2)])
  linarith [mul_le_mul alo tail (by norm_num) (by linarith : 0 ≤ a),
    response_uniform_upper ht.1]

private theorem pulse_upper {q gain t deadline r g : ℝ}
    (hq : q ≤ 101 / 1000) (hg : gain ≤ g) (gg : 0 ≤ g)
    (ht : 0 ≤ t) (hle : t ≤ deadline) (hd : deadline ≤ 1)
    (hr : response deadline ≤ r) :
    readyPulse q gain 0 t ≤ 101 / 1000 + g * r := by
  have hcarry := decay_upper (show q - 1 / 10 ≤ (1 / 1000 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) ht
  have hr' := (response_mono_pulse ⟨ht, hle.trans hd⟩ ⟨ht.trans hle, hd⟩ hle).trans hr
  have hamp := mul_le_mul hg hr' (response_nonnegative ht) gg
  simp only [readyPulse, sub_zero]
  linarith

private theorem latency_gap {qFast qSlow fast slow early late gFast gSlow : ℝ}
    (hfast : FirstPulseReport qFast gFast (97 / 100) fast)
    (hslow : FirstPulseReport qSlow gSlow (103 / 100) slow)
    (fastCharge : 1 / 10 ≤ qFast) (slowCharge : qSlow ≤ 101 / 1000)
    (hEarly : 0 ≤ early) (hLate : late ≤ 1) (width : early + 1 / 20 ≤ late)
    (earlyFire : 97 / 100 ≤ 1 / 10 + gFast * response early)
    (lateSilent : 101 / 1000 + gSlow * response late < 103 / 100)
    (gainSlow : 0 ≤ gSlow) : 3 / 20 ≤ 1 / 10 + slow - fast := by
  have upper : fast ≤ early := by
    by_contra h
    have before := hfast.first early ⟨hEarly, lt_of_not_ge h⟩
    have comp := readyPulse_mono_initial (amplitude := gFast) (start := 0) (t := early) fastCharge
    simp only [readyPulse, sub_zero, sub_self, zero_mul, add_zero] at comp before
    linarith
  have lower : late < slow := by
    by_contra h
    have comp := pulse_upper slowCharge le_rfl gainSlow hslow.live.1 (le_of_not_gt h) hLate le_rfl
    linarith [hslow.hit]
  linarith

private theorem exp_at_least_sq {x g : ℝ}
    (bound : g ≤ Real.exp (x / 2)) (hg : 0 ≤ g) :
    g ^ 2 ≤ Real.exp x := by
  rw [show x = x / 2 + x / 2 by ring, Real.exp_add]
  nlinarith [mul_le_mul bound bound hg (Real.exp_pos _).le]

private theorem exp_at_most_sq {x g : ℝ}
    (bound : Real.exp (x / 2) ≤ g) :
    Real.exp x ≤ g ^ 2 := by
  rw [show x = x / 2 + x / 2 by ring, Real.exp_add]
  nlinarith [mul_le_mul bound bound (Real.exp_pos _).le ((Real.exp_pos _).le.trans bound)]

private theorem certified_response_lower {t sl fu r : ℝ}
    (ht : 0 ≤ t)
    (slow : sl ≤ Real.exp (-(1 / 2) * t))
    (fast : Real.exp (-(138629436 / 100000000) * t) ≤ fu)
    (diff : fu ≤ sl) (bound : r ≤ (156414 / 100000) * (sl - fu)) :
    r ≤ response t := by
  have ha : (138629436 / 100000000 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have hfast := (Real.exp_le_exp.mpr (show -a * t ≤ -(138629436 / 100000000) * t by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) ht])).trans fast
  exact bound.trans (mul_le_mul response_ratio_bounds.1 (sub_le_sub slow hfast)
    (sub_nonneg.mpr diff) (by
      exact (by norm_num : (0 : ℝ) ≤ 156414 / 100000).trans response_ratio_bounds.1))

private theorem certified_response_upper {t su fl r : ℝ}
    (ht : 0 ≤ t)
    (slow : Real.exp (-(1 / 2) * t) ≤ su)
    (fast : fl ≤ Real.exp (-(138629437 / 100000000) * t))
    (bound : (156415 / 100000) * (su - fl) ≤ r) :
    response t ≤ r := by
  have ha : a ≤ (138629437 / 100000000 : ℝ) := by dsimp [a]; linarith [KernelR.log_four_bounds.2]
  have hfast := fast.trans (Real.exp_le_exp.mpr (show -(138629437 / 100000000) * t ≤ -a * t by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) ht]))
  have diff : 0 ≤ Real.exp (-(1 / 2 : ℝ) * t) - Real.exp (-a * t) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [a_coarse_bounds.1]))
  exact (mul_le_mul response_ratio_bounds.2 (sub_le_sub slow hfast) diff (by norm_num)).trans bound

private theorem timedGain_lower {dose d g : ℝ} (hd : d ≤ dose) (cap : g ≤ 22 / 5)
    (write : g ≤ (6 / 5) * Real.exp ((11 / 10) * d)) :
    g ≤ timedCurrentGain dose (11 / 10) (22 / 5) :=
  le_min cap (write.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) (by norm_num)))

private theorem timedGain_upper {dose d g : ℝ} (hd : dose ≤ d)
    (write : (6 / 5) * Real.exp ((9 / 10) * d) ≤ g) :
    timedCurrentGain dose (9 / 10) (18 / 5) ≤ g :=
  (min_le_right _ _).trans ((mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) (by norm_num)).trans write)

private theorem certify_pair {dose qF qS fast slow early late gLo gHi rLo rHi : ℝ}
    (hfast : FirstPulseReport qF (timedCurrentGain dose (11 / 10) (22 / 5)) (97 / 100) fast)
    (hslow : FirstPulseReport qS (timedCurrentGain dose (9 / 10) (18 / 5)) (103 / 100) slow)
    (fastCharge : 1 / 10 ≤ qF) (slowCharge : qS ≤ 101 / 1000)
    (hgLo : gLo ≤ timedCurrentGain dose (11 / 10) (22 / 5)) (hgLoPos : 0 ≤ gLo)
    (hgHi : timedCurrentGain dose (9 / 10) (18 / 5) ≤ gHi) (hgHiPos : 0 ≤ gHi)
    (earlyPos : 0 ≤ early) (latePos : 0 ≤ late) (lateLive : late ≤ 1)
    (gap : early + 1 / 20 ≤ late) (hRespLo : rLo ≤ response early) (hrLoPos : 0 ≤ rLo)
    (hRespHi : response late ≤ rHi)
    (fires : 97 / 100 ≤ 1 / 10 + gLo * rLo) (quiet : 101 / 1000 + gHi * rHi < 103 / 100) :
    3 / 20 ≤ 1 / 10 + slow - fast := by
  apply latency_gap hfast hslow fastCharge slowCharge earlyPos lateLive gap
  · exact fires.trans (by linarith [mul_le_mul hgLo hRespLo hrLoPos (hgLoPos.trans hgLo)])
  · exact lt_of_le_of_lt (by
      linarith [mul_le_mul hgHi hRespHi (response_nonnegative latePos) hgHiPos]) quiet
  · exact le_min (by norm_num) (mul_nonneg (by norm_num) (Real.exp_pos _).le)


/-- Even a slow-corner cell that reports during the live pulse must have
received more than this dose. This rules out the small-dose regime. -/
private theorem small_dose_no_report {dose q t : ℝ} (hd : dose ≤ 360 / 1000)
    (hq : q ≤ 101 / 1000)
    (run : FirstPulseReport q (timedCurrentGain dose (9 / 10) (18 / 5)) (103 / 100) t) :
    False := by
  have g : timedCurrentGain dose (9 / 10) (18 / 5) ≤ 1659187 / 1000000 := by
    apply timedGain_upper hd
    have ex : Real.exp (((9 / 10 : ℝ) * (360 / 1000)) / 2) ∈ Icc (0 : ℝ) (1175863 / 1000000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    have sq := exp_at_most_sq (x := (9 / 10 : ℝ) * (360 / 1000)) ex.2
    linarith
  have h : response 1 ≤ 558 / 1000 := by
    have expBound : Real.exp (-(1 / 2 : ℝ)) ∈ Icc (0 : ℝ) (606532 / 1000000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    have nonneg : 0 ≤ Real.exp (-(1 / 2 : ℝ)) - (1 / 4 : ℝ) := by
      linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
    unfold response
    rw [mul_one, mul_one, exp_neg_a]
    have h := mul_le_mul response_ratio_bounds.2
      (sub_le_sub_right expBound.2 (1 / 4)) nonneg
      (by norm_num : (0 : ℝ) ≤ 156415 / 100000)
    linarith
  have b := pulse_upper hq g (by norm_num) run.live.1 run.live.2 le_rfl h
  linarith [run.hit]

/-- For every shared current-times-duration dose, a registered
zero-offset trial at opposing current, cap, FIRE and jitter corners
either lacks a report or misses the aperture. Conditional on both
reports, their skew is at least 15 microseconds. -/
theorem constant_current_corner_skew {dose qFast qSlow fast slow : ℝ}
    (hFast : FirstPulseReport qFast (timedCurrentGain dose (11 / 10) (22 / 5)) (97 / 100) fast)
    (hSlow : FirstPulseReport qSlow (timedCurrentGain dose (9 / 10) (18 / 5)) (103 / 100) slow)
    (fastCharge : 1 / 10 ≤ qFast) (slowCharge : qSlow ≤ 101 / 1000) :
    3 / 20 ≤ 1 / 10 + slow - fast := by
  by_cases first : dose ≤ 360 / 1000
  · exact (small_dose_no_report first slowCharge hSlow).elim
  by_cases upper0 : dose ≤ 474 / 1000
  · refine certify_pair (early := 631 / 1000) (late := 682 / 1000)
      (gLo := 1783034 / 1000000) (gHi := 1838456 / 1000000) (rLo := 488719 / 1000000) (rHi := 504535 / 1000000)
      hFast hSlow fastCharge slowCharge ?_ (by norm_num) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) ?_
      (by norm_num) (by norm_num)
    · apply timedGain_lower (d := 360 / 1000) (le_of_lt (lt_of_not_ge first)) (by norm_num)
      have ex : Real.exp (((11 / 10 : ℝ) * (360 / 1000)) / 2) ∈ Icc (1218960 / 1000000 : ℝ) 3 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_least_sq (x := (11 / 10 : ℝ) * (360 / 1000)) ex.1 (by norm_num)
      linarith
    · apply timedGain_upper upper0
      have ex : Real.exp (((9 / 10 : ℝ) * (474 / 1000)) / 2) ∈ Icc (0 : ℝ) (1237758 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_most_sq (x := (9 / 10 : ℝ) * (474 / 1000)) ex.2
      linarith
    · have slow : Real.exp (-(1 / 2 : ℝ) * (631 / 1000)) ∈ Icc (729422 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629436 / 100000000 : ℝ) * (631 / 1000)) ∈ Icc (0 : ℝ) (416968 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_lower (by norm_num) slow.1
        fast.2 (by norm_num) (by norm_num)
    · have slow : Real.exp (-(1 / 2 : ℝ) * (682 / 1000)) ∈ Icc (0 : ℝ) (711061 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629437 / 100000000 : ℝ) * (682 / 1000)) ∈ Icc (388501 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_upper (by norm_num) slow.2
        fast.1 (by norm_num)
  by_cases upper1 : dose ≤ 590 / 1000
  · refine certify_pair (early := 490 / 1000) (late := 541 / 1000)
      (gLo := 2021251 / 1000000) (gHi := 2040768 / 1000000) (rLo := 431262 / 1000000) (rHi := 454590 / 1000000)
      hFast hSlow fastCharge slowCharge ?_ (by norm_num) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) ?_
      (by norm_num) (by norm_num)
    · apply timedGain_lower (d := 474 / 1000) (le_of_lt (lt_of_not_ge upper0)) (by norm_num)
      have ex : Real.exp (((11 / 10 : ℝ) * (474 / 1000)) / 2) ∈ Icc (1297836 / 1000000 : ℝ) 3 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_least_sq (x := (11 / 10 : ℝ) * (474 / 1000)) ex.1 (by norm_num)
      linarith
    · apply timedGain_upper upper1
      have ex : Real.exp (((9 / 10 : ℝ) * (590 / 1000)) / 2) ∈ Icc (0 : ℝ) (1304085 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_most_sq (x := (9 / 10 : ℝ) * (590 / 1000)) ex.2
      linarith
    · have slow : Real.exp (-(1 / 2 : ℝ) * (490 / 1000)) ∈ Icc (782702 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629436 / 100000000 : ℝ) * (490 / 1000)) ∈ Icc (0 : ℝ) (506982 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_lower (by norm_num) slow.1
        fast.2 (by norm_num) (by norm_num)
    · have slow : Real.exp (-(1 / 2 : ℝ) * (541 / 1000)) ∈ Icc (0 : ℝ) (763000 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629437 / 100000000 : ℝ) * (541 / 1000)) ∈ Icc (472371 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_upper (by norm_num) slow.2
        fast.1 (by norm_num)
  by_cases upper2 : dose ≤ 707 / 1000
  · refine certify_pair (early := 396 / 1000) (late := 447 / 1000)
      (gLo := 2296340 / 1000000) (gHi := 2267383 / 1000000) (rLo := 379805 / 1000000) (rHi := 409183 / 1000000)
      hFast hSlow fastCharge slowCharge ?_ (by norm_num) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) ?_
      (by norm_num) (by norm_num)
    · apply timedGain_lower (d := 590 / 1000) (le_of_lt (lt_of_not_ge upper1)) (by norm_num)
      have ex : Real.exp (((11 / 10 : ℝ) * (590 / 1000)) / 2) ∈ Icc (1383336 / 1000000 : ℝ) 3 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_least_sq (x := (11 / 10 : ℝ) * (590 / 1000)) ex.1 (by norm_num)
      linarith
    · apply timedGain_upper upper2
      have ex : Real.exp (((9 / 10 : ℝ) * (707 / 1000)) / 2) ∈ Icc (0 : ℝ) (1374585 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_most_sq (x := (9 / 10 : ℝ) * (707 / 1000)) ex.2
      linarith
    · have slow : Real.exp (-(1 / 2 : ℝ) * (396 / 1000)) ∈ Icc (820367 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629436 / 100000000 : ℝ) * (396 / 1000)) ∈ Icc (0 : ℝ) (577545 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_lower (by norm_num) slow.1
        fast.2 (by norm_num) (by norm_num)
    · have slow : Real.exp (-(1 / 2 : ℝ) * (447 / 1000)) ∈ Icc (0 : ℝ) (799717 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629437 / 100000000 : ℝ) * (447 / 1000)) ∈ Icc (538118 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_upper (by norm_num) slow.2
        fast.1 (by norm_num)
  by_cases upper3 : dose ≤ 823 / 1000
  · refine certify_pair (early := 327 / 1000) (late := 378 / 1000)
      (gLo := 2611742 / 1000000) (gHi := 2516895 / 1000000) (rLo := 334170 / 1000000) (rHi := 368604 / 1000000)
      hFast hSlow fastCharge slowCharge ?_ (by norm_num) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) ?_
      (by norm_num) (by norm_num)
    · apply timedGain_lower (d := 707 / 1000) (le_of_lt (lt_of_not_ge upper2)) (by norm_num)
      have ex : Real.exp (((11 / 10 : ℝ) * (707 / 1000)) / 2) ∈ Icc (1475281 / 1000000 : ℝ) 3 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_least_sq (x := (11 / 10 : ℝ) * (707 / 1000)) ex.1 (by norm_num)
      linarith
    · apply timedGain_upper upper3
      have ex : Real.exp (((9 / 10 : ℝ) * (823 / 1000)) / 2) ∈ Icc (0 : ℝ) (1448244 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_most_sq (x := (9 / 10 : ℝ) * (823 / 1000)) ex.2
      linarith
    · have slow : Real.exp (-(1 / 2 : ℝ) * (327 / 1000)) ∈ Icc (849164 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629436 / 100000000 : ℝ) * (327 / 1000)) ∈ Icc (0 : ℝ) (635518 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_lower (by norm_num) slow.1
        fast.2 (by norm_num) (by norm_num)
    · have slow : Real.exp (-(1 / 2 : ℝ) * (378 / 1000)) ∈ Icc (0 : ℝ) (827789 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629437 / 100000000 : ℝ) * (378 / 1000)) ∈ Icc (592133 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_upper (by norm_num) slow.2
        fast.1 (by norm_num)
  by_cases upper4 : dose ≤ 937 / 1000
  · refine certify_pair (early := 274 / 1000) (late := 325 / 1000)
      (gLo := 2967196 / 1000000) (gHi := 2788839 / 1000000) (rLo := 294053 / 1000000) (rHi := 332761 / 1000000)
      hFast hSlow fastCharge slowCharge ?_ (by norm_num) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) ?_
      (by norm_num) (by norm_num)
    · apply timedGain_lower (d := 823 / 1000) (le_of_lt (lt_of_not_ge upper3)) (by norm_num)
      have ex : Real.exp (((11 / 10 : ℝ) * (823 / 1000)) / 2) ∈ Icc (1572471 / 1000000 : ℝ) 3 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_least_sq (x := (11 / 10 : ℝ) * (823 / 1000)) ex.1 (by norm_num)
      linarith
    · apply timedGain_upper upper4
      have ex : Real.exp (((9 / 10 : ℝ) * (937 / 1000)) / 2) ∈ Icc (0 : ℝ) (1524477 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_most_sq (x := (9 / 10 : ℝ) * (937 / 1000)) ex.2
      linarith
    · have slow : Real.exp (-(1 / 2 : ℝ) * (274 / 1000)) ∈ Icc (871968 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629436 / 100000000 : ℝ) * (274 / 1000)) ∈ Icc (0 : ℝ) (683970 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_lower (by norm_num) slow.1
        fast.2 (by norm_num) (by norm_num)
    · have slow : Real.exp (-(1 / 2 : ℝ) * (325 / 1000)) ∈ Icc (0 : ℝ) (850019 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629437 / 100000000 : ℝ) * (325 / 1000)) ∈ Icc (637278 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_upper (by norm_num) slow.2
        fast.1 (by norm_num)
  by_cases upper5 : dose ≤ 1044 / 1000
  · refine certify_pair (early := 233 / 1000) (late := 284 / 1000)
      (gLo := 3363621 / 1000000) (gHi := 3070762 / 1000000) (rLo := 259732 / 1000000) (rHi := 302001 / 1000000)
      hFast hSlow fastCharge slowCharge ?_ (by norm_num) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) ?_
      (by norm_num) (by norm_num)
    · apply timedGain_lower (d := 937 / 1000) (le_of_lt (lt_of_not_ge upper4)) (by norm_num)
      have ex : Real.exp (((11 / 10 : ℝ) * (937 / 1000)) / 2) ∈ Icc (1674222 / 1000000 : ℝ) 3 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_least_sq (x := (11 / 10 : ℝ) * (937 / 1000)) ex.1 (by norm_num)
      linarith
    · apply timedGain_upper upper5
      have ex : Real.exp (((9 / 10 : ℝ) * (1044 / 1000)) / 2) ∈ Icc (0 : ℝ) (1599677 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_most_sq (x := (9 / 10 : ℝ) * (1044 / 1000)) ex.2
      linarith
    · have slow : Real.exp (-(1 / 2 : ℝ) * (233 / 1000)) ∈ Icc (890028 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629436 / 100000000 : ℝ) * (233 / 1000)) ∈ Icc (0 : ℝ) (723972 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_lower (by norm_num) slow.1
        fast.2 (by norm_num) (by norm_num)
    · have slow : Real.exp (-(1 / 2 : ℝ) * (284 / 1000)) ∈ Icc (0 : ℝ) (867624 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629437 / 100000000 : ℝ) * (284 / 1000)) ∈ Icc (674549 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_upper (by norm_num) slow.2
        fast.1 (by norm_num)
  by_cases upper6 : dose ≤ 1140 / 1000
  · refine certify_pair (early := 201 / 1000) (late := 252 / 1000)
      (gLo := 3783760 / 1000000) (gHi := 3347873 / 1000000) (rLo := 230821 / 1000000) (rHi := 276030 / 1000000)
      hFast hSlow fastCharge slowCharge ?_ (by norm_num) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) ?_
      (by norm_num) (by norm_num)
    · apply timedGain_lower (d := 1044 / 1000) (le_of_lt (lt_of_not_ge upper5)) (by norm_num)
      have ex : Real.exp (((11 / 10 : ℝ) * (1044 / 1000)) / 2) ∈ Icc (1775707 / 1000000 : ℝ) 3 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_least_sq (x := (11 / 10 : ℝ) * (1044 / 1000)) ex.1 (by norm_num)
      linarith
    · apply timedGain_upper upper6
      have ex : Real.exp (((9 / 10 : ℝ) * (1140 / 1000)) / 2) ∈ Icc (0 : ℝ) (1670297 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have sq := exp_at_most_sq (x := (9 / 10 : ℝ) * (1140 / 1000)) ex.2
      linarith
    · have slow : Real.exp (-(1 / 2 : ℝ) * (201 / 1000)) ∈ Icc (904383 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629436 / 100000000 : ℝ) * (201 / 1000)) ∈ Icc (0 : ℝ) (756811 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_lower (by norm_num) slow.1
        fast.2 (by norm_num) (by norm_num)
    · have slow : Real.exp (-(1 / 2 : ℝ) * (252 / 1000)) ∈ Icc (0 : ℝ) (881617 / 1000000) :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      have fast : Real.exp (-(138629437 / 100000000 : ℝ) * (252 / 1000)) ∈ Icc (705146 / 1000000 : ℝ) 1 :=
        exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
      exact certified_response_upper (by norm_num) slow.2
        fast.1 (by norm_num)
  refine certify_pair (early := 178 / 1000) (late := 230 / 1000)
      (gLo := 4205186 / 1000000) (gHi := 3600000 / 1000000) (rLo := 208831 / 1000000) (rHi := 257125 / 1000000)
      hFast hSlow fastCharge slowCharge ?_ (by norm_num) ?_ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) ?_
      (by norm_num) (by norm_num)
  · apply timedGain_lower (d := 1140 / 1000) (le_of_lt (lt_of_not_ge upper6)) (by norm_num)
    have ex : Real.exp (((11 / 10 : ℝ) * (1140 / 1000)) / 2) ∈ Icc (1871984 / 1000000 : ℝ) 3 :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    have sq := exp_at_least_sq (x := (11 / 10 : ℝ) * (1140 / 1000)) ex.1 (by norm_num)
    linarith
  · unfold timedCurrentGain
    calc
      _ ≤ (18 / 5 : ℝ) := min_le_left _ _
      _ ≤ _ := by norm_num
  · have slow : Real.exp (-(1 / 2 : ℝ) * (178 / 1000)) ∈ Icc (914843 / 1000000 : ℝ) 1 :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    have fast : Real.exp (-(138629436 / 100000000 : ℝ) * (178 / 1000)) ∈ Icc (0 : ℝ) (781330 / 1000000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    exact certified_response_lower (by norm_num) slow.1
      fast.2 (by norm_num) (by norm_num)
  · have slow : Real.exp (-(1 / 2 : ℝ) * (230 / 1000)) ∈ Icc (0 : ℝ) (891369 / 1000000) :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    have fast : Real.exp (-(138629437 / 100000000 : ℝ) * (230 / 1000)) ∈ Icc (726984 / 1000000 : ℝ) 1 :=
      exp_bracket_10 (by norm_num) (by norm_num [Finset.sum_range_succ])
    exact certified_response_upper (by norm_num) slow.2
      fast.1 (by norm_num)

/-- The same shared wire delay cancels. The positive trial requires both
reports and strict skew below the registered aperture. -/
theorem constant_current_no_common_timing {current duration qFast qSlow wire : ℝ}
    (fastCharge : 1 / 10 ≤ qFast) (slowCharge : qSlow ≤ 101 / 1000) :
    ¬ ∃ fast slow : ℝ,
      FirstPulseReport qFast (timedCurrentGain (current * duration) (11 / 10) (22 / 5)) (97 / 100) fast ∧
      FirstPulseReport qSlow (timedCurrentGain (current * duration) (9 / 10) (18 / 5)) (103 / 100) slow ∧
      |((17 + 1 / 20 + slow) + wire) - ((17 - 1 / 20 + fast) + wire)| < 3 / 20 := by
  rintro ⟨fast, slow, hf, hs, accepted⟩
  have bound := constant_current_corner_skew hf hs fastCharge slowCharge
  linarith [(abs_lt.mp accepted).2]

/-- The charge interval used in the corner proof follows from quiet
relaxation after the width-one training pulse. The two corner reads are
at 16.95 and 17.05. A silent training pulse leaves at most its threshold
at expiry. -/
theorem timed_current_read_charge {atExpiry readTime : ℝ}
    (aboveRest : 1 / 10 ≤ atExpiry) (belowFire : atExpiry ≤ 103 / 100)
    (readLate : 16 ≤ readTime) :
    relax (1 / 2) (1 / 10) atExpiry 1 readTime ∈ Icc (1 / 10) (101 / 1000) := by
  have series := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 15 / 2 by norm_num) 15
  norm_num [Finset.sum_range_succ] at series
  have decay : Real.exp (-(1 / 2) * (readTime - 1)) ≤ 1 / 1000 := by
    calc
      _ ≤ Real.exp (-(15 / 2)) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by
        rw [Real.exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num)
          (show (1000 : ℝ) ≤ Real.exp (15 / 2) by linarith)
  have positive := Real.exp_pos (-(1 / 2) * (readTime - 1))
  have upper := mul_le_mul (show atExpiry - 1 / 10 ≤ 93 / 100 by linarith)
    decay positive.le (by norm_num)
  have lower := mul_nonneg (sub_nonneg.mpr aboveRest) positive.le
  constructor <;> unfold relax <;> linarith

end RecursiveLearning.Native
