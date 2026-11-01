import KernelR.HybridFirstCycleSchedule

namespace KernelR.Hybrid
open Set

/-- The true exponential response remains strictly below the first main guard
through .4, even with carried charge .14 and learned gain 2. -/
theorem readyPulse_learned_four_tenths_margin {initial amplitude start t : ℝ}
    (hi : initial ≤ 7 / 50) (ha : amplitude ≤ 2)
    (ht : start ≤ t) (hu : t ≤ start + 2 / 5) :
    readyPulse initial amplitude start t ≤ 499 / 500 ∧
      readyPulse initial amplitude start t < 1 := by
  have hd := sub_nonneg.mpr ht
  have hc := decay_upper (show initial - 1 / 10 ≤ (1 / 25 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have he : (571 / 1000 : ℝ) ≤ Real.exp (-(14 / 25 : ℝ)) := by
    have h := Real.exp_bound (x := -(14 / 25 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have hdecay : (571 / 1000 : ℝ) ≤ Real.exp (-a * (t - start)) :=
    he.trans (Real.exp_le_exp.mpr (by nlinarith [a_coarse_bounds.2]))
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hr := mul_le_mul_of_nonneg_left (response_le_raw_charge hd) (by norm_num : (0 : ℝ) ≤ 2)
  unfold readyPulse
  constructor <;> nlinarith

theorem readyPulse_root_after_four_tenths {initial amplitude start t : ℝ}
    (hi : initial ≤ 7 / 50) (ha : amplitude ≤ 2) (ht : start ≤ t)
    (hroot : readyPulse initial amplitude start t = 1) : start + 2 / 5 < t := by
  by_contra hn
  have h := (readyPulse_learned_four_tenths_margin hi ha ht (le_of_not_gt hn)).2
  rw [hroot] at h
  exact (lt_irrefl _ h)

/-- ERROR and raw expiry both finish before the constructed FAST endpoint.
This removes any competing main guard while assembling the auxiliary cycle. -/
theorem PhysicalBox.first_cycle_before_fast_end {n θ ε} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) {sensorLatency firingLatency : ℝ}
    (hsensor : 1 / 100 < sensorLatency ∧ sensorLatency < 1 / 40)
    (hfire : 2 / 5 < firingLatency) :
    sensorLatency + auxCycleDuration (θ i) p < firingLatency + 1 ∧
      (1 : ℝ) < firingLatency + 1 := by
  have haux := (hb.first_cycle_schedule i p hsensor).2.2.2.2.2
  constructor <;> linarith

/-- Scalar endpoints of the first strong A pulse, using the actual birth
recovery rather than a nominal reset or an assumed later READY section. -/
theorem birth_first_strong_slow_at32_bounds {birthRecovery fireTime : ℝ}
    (hb : 7999 / 100000 ≤ birthRecovery ∧ birthRecovery ≤ 8001 / 100000)
    (hf : 24 + 2 / 5 < fireTime ∧ fireTime < 24 + 9 / 10) :
    7 / 50 < (1 / 4 : ℝ) * Real.exp (-birthRecovery * (32 - (fireTime + 1))) ∧
      (1 / 4 : ℝ) * Real.exp (-birthRecovery * (32 - (fireTime + 1))) < 4 / 25 := by
  have hd : 61 / 10 < 32 - (fireTime + 1) ∧ 32 - (fireTime + 1) < 33 / 5 := by
    constructor <;> linarith [hf.1,hf.2]
  have hmulLo := mul_le_mul hb.1 hd.1.le (by norm_num : (0 : ℝ) ≤ 61 / 10)
    (show 0 ≤ birthRecovery by linarith [hb.1])
  have hmulHi := mul_le_mul hb.2 hd.2.le (show 0 ≤ 32 - (fireTime + 1) by linarith [hd.1])
    (by norm_num : (0 : ℝ) ≤ 8001 / 100000)
  have hIlo : (12 / 25 : ℝ) ≤ birthRecovery * (32 - (fireTime + 1)) := by nlinarith
  have hIhi : birthRecovery * (32 - (fireTime + 1)) ≤ (27 / 50 : ℝ) := by nlinarith
  have hexpLo : (14 / 25 : ℝ) < Real.exp (-(27 / 50 : ℝ)) := by
    have h := Real.exp_bound (x := -(27 / 50 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have hexpHi : Real.exp (-(12 / 25 : ℝ)) < 16 / 25 := by
    have h := Real.exp_bound (x := -(12 / 25 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have hlo := Real.exp_le_exp.mpr (show -(27 / 50 : ℝ) ≤
    -birthRecovery * (32 - (fireTime + 1)) by nlinarith)
  have hhi := Real.exp_le_exp.mpr (show -birthRecovery * (32 - (fireTime + 1)) ≤
    -(12 / 25 : ℝ) by nlinarith)
  constructor <;> linarith

theorem birth_first_strong_slow_guards_to32 {birthRecovery fireTime : ℝ}
    (hb : 7999 / 100000 ≤ birthRecovery ∧ birthRecovery ≤ 8001 / 100000)
    (hf : 24 + 2 / 5 < fireTime ∧ fireTime < 24 + 9 / 10) :
    ∀ t ∈ Icc (fireTime + 1) 32,
      1 / 10 < (1 / 4 : ℝ) * Real.exp (-birthRecovery * (t - (fireTime + 1))) ∧
        (1 / 4 : ℝ) * Real.exp (-birthRecovery * (t - (fireTime + 1))) ≤ 1 / 4 := by
  intro t ht
  have hend := birth_first_strong_slow_at32_bounds hb hf
  have hbpos : 0 ≤ birthRecovery := by linarith [hb.1]
  have hlo := Real.exp_le_exp.mpr (show -birthRecovery * (32 - (fireTime + 1)) ≤
    -birthRecovery * (t - (fireTime + 1)) by nlinarith [ht.2])
  have hhi := Real.exp_le_one_iff.mpr (show -birthRecovery * (t - (fireTime + 1)) ≤ 0 by
    nlinarith [ht.1])
  constructor <;> linarith [hend.1]

end KernelR.Hybrid
