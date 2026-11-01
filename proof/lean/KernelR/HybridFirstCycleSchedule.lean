import KernelR.HybridAuxCycle
import KernelR.HybridPulseBounds

namespace KernelR.Hybrid

/-- Scalar protected-phase endpoints and strict preguards, independently of
any supplied hybrid execution. -/
theorem protected_decay_schedule {initial floor rate : ℝ}
    (hf : 0 < floor) (hi : floor < initial) (hr : 0 < rate) :
    0 < Real.log (initial / floor) / rate ∧
    initial * Real.exp (-rate * (Real.log (initial / floor) / rate)) = floor ∧
    ∀ t : ℝ, 0 ≤ t → t < Real.log (initial / floor) / rate →
      floor < initial * Real.exp (-rate * t) := by
  have hip : 0 < initial := hf.trans hi
  have hratio : 0 < initial / floor := div_pos hip hf
  have hd : 0 < Real.log (initial / floor) / rate :=
    div_pos (Real.log_pos ((one_lt_div hf).mpr hi)) hr
  have hend : initial * Real.exp (-rate * (Real.log (initial / floor) / rate)) = floor := by
    have he : -rate * (Real.log (initial / floor) / rate) = -Real.log (initial / floor) := by
      field_simp [ne_of_gt hr]
    rw [he,Real.exp_neg,Real.exp_log hratio]
    field_simp [ne_of_gt hip,ne_of_gt hf]
  refine ⟨hd,hend,?_⟩
  intro t _ ht
  rw [← hend]
  apply mul_lt_mul_of_pos_left _ hip
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- Fabrication bounds determine the first MARK/SILENT/ERROR schedule.
The raw expiry at relative time 1 may lie in SILENT or ERROR. -/
theorem PhysicalBox.first_cycle_schedule {n θ ε} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) {tau : ℝ} (htau : 1 / 100 < tau ∧ tau < 1 / 40) :
    tau < tau + Real.log (5 / 4) / (θ i).lm p ∧
    tau + Real.log (5 / 4) / (θ i).lm p < 1 / 20 ∧
    99 / 100 < tau + Real.log (5 / 4) / (θ i).lm p + Real.log 8 / (θ i).ls p ∧
    tau + Real.log (5 / 4) / (θ i).lm p + Real.log 8 / (θ i).ls p < 123 / 100 ∧
    1 < tau + auxCycleDuration (θ i) p ∧
    tau + auxCycleDuration (θ i) p < 419 / 300 := by
  have hmark := hb.mark_duration_upper i p
  have hsilent := protected_duration_upper hb.epsilon_bounds.2 (by norm_num : (0 : ℝ) < 53 / 50)
    (Real.log_pos (by norm_num : (1 : ℝ) < 8)) (hb.2 i p).2.2.1
  rcases hb.aux_durations_lower i p with ⟨hlmark,hlsilent,hlerror⟩
  have hpositive := hb.aux_durations_positive i p
  have hlcycle := hb.aux_cycle_duration_lower i p
  have hucycle := hb.aux_cycle_duration_upper i p
  refine ⟨by linarith [hpositive.1],by linarith,by linarith,by linarith,by linarith,by linarith⟩

/-- A quantitative margin before ERROR, retaining the real birth residual. -/
theorem readyPulse_first_weak_margin {initial amplitude start t : ℝ}
    (hi : initial ≤ 10001 / 100000) (ha : amplitude ≤ 4 / 3) (ht : start ≤ t) :
    readyPulse initial amplitude start t ≤ 24 / 25 := by
  have hd := sub_nonneg.mpr ht
  have hc := decay_upper (show initial - 1 / 10 ≤ (1 / 100000 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hr := mul_le_mul_of_nonneg_left (response_uniform_upper hd) (by norm_num : (0 : ℝ) ≤ 4 / 3)
  unfold readyPulse
  linarith

/-- The remaining raw drive is already attenuated when ERROR can begin. -/
theorem raw_attenuation_after_error_start {elapsed : ℝ} (ht : 99 / 100 ≤ elapsed) :
    Real.exp (-a * elapsed) < 1 / 2 := by
  calc
    _ ≤ Real.exp (-(1 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      dsimp [a]
      nlinarith [KernelR.log_four_bounds.1]
    _ < _ := Real.exp_neg_one_lt_half

theorem cap_raw_amplitude_tiny_error {gain elapsed : ℝ}
    (hg : gain ≤ 22 / 5) (ht : 99 / 100 ≤ elapsed) :
    gain * Real.exp (-a * elapsed) ≤ 11 / 5 := by
  have h1 := mul_le_mul_of_nonneg_right hg (Real.exp_pos (-a * elapsed)).le
  have h2 := mul_le_mul_of_nonneg_left (raw_attenuation_after_error_start ht).le
    (by norm_num : (0 : ℝ) ≤ 22 / 5)
  linarith

/-- During the possible ERROR/raw overlap, even the full fabrication cap
leaves a strict READY guard margin. The comparison profile only needs its
initial charge and a smooth upper drive, not a frozen physical gain. -/
theorem readyPulse_tiny_error_guard {initial amplitude start t : ℝ}
    (hi : initial ≤ 24 / 25) (ha : amplitude ≤ 11 / 5)
    (ht : start ≤ t) (hu : t ≤ start + 1 / 100) :
    readyPulse initial amplitude start t ≤ 2477 / 2500 ∧
      readyPulse initial amplitude start t < 1 := by
  have hd := sub_nonneg.mpr ht
  have hc := decay_upper (show initial - 1 / 10 ≤ (43 / 50 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hr := mul_le_mul_of_nonneg_left (response_upper hd) (by norm_num : (0 : ℝ) ≤ 11 / 5)
  have htime : a * (t - start) ≤ (7 / 5 : ℝ) * (1 / 100) :=
    mul_le_mul a_coarse_bounds.2.le (by linarith) hd (by norm_num)
  unfold readyPulse
  constructor <;> nlinarith

end KernelR.Hybrid
