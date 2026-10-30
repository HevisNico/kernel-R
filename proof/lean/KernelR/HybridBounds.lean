import KernelR.HybridFlow
import KernelR.Recovery

/-! Coarse bounds on actual real fabrication parameters, derived in Lean.
These do not assume membership in a stored rational certificate enclosure. -/
namespace KernelR.Hybrid

theorem a_coarse_bounds : 1 < a ∧ a < 7 / 5 := by
  dsimp [a]
  constructor <;> linarith [KernelR.log_four_bounds.1, KernelR.log_four_bounds.2]

theorem response_lower_bound (t : ℝ) : a * t * Real.exp (-a * t) ≤ response t := by
  have ha := a_coarse_bounds.1
  have hd : 0 < a - 1 / 2 := by linarith
  have hc : 0 < a / (a - 1 / 2) := div_pos (by linarith) hd
  have he : Real.exp (-(1 / 2) * t) - Real.exp (-a * t) =
      Real.exp (-a * t) * (Real.exp ((a - 1 / 2) * t) - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_left
    (show (a - 1 / 2) * t ≤ Real.exp ((a - 1 / 2) * t) - 1 by
      linarith [Real.add_one_le_exp ((a - 1 / 2) * t)])
    (mul_nonneg hc.le (Real.exp_pos (-a * t)).le)
  have halgebra : a / (a - 1 / 2) * Real.exp (-a * t) * ((a - 1 / 2) * t) =
      a * t * Real.exp (-a * t) := by
    calc
      _ = (a / (a - 1 / 2) * (a - 1 / 2)) * (t * Real.exp (-a * t)) := by ring
      _ = _ := by rw [div_mul_cancel₀ a (ne_of_gt hd)]; ring
  rw [halgebra] at h
  simpa only [response, he, mul_assoc] using h

theorem sensor_response_lower : (1 / 55 : ℝ) ≤ response (1 / 50) := by
  have ha := a_coarse_bounds
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have he : (243 / 250 : ℝ) ≤ Real.exp (-a * (1 / 50)) := by
    linarith [Real.add_one_le_exp (-a * (1 / 50))]
  have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ a * (1 / 50) by positivity)
  have hlower := response_lower_bound (1 / 50)
  nlinarith

theorem PhysicalBox.epsilon_bounds {n θ ε} (hb : @PhysicalBox n θ ε) : 0 ≤ ε ∧ ε ≤ 1 / 10 := by
  rcases hb.1 with rfl | rfl <;> norm_num

theorem relative_box_upper {ε nominal value : ℝ} (he : ε ≤ 1 / 10) (hn : 0 ≤ nominal)
    (h : InRelativeBox ε nominal value) : value ≤ (11 / 10) * nominal := by
  have hu := h.2
  nlinarith

theorem PhysicalBox.coarse_upper {n θ ε} (hb : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    (θ i).cap p ≤ 5 ∧ (θ i).lm p ≤ 14 ∧ (θ i).ls p ≤ 3 ∧
      (θ i).le p ≤ 11 ∧ (θ i).inputGain p ≤ 60 := by
  have he := hb.epsilon_bounds.2
  have hlmpos : 0 < Real.log (5 / 4) / (1 / 50) :=
    div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hlspos : 0 < Real.log 8 / (53 / 50) :=
    div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hlepos : 0 < a / (3 / 20) := div_pos (by linarith [a_coarse_bounds.1]) (by norm_num)
  have hrpos : 0 < response (1 / 50) := lt_of_lt_of_le (by norm_num) sensor_response_lower
  have hmpos : 0 < (1 - 1 / 40) / response (1 / 50) := div_pos (by norm_num) hrpos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := relative_box_upper he (by norm_num : (0 : ℝ) ≤ 4) (hb.2 i p).1
    linarith
  · have h := relative_box_upper he hlmpos.le (hb.2 i p).2.1
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
    norm_num at h hlog
    linarith
  · have h := relative_box_upper he hlspos.le (hb.2 i p).2.2.1
    have hlog : Real.log 8 < 21 / 10 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
      linarith [Real.log_two_lt_d9]
    norm_num at h
    linarith
  · have h := relative_box_upper he hlepos.le (hb.2 i p).2.2.2.1
    have ha := a_coarse_bounds.2
    norm_num at h
    linarith
  · have h := relative_box_upper he hmpos.le (hb.2 i p).2.2.2.2
    have hratio : (1 - 1 / 40) / response (1 / 50) ≤ (600 / 11 : ℝ) :=
      (div_le_iff₀ hrpos).2 (by nlinarith [sensor_response_lower])
    linarith

theorem PhysicalBox.cap_positive {n θ ε} (hb : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    0 < (θ i).cap p := by
  have he : ε < 1 := by rcases hb.1 with rfl | rfl <;> norm_num
  exact positive_of_relative_box he (by norm_num) (hb.2 i p).1

theorem PhysicalBox.input_gain_positive {n θ ε} (hb : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    0 < (θ i).inputGain p := by
  have he : ε < 1 := by rcases hb.1 with rfl | rfl <;> norm_num
  have hrpos : 0 < response (1 / 50) := lt_of_lt_of_le (by norm_num) sensor_response_lower
  exact positive_of_relative_box he (div_pos (by norm_num) hrpos) (hb.2 i p).2.2.2.2

end KernelR.Hybrid
