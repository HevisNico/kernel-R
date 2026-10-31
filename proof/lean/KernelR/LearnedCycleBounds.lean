import KernelR.LearnedResponse
import KernelR.Indefinite

/-! Uniform real crossing and phase-clock bounds for a stable learned pulse.
These bounds use the actual physical fabrication expressions. They do not
postulate a pulse-case word or a stored interval enclosure. -/
namespace KernelR.Hybrid
open Set

theorem relative_box_lower {epsilon nominal value : ℝ} (he : epsilon ≤ 1/10)
    (hn : 0 ≤ nominal) (h : InRelativeBox epsilon nominal value) :
    (9/10:ℝ)*nominal ≤ value := by
  have hm := mul_nonneg (sub_nonneg.mpr he) hn
  nlinarith [h.1]

theorem PhysicalBox.input_gain_bounds {n θ epsilon} (hb : @PhysicalBox n θ epsilon)
    (i : Fin n) (p : Port) : 31 ≤ (θ i).inputGain p ∧ (θ i).inputGain p ≤ 60 := by
  have hr : 0 < response (1/50) := lt_of_lt_of_le (by norm_num) sensor_response_lower
  have hru : response (1/50) ≤ (7/250:ℝ) := by
    have h := response_linear_upper (t := 1/50) (by norm_num)
    nlinarith [a_coarse_bounds.2]
  have hn : (310/9:ℝ) ≤ (1-1/40) / response (1/50) :=
    (le_div_iff₀ hr).mpr (by linarith)
  have hp : 0 ≤ (1-1/40:ℝ) / response (1/50) := div_nonneg (by norm_num) hr.le
  have hlo := relative_box_lower hb.epsilon_bounds.2 hp (hb.2 i p).2.2.2.2
  exact ⟨by linarith, (hb.coarse_upper i p).2.2.2.2⟩

theorem response_twentieth_lower : (93/2000:ℝ) ≤ response (1/20) := by
  have ha := a_coarse_bounds
  have he : (93/100:ℝ) ≤ Real.exp (-a*(1/20)) := by
    linarith [Real.add_one_le_exp (-a*(1/20))]
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ a*(1/20) by linarith)
  have hr := response_lower_bound (1/20)
  nlinarith

theorem auxPulse_normal (initial gain t : ℝ) : auxPulse initial gain 0 t =
    1/40 + (initial-1/40)*Real.exp (-(1/2)*t) + gain*response t := by
  simp [auxPulse, readyPulse]
  ring

theorem auxiliary_early {initial gain t : ℝ}
    (hi : |initial-1/40| ≤ 1/100000) (hg : 31 ≤ gain ∧ gain ≤ 60)
    (ht : 0 ≤ t ∧ t ≤ 1/100) : auxPulse initial gain 0 t < 1 := by
  have hp := (Real.exp_pos (-(1/2:ℝ)*t)).le
  have he : Real.exp (-(1/2:ℝ)*t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hres := mul_le_mul (abs_le.mp hi).2 he hp (by norm_num : (0:ℝ) ≤ 1/100000)
  have hr := response_linear_upper ht.1
  have hat := mul_le_mul_of_nonneg_right a_coarse_bounds.2.le ht.1
  have hru : response t ≤ (7/500:ℝ) := by linarith
  have hm := mul_le_mul hg.2 hru (response_nonnegative ht.1) (by norm_num : (0:ℝ) ≤ 60)
  rw [auxPulse_normal]
  linarith

theorem auxiliary_late {initial gain : ℝ}
    (hi : |initial-1/40| ≤ 1/100000) (hg : 31 ≤ gain ∧ gain ≤ 60) :
    1 < auxPulse initial gain 0 (1/20) := by
  have hp := (Real.exp_pos (-(1/2:ℝ)*(1/20))).le
  have he : Real.exp (-(1/2:ℝ)*(1/20)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hres := mul_le_mul_of_nonneg_right (abs_le.mp hi).1 hp
  have hlo : -(1/100000:ℝ) ≤ (initial-1/40)*Real.exp (-(1/2)*(1/20)) := by linarith
  have hm := mul_le_mul hg.1 response_twentieth_lower
    (by norm_num : (0:ℝ) ≤ 93/2000) (by linarith : 0 ≤ gain)
  rw [auxPulse_normal]
  linarith

theorem auxiliary_latency_exists {initial gain : ℝ}
    (hi : |initial-1/40| ≤ 1/100000) (hg : 31 ≤ gain ∧ gain ≤ 60) :
    ∃ tau, 1/100 < tau ∧ tau ≤ 1/20 ∧ auxPulse initial gain 0 tau = 1 ∧
      A22.Crossing.IsFirstCrossing (auxPulse initial gain 0) 0 tau := by
  have hc : Continuous (auxPulse initial gain 0) := by unfold auxPulse readyPulse response; fun_prop
  obtain ⟨tau, hf, hupper⟩ := A22.Crossing.first_crossing_exists
    (a := 0) (b := 1/20) (by norm_num) hc.continuousOn (auxiliary_late hi hg).le
  have hlower : (1/100:ℝ) < tau := by
    by_contra hn
    have h := auxiliary_early hi hg ⟨hf.1, le_of_not_gt hn⟩
    linarith [hf.2.1]
  have hbound := continuous_bound_from_Ico (show (0:ℝ) < tau by linarith)
    hc.continuousOn (fun t ht => (hf.2.2 t ht).le) tau ⟨hf.1, le_rfl⟩
  exact ⟨tau, hlower, hupper, le_antisymm hbound hf.2.1, hf⟩

theorem PhysicalBox.mark_duration_bounds {n θ epsilon} (hb : @PhysicalBox n θ epsilon)
    (i : Fin n) (p : Port) :
    (1/55:ℝ) ≤ Real.log (5/4) / (θ i).lm p ∧
      Real.log (5/4) / (θ i).lm p ≤ 1/45 := by
  have hp : 0 < Real.log (5/4:ℝ) := Real.log_pos (by norm_num)
  have hnp : 0 ≤ Real.log (5/4:ℝ) / (1/50) := div_nonneg hp.le (by norm_num)
  have hlo := relative_box_lower hb.epsilon_bounds.2 hnp (hb.2 i p).2.1
  have hhi := relative_box_upper hb.epsilon_bounds.2 hnp (hb.2 i p).2.1
  norm_num at hlo hhi
  constructor
  · apply (le_div_iff₀ (hb.rates_positive i p).1).mpr; nlinarith
  · apply (div_le_iff₀ (hb.rates_positive i p).1).mpr; nlinarith

theorem PhysicalBox.silent_duration_bounds {n θ epsilon} (hb : @PhysicalBox n θ epsilon)
    (i : Fin n) (p : Port) :
    (53/55:ℝ) ≤ Real.log 8 / (θ i).ls p ∧ Real.log 8 / (θ i).ls p ≤ 53/45 := by
  have hp : 0 < Real.log (8:ℝ) := Real.log_pos (by norm_num)
  have hnp : 0 ≤ Real.log (8:ℝ) / (53/50) := div_nonneg hp.le (by norm_num)
  have hlo := relative_box_lower hb.epsilon_bounds.2 hnp (hb.2 i p).2.2.1
  have hhi := relative_box_upper hb.epsilon_bounds.2 hnp (hb.2 i p).2.2.1
  norm_num at hlo hhi
  constructor
  · apply (le_div_iff₀ (hb.rates_positive i p).2.1).mpr; nlinarith
  · apply (div_le_iff₀ (hb.rates_positive i p).2.1).mpr; nlinarith

theorem PhysicalBox.error_duration_bounds {n θ epsilon} (hb : @PhysicalBox n θ epsilon)
    (i : Fin n) (p : Port) :
    (3/22:ℝ) ≤ a / (θ i).le p ∧ a / (θ i).le p ≤ 1/6 := by
  have hnp : 0 ≤ a / (3/20) := div_nonneg (by linarith [a_coarse_bounds.1]) (by norm_num)
  have hlo := relative_box_lower hb.epsilon_bounds.2 hnp (hb.2 i p).2.2.2.1
  have hhi := relative_box_upper hb.epsilon_bounds.2 hnp (hb.2 i p).2.2.2.1
  norm_num at hlo hhi
  constructor
  · apply (le_div_iff₀ (hb.rates_positive i p).2.2).mpr; nlinarith
  · apply (div_le_iff₀ (hb.rates_positive i p).2.2).mpr; nlinarith

theorem response_half_upper : response (1/2) ≤ (9/20:ℝ) := by
  have ha : (4/3:ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have had : 0 < a-1/2 := by linarith
  have hfactor : a/(a-1/2) ≤ (8/5:ℝ) := (div_le_iff₀ had).mpr (by linarith)
  have hhalf : Real.exp (-a*(1/2)) = (1/2:ℝ) := by
    have hp := Real.exp_pos (-a*(1/2))
    have hs : Real.exp (-a*(1/2))^2 = (1/4:ℝ) := by
      rw [pow_two, ← Real.exp_add, show -a*(1/2)+ -a*(1/2) = -a by ring,
        a, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 4)]
      norm_num
    nlinarith
  have hquarter : Real.exp (-(1/4:ℝ)) ≤ 32/41 := by
    have hl := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 1/4 by norm_num)
    have hm := mul_le_mul_of_nonneg_right hl (Real.exp_pos (-(1/4:ℝ))).le
    have he : Real.exp (1/4:ℝ) * Real.exp (-(1/4:ℝ)) = 1 := by
      rw [← Real.exp_add]; norm_num
    rw [he] at hm
    norm_num at hm
    linarith
  have hdiff : 0 ≤ Real.exp (-(1/2:ℝ)*(1/2))-Real.exp (-a*(1/2)) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_exp.mpr (by linarith)
  have hu : Real.exp (-(1/2:ℝ)*(1/2))-Real.exp (-a*(1/2)) ≤ 32/41-1/2 := by
    rw [hhalf]; norm_num; exact hquarter
  have hm := mul_le_mul hfactor hu hdiff (by norm_num : (0:ℝ) ≤ 8/5)
  dsimp [response]
  linarith

theorem learned_latency_after_half {gain f : ℝ} (hg : 9/5 ≤ gain ∧ gain ≤ 19/10)
    (hf : A22.Crossing.IsFirstCrossing (learnedHead gain) 0 f) : (1/2:ℝ) < f := by
  have hm := mul_le_mul hg.2 response_half_upper (response_nonnegative (by norm_num))
    (by norm_num : (0:ℝ) ≤ 19/10)
  have hsmall : learnedHead gain (1/2) < 1 := by dsimp [learnedHead]; linarith
  by_contra hn
  have hle := (learned_head_strictMono (show 0 < gain by linarith)).monotoneOn
    ⟨hf.1, by linarith [le_of_not_gt hn]⟩ (show (1/2:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (le_of_not_gt hn)
  linarith [hf.2.1]

theorem LearnedRest.upper_region {n θ active s} (hs : @LearnedRest n θ active s) : UpperRegion s := by
  intro i
  refine ⟨by linarith [(hs.recovery i).1], by rw [hs.charge i]; norm_num, ?_⟩
  intro p
  have hm := (abs_le.mp (hs.sensor i p)).2
  rw [hs.aux i p]
  dsimp [auxUpper]
  linarith

theorem Execution.reserve_learned_invariant {n θ epsilon route active s u}
    (e : @Execution n θ route s u) (hs : LearnedRest θ active s) (hb : PhysicalBox θ epsilon)
    (i : Fin n) : 50 ≤ u.x i .energy ∧ u.x i .energy ≤ 100 :=
  e.reserve_invariant i (hs.reserve i) (e.actual_work_bound hb hs.upper_region hs.cap i)

end KernelR.Hybrid
