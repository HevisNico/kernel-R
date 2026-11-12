import Thresholds.ErrorReadHandoff

/-! A short live-current ERROR segment up to raw expiry. This prefix
uses native guards as well as the realized guards of the training task. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

structure LiveErrorExpiry (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port)
    (origin lower level : ℝ) where
  flow : Flow θ s (errorTailEnd θ s 0 p (some origin) (origin + 1))
  main : s.main 0 = .ready
  mode : s.aux 0 p = .error
  other_modes : ∀ q ≠ p, s.aux 0 q = .ready
  main_guard : ∀ t ∈ Ico s.time (origin + 1), flow.path t 0 .q < level
  sensor_guard : ∀ t ∈ Ico s.time (origin + 1), lower < flow.path t 0 (.m p)
  above_lower : lower < (errorTailEnd θ s 0 p (some origin) (origin + 1)).x 0 (.m p)
  charge : (errorTailEnd θ s 0 p (some origin) (origin + 1)).x 0 .q ∈ Icc (1 / 10) (47 / 50)
  energy : 50 ≤ (errorTailEnd θ s 0 p (some origin) (origin + 1)).x 0 .energy ∧
    (errorTailEnd θ s 0 p (some origin) (origin + 1)).x 0 .energy ≤ 100

/-- The gain can evolve during the remaining raw current. Even its
largest possible drive keeps the main charge below 0.94, and the
sensor is still above both its realized and nominal exit levels. -/
theorem live_error_expiry {θ ε s p origin lower level}
    (box : @PhysicalBox 1 θ ε) (threshold : 19 / 20 ≤ level)
    (window : origin + 24 / 25 ≤ s.time ∧ s.time < origin + 1)
    (lo : lower < 1 / 20)
    (sensor : s.x 0 (.m p) ∈ Icc (19 / 200) (21 / 200))
    (outputGain : Real.exp (s.x 0 (.z p) + 8 * (s.x 0 (.m p) - lower)) ≤ 13 / 5)
    (charge : s.x 0 .q ∈ Icc (1 / 10) (217 / 250))
    (energy : 50 ≤ s.x 0 .energy ∧ s.x 0 .energy ≤ 100)
    (main : s.main 0 = .ready) (aux : s.aux 0 p = .error)
    (other : ∀ q ≠ p, s.aux 0 q = .ready ∧ s.x 0 (.m q) = 1 / 40)
    (raw : s.raw 0 p = some origin) (otherRaw : ∀ q ≠ p, s.raw 0 q = none)
    (pending : ∀ d ∈ s.pending, origin + 1 ≤ d.due) :
    Nonempty (LiveErrorExpiry θ s p origin lower level) := by
  let T := origin + 1
  let path := errorTailValues θ s 0 p (some origin)
  let rhs := errorTailRhs θ s 0 p (some origin)
  let m := errorTailSensor θ s 0 p
  let r := (θ 0).le p
  let forcing := errorTailDrive θ s 0 p (some origin)
  have rp : 0 < r := (box.rates_positive 0 p).2.2
  have ru : r ≤ 11 := (box.coarse_upper 0 p).2.2.2.1
  have mRange (t : ℝ) (ht : t ∈ Icc s.time T) : m t ∈ Icc (1 / 20) (21 / 200) := by
    have elapsed : t - s.time ≤ 1 / 25 := by linarith [ht.2]
    have hx := mul_le_mul ru elapsed (sub_nonneg.mpr ht.1) (by norm_num : (0 : ℝ) ≤ 11)
    have he : (14 / 25 : ℝ) ≤ Real.exp (-r * (t - s.time)) := by
      linarith [Real.add_one_le_exp (-r * (t - s.time))]
    constructor
    · have hm := mul_le_mul sensor.1 he (by norm_num : (0 : ℝ) ≤ 14 / 25)
        (by linarith [sensor.1] : 0 ≤ s.x 0 (.m p))
      change (1 / 20 : ℝ) ≤ s.x 0 (.m p) * Real.exp (-r * (t - s.time))
      linarith
    · exact decay_upper sensor.2 (by norm_num) rp.le (sub_nonneg.mpr ht.1)
  have gain (t : ℝ) (ht : t ∈ Icc s.time T) :
      Real.exp (errorTailGain θ s 0 p t) ≤ 13 / 5 := by
    refine (Real.exp_le_exp.mpr ?_).trans outputGain
    have hm := (mRange t ht).1
    change s.x 0 (.z p) + 8 * (s.x 0 (.m p) - m t) ≤ _
    linarith
  have atten : rawInputScale (some origin) s.time ≤ 2 / 5 := by
    have series := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4
    norm_num [Finset.sum_range_succ] at series
    have expOne : (5 / 2 : ℝ) ≤ Real.exp 1 := by linarith
    calc
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by
        dsimp [a]
        nlinarith [KernelR.log_four_bounds.1, window.1])
      _ ≤ _ := by
        rw [Real.exp_neg]
        have bound := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5 / 2) expOne
        norm_num [one_div] at bound
        exact bound
  have forceBound (t : ℝ) (ht : t ∈ Icc s.time T) :
      0 ≤ forcing t ∧ forcing t ≤ 42 / 25 := by
    have rawNonneg := rawInputScale_nonnegative (some origin) s.time
    have aPos : 0 ≤ a := by linarith [a_coarse_bounds.1]
    have expBound : Real.exp (-a * (t - s.time)) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith [mul_nonneg aPos (sub_nonneg.mpr ht.1)])
    have h := mul_le_mul (gain t ht) atten rawNonneg (by norm_num : (0 : ℝ) ≤ 13 / 5)
    have h₂ := mul_le_mul h a_coarse_bounds.2.le aPos (by norm_num : (0 : ℝ) ≤ 13 / 5 * (2 / 5))
    have h₃ := mul_le_mul h₂ expBound (Real.exp_pos _).le
      (by norm_num : (0 : ℝ) ≤ 13 / 5 * (2 / 5) * (7 / 5))
    refine ⟨errorTailDrive_nonnegative s 0 p (some origin) t, ?_⟩
    dsimp [forcing, errorTailDrive]
    linarith
  have reserve (t : ℝ) (ht : t ∈ Icc s.time T) :
      50 ≤ errorTailEnergy θ s 0 p (some origin) t ∧ errorTailEnergy θ s 0 p (some origin) t ≤ 100 := by
    apply reserve_of_derivative ht.1 (errorTailWork_continuous s 0 p (some origin))
      (errorTailEnergy_derivative s 0 p (some origin))
    · simpa [errorTailEnergy, linearConvolution_initial, relax_initial] using energy
    · intro v hv
      have hv' : v ∈ Icc s.time T := ⟨hv.1, hv.2.trans ht.2⟩
      have hf := forceBound v hv'
      have hm := mRange v hv'
      change 0 ≤ 9 * r * m v + forcing v ∧ 9 * r * m v + forcing v ≤ 500
      have hp := mul_nonneg rp.le (by linarith [hm.1] : 0 ≤ m v)
      have hb := mul_le_mul ru hm.2 (by linarith [hm.1] : 0 ≤ m v) (by norm_num : (0 : ℝ) ≤ 11)
      constructor <;> nlinarith [hf.1, hf.2]
  have chargeAt (t : ℝ) (ht : t ∈ Icc s.time T) :
      path t 0 .q ∈ Icc (1 / 10) (47 / 50) := by
    have hc := errorTailDrive_continuous (θ := θ) s 0 p (some origin)
    have upper := linearConvolution_le_mass hc (by norm_num : (0 : ℝ) ≤ 1 / 2) ht.1
      (fun v hv => (forceBound v ⟨hv.1, hv.2.trans ht.2⟩).1)
    have nonneg : 0 ≤ linearConvolution (1 / 2) forcing s.time t := by
      simpa [linearConvolution] using linearConvolution_mono (f := fun _ => 0)
        continuous_const hc (rate := 1 / 2) ht.1
        (fun v hv => (forceBound v ⟨hv.1, hv.2.trans ht.2⟩).1)
    have mass := intervalIntegral.integral_mono_on (μ := volume) ht.1
      (hc.intervalIntegrable s.time t) (intervalIntegrable_const (c := (42 / 25 : ℝ)))
      (fun v hv => (forceBound v ⟨hv.1, hv.2.trans ht.2⟩).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at mass
    have base := relax_mem_band (by norm_num : (0 : ℝ) ≤ 1 / 2) ht.1 charge
      (show (1 / 10 : ℝ) ∈ Icc (1 / 10) (217 / 250) by norm_num)
    change relax (1 / 2) (1 / 10) (s.x 0 .q) s.time t +
      linearConvolution (1 / 2) forcing s.time t ∈ Icc (1 / 10) (47 / 50)
    have elapsed : t - s.time ≤ 1 / 25 := by linarith [ht.2]
    constructor <;> linarith [base.1, base.2]
  have fieldEq (t : ℝ) (ht : t ∈ Ico s.time T) (i : Fin 1) (c : Coord) :
      field θ s (path t) t i c = rhs t i c := by
    have ht' : t ∈ Icc s.time T := ⟨ht.1, ht.2.le⟩
    rw [Subsingleton.elim i 0]
    apply error_path_field main aux (fun q h => (other q h).1) otherRaw
    · have live : origin ≤ t ∧ t < origin + 1 := ⟨by linarith [ht.1, window.1], ht.2⟩
      simp only [current, raw, pulse, ite_eq_left live, rawInputScale]
      have eq : Real.exp (-a * (s.time - origin)) * Real.exp (-a * (t - s.time)) =
          Real.exp (-a * (t - origin)) := by rw [← Real.exp_add]; congr 1; ring
      linear_combination -a * eq
    · linarith [(reserve t ht').1]
    · have h := (box.2 0 p).1.1
      change 4 * (1 - ε) ≤ (θ 0).cap p at h
      apply Real.exp_lt_exp.mp
      rw [Real.exp_log (box.cap_positive 0 p)]
      linarith [box.epsilon_bounds.2, gain t ht']
  let flow : Flow θ s (errorTailEnd θ s 0 p (some origin) T) := {
    positive := window.2
    path := path
    initial := errorTailValues_initial _ _ _ _
    final := rfl
    main_fixed := rfl
    aux_fixed := rfl
    raw_fixed := rfl
    queue_fixed := rfl
    continuous := fun i c => (continuous_iff_continuousAt.mpr fun t =>
      (errorTailValues_derivative (θ := θ) s 0 p (some origin) t i c).continuousAt).continuousOn
    integrable := by
      intro i c
      apply ((errorTailRhs_continuous (θ := θ) s 0 p (some origin) i c).intervalIntegrable _ _).congr_uIoo
      intro t ht
      change t ∈ uIoo s.time T at ht
      rw [uIoo_of_lt window.2] at ht
      exact (fieldEq t ⟨ht.1.le, ht.2⟩ i c).symm
    mark_integrable := by intro i q; rw [Subsingleton.elim i 0]; simp [markAct, main]
    integral_eq := by
      intro t ht i c
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun v _ => errorTailValues_derivative (θ := θ) s 0 p (some origin) v i c)
        ((errorTailRhs_continuous (θ := θ) s 0 p (some origin) i c).intervalIntegrable s.time t)
      rw [errorTailValues_initial] at h
      have eq : (∫ v in s.time..t, field θ s (path v) v i c) = ∫ v in s.time..t, rhs v i c := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht.1
        intro v hv
        exact fieldEq v ⟨hv.1.le, hv.2.trans_le ht.2⟩ i c
      rw [eq, h]
      change path t i c = _
      ring
    guards := by
      intro t ht
      constructor
      · intro i
        rw [Subsingleton.elim i 0, main]
        linarith [(chargeAt t ⟨ht.1, ht.2.le⟩).2]
      · intro i q
        rw [Subsingleton.elim i 0]
        by_cases h : q = p
        · subst q
          rw [aux]
          simp only [path, errorTailValues, and_self, ite_true]
          change (1 / 40 : ℝ) < m t
          linarith [(mRange t ⟨ht.1, ht.2.le⟩).1]
        · rw [(other q h).1]
          norm_num [path, errorTailValues, h, (other q h).2, relax]
    raw_support := by
      intro i q o h
      rw [Subsingleton.elim i 0] at h
      by_cases hq : q = p
      · subst q
        rw [raw, Option.some.injEq] at h
        subst o
        exact ⟨by linarith [window.1], le_rfl⟩
      · rw [otherRaw q hq] at h
        cases h
    pending_urgent := pending
  }
  refine ⟨⟨flow, main, aux, fun q h => (other q h).1, ?_, ?_, ?_, chargeAt T ⟨window.2.le, le_rfl⟩, reserve T ⟨window.2.le, le_rfl⟩⟩⟩
  · intro t ht
    change path t 0 .q < level
    linarith [(chargeAt t ⟨ht.1, ht.2.le⟩).2]
  · intro t ht
    change lower < path t 0 (.m p)
    simp only [path, errorTailValues, and_self, ite_true]
    change lower < m t
    linarith [(mRange t ⟨ht.1, ht.2.le⟩).1]
  · simp only [errorTailEnd, errorTailValues, and_self, ite_true]
    change lower < m T
    linarith [(mRange T ⟨window.2.le, le_rfl⟩).1]

end RecursiveLearning.Native
