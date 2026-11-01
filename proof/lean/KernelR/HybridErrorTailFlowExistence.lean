import KernelR.HybridReadyProtectedFlowExistence
import KernelR.HybridPhysicalInvariant
/-! ERROR with an optional still-active raw tail, including raw expiry endpoints. -/
namespace KernelR.Hybrid
open Set MeasureTheory

noncomputable def linearConvolution (rate : ℝ) (forcing : ℝ → ℝ) (start t : ℝ) : ℝ :=
  Real.exp (-rate * (t - start)) * ∫ v in start..t, Real.exp (rate * (v - start)) * forcing v

theorem linearConvolution_initial (rate : ℝ) (forcing : ℝ → ℝ) (start : ℝ) :
    linearConvolution rate forcing start start = 0 := by simp [linearConvolution]

theorem linearConvolution_derivative {forcing : ℝ → ℝ} (hf : Continuous forcing) (rate start t : ℝ) :
    HasDerivAt (linearConvolution rate forcing start)
      (forcing t - rate * linearConvolution rate forcing start t) t := by
  have hc : Continuous (fun v : ℝ => Real.exp (rate * (v - start)) * forcing v) := by fun_prop
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable start t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he := ((((hasDerivAt_id t).sub_const start).const_mul (-rate)).exp)
  have hexp : Real.exp (-rate * (t - start)) * Real.exp (rate * (t - start)) = 1 := by
    rw [← Real.exp_add]
    simp
  convert he.mul hi using 1
  · rfl
  · dsimp only [linearConvolution,id_eq]
    linear_combination -forcing t * hexp

@[fun_prop] theorem linearConvolution_continuous {forcing : ℝ → ℝ} (hf : Continuous forcing) (rate start : ℝ) :
    Continuous (linearConvolution rate forcing start) :=
  continuous_iff_continuousAt.mpr (fun t => (linearConvolution_derivative hf rate start t).continuousAt)

theorem linearConvolution_eq_integral (rate : ℝ) (forcing : ℝ → ℝ) (start t : ℝ) :
    linearConvolution rate forcing start t =
      ∫ v in start..t, Real.exp (-rate * (t - v)) * forcing v := by
  rw [linearConvolution,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  have he : Real.exp (-rate * (t - start)) * Real.exp (rate * (v - start)) =
      Real.exp (-rate * (t - v)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linear_combination forcing v * he

theorem linearConvolution_le_mass {forcing : ℝ → ℝ} (hf : Continuous forcing)
    {rate start t : ℝ} (hr : 0 ≤ rate) (ht : start ≤ t)
    (hpos : ∀ v ∈ Icc start t, 0 ≤ forcing v) :
    linearConvolution rate forcing start t ≤ ∫ v in start..t, forcing v := by
  rw [linearConvolution_eq_integral]
  apply intervalIntegral.integral_mono_on (μ := volume) ht (by
    apply Continuous.intervalIntegrable
    fun_prop) (hf.intervalIntegrable start t)
  intro v hv
  have hkernel : Real.exp (-rate * (t - v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hv.2])
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hkernel (hpos v hv)

theorem exp_rate_mass (rate start t : ℝ) :
    (∫ v in start..t, rate * Real.exp (-rate * (v - start))) = 1 - Real.exp (-rate * (t - start)) := by
  have hd (v : ℝ) : HasDerivAt (fun w : ℝ => -Real.exp (-rate * (w - start)))
      (rate * Real.exp (-rate * (v - start))) v := by
    have h := ((((hasDerivAt_id v).sub_const start).const_mul (-rate)).exp)
    convert h.neg using 1
    · rfl
    · dsimp only [id_eq]
      ring
  have hc : Continuous (fun v : ℝ => rate * Real.exp (-rate * (v - start))) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) (hc.intervalIntegrable start t)
  simpa [sub_eq_add_neg,add_comm] using h

noncomputable def errorTailSensor {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  s.x i (.m p) * Real.exp (-(θ i).le p * (t - s.time))

noncomputable def errorTailGain {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  s.x i (.z p) + 8 * (s.x i (.m p) - errorTailSensor θ s i p t)

noncomputable def errorTailDuration {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port) : ℝ :=
  Real.log (40 * s.x i (.m p)) / (θ i).le p

noncomputable def errorTailDrive {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (t : ℝ) : ℝ :=
  Real.exp (errorTailGain θ s i p t) * rawInputScale origin s.time * a * Real.exp (-a * (t - s.time))

noncomputable def errorTailWork {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (t : ℝ) : ℝ :=
  9 * (θ i).le p * errorTailSensor θ s i p t + errorTailDrive θ s i p origin t

theorem errorTailDuration_positive {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 1 / 40 < s.x i (.m p)) : 0 < errorTailDuration θ s i p :=
  div_pos (Real.log_pos (by linarith)) (hb.rates_positive i p).2.2

theorem errorTailSensor_endpoint {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 1 / 40 < s.x i (.m p)) :
    errorTailSensor θ s i p (s.time + errorTailDuration θ s i p) = 1 / 40 := by
  have hmpos : 0 < 40 * s.x i (.m p) := by linarith
  have hr := ne_of_gt (hb.rates_positive i p).2.2
  have hexp : -(θ i).le p * errorTailDuration θ s i p = -Real.log (40 * s.x i (.m p)) := by
    dsimp [errorTailDuration]
    field_simp [hr]
  simp only [errorTailSensor,add_sub_cancel_left,hexp,Real.exp_neg,Real.exp_log hmpos]
  field_simp

theorem errorTailSensor_floor {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 1 / 40 < s.x i (.m p)) {t : ℝ} (ht : t ≤ s.time + errorTailDuration θ s i p) :
    1 / 40 ≤ errorTailSensor θ s i p t := by
  rw [← errorTailSensor_endpoint hb s i p hm]
  apply mul_le_mul_of_nonneg_left ?_ (by linarith)
  apply Real.exp_le_exp.mpr
  simp only [add_sub_cancel_left]
  nlinarith [(hb.rates_positive i p).2.2]

theorem errorTailSensor_strict_floor {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 1 / 40 < s.x i (.m p)) {t : ℝ} (ht : t < s.time + errorTailDuration θ s i p) :
    1 / 40 < errorTailSensor θ s i p t := by
  rw [← errorTailSensor_endpoint hb s i p hm]
  apply mul_lt_mul_of_pos_left ?_ (by linarith)
  apply Real.exp_lt_exp.mpr
  simp only [add_sub_cancel_left]
  nlinarith [(hb.rates_positive i p).2.2]

theorem errorTailGain_headroom {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 1 / 40 < s.x i (.m p))
    (hh : s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p))
    {t : ℝ} (ht : t ≤ s.time + errorTailDuration θ s i p) :
    errorTailGain θ s i p t < Real.log ((θ i).cap p) := by
  have hfloor := errorTailSensor_floor hb s i p hm ht
  dsimp [errorTailGain]
  linarith

theorem errorTailDrive_continuous {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (origin : Option ℝ) :
    Continuous (errorTailDrive θ s i p origin) := by
  unfold errorTailDrive errorTailGain errorTailSensor
  fun_prop

theorem errorTailWork_continuous {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (origin : Option ℝ) :
    Continuous (errorTailWork θ s i p origin) := by
  have hc := errorTailDrive_continuous (θ := θ) s i p origin
  unfold errorTailWork errorTailSensor
  fun_prop

theorem rawInputScale_nonnegative (origin : Option ℝ) (start : ℝ) : 0 ≤ rawInputScale origin start := by
  cases origin <;> simp [rawInputScale,(Real.exp_pos _).le]

theorem errorTailDrive_nonnegative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (origin : Option ℝ) (t : ℝ) :
    0 ≤ errorTailDrive θ s i p origin t := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (rawInputScale_nonnegative origin s.time))
    (by linarith [a_coarse_bounds.1])) (Real.exp_pos _).le

theorem errorTailDrive_upper {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 1 / 40 < s.x i (.m p))
    (hh : s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p))
    (origin : Option ℝ) {t : ℝ} (ht : t ≤ s.time + errorTailDuration θ s i p) :
    errorTailDrive θ s i p origin t ≤ (22 / 5) * (rawInputScale origin s.time * a * Real.exp (-a * (t - s.time))) := by
  have hcap : (θ i).cap p ≤ (22 / 5 : ℝ) := by
    have h := (hb.2 i p).1.2
    nlinarith [hb.epsilon_bounds.2]
  have hexp : Real.exp (errorTailGain θ s i p t) ≤ 22 / 5 := by
    apply le_trans ?_ hcap
    calc
      _ ≤ Real.exp (Real.log ((θ i).cap p)) := Real.exp_le_exp.mpr (errorTailGain_headroom hb s i p hm hh ht).le
      _ = _ := Real.exp_log (hb.cap_positive i p)
  have hnon : 0 ≤ rawInputScale origin s.time * a * Real.exp (-a * (t - s.time)) :=
    mul_nonneg (mul_nonneg (rawInputScale_nonnegative _ _) (by linarith [a_coarse_bounds.1])) (Real.exp_pos _).le
  simpa only [errorTailDrive,mul_assoc] using mul_le_mul_of_nonneg_right hexp hnon

theorem errorTailRaw_mass {start t : ℝ} (origin : Option ℝ) (_ht : start ≤ t)
    (hsupport : ∀ o, origin = some o → o ≤ start ∧ t ≤ o + 1) :
    (∫ v in start..t, rawInputScale origin start * a * Real.exp (-a * (v - start))) ≤ 3 / 4 := by
  have hmass : (∫ v in start..t, rawInputScale origin start * a * Real.exp (-a * (v - start))) =
      rawInputScale origin start * (1 - Real.exp (-a * (t - start))) := by
    have h := congrArg (fun v => rawInputScale origin start * v) (exp_rate_mass a start t)
    simpa only [intervalIntegral.integral_const_mul,mul_assoc] using h
  rw [hmass]
  cases origin with
  | none => norm_num [rawInputScale]
  | some o =>
    obtain ⟨hstart,hend⟩ := hsupport o rfl
    have hscale : Real.exp (-a * (start - o)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [a_coarse_bounds.1])
    have htail : (1 / 4 : ℝ) ≤ Real.exp (-a * (t - o)) := by
      have he : Real.exp (-a) = 1 / 4 := by
        rw [Real.exp_neg]
        norm_num [a,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      rw [← he]
      apply Real.exp_le_exp.mpr
      nlinarith [a_coarse_bounds.1]
    have he : Real.exp (-a * (start - o)) * Real.exp (-a * (t - start)) = Real.exp (-a * (t - o)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [rawInputScale]
    nlinarith

theorem errorTailWork_nonnegative {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 1 / 40 < s.x i (.m p)) (origin : Option ℝ) (t : ℝ) :
    0 ≤ errorTailWork θ s i p origin t := by
  have hs : 0 ≤ errorTailSensor θ s i p t := mul_nonneg (by linarith) (Real.exp_pos _).le
  dsimp only [errorTailWork]
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hb.rates_positive i p).2.2.le) hs) (errorTailDrive_nonnegative s i p origin t)

theorem errorTailWork_mass {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 1 / 40 < s.x i (.m p)) (hupper : s.x i (.m p) ≤ 1 / 10)
    (hh : s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p))
    (origin : Option ℝ) {t : ℝ} (ht : s.time ≤ t) (hend : t ≤ s.time + errorTailDuration θ s i p)
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ t ≤ o + 1) :
    (∫ v in s.time..t, errorTailWork θ s i p origin v) ≤ 21 / 5 := by
  have hdrive : (∫ v in s.time..t, errorTailDrive θ s i p origin v) ≤ 33 / 10 := by
    have hc : Continuous (fun v : ℝ => (22 / 5) * (rawInputScale origin s.time * a * Real.exp (-a * (v - s.time)))) := by fun_prop
    have h := intervalIntegral.integral_mono_on (μ := volume) ht
      ((errorTailDrive_continuous (θ := θ) s i p origin).intervalIntegrable s.time t)
      (hc.intervalIntegrable s.time t) (fun v hv => errorTailDrive_upper hb s i p hm hh origin (hv.2.trans hend))
    rw [intervalIntegral.integral_const_mul] at h
    have hraw := errorTailRaw_mass origin ht hsupport
    linarith
  have herror : (∫ v in s.time..t, 9 * (θ i).le p * errorTailSensor θ s i p v) ≤ 9 / 10 := by
    have hmass : (∫ v in s.time..t, 9 * (θ i).le p * errorTailSensor θ s i p v) =
        9 * s.x i (.m p) * (1 - Real.exp (-(θ i).le p * (t - s.time))) := by
      have h := congrArg (fun v => 9 * s.x i (.m p) * v) (exp_rate_mass ((θ i).le p) s.time t)
      simpa [errorTailSensor,intervalIntegral.integral_const_mul,mul_assoc,mul_left_comm,mul_comm] using h
    rw [hmass]
    have hnon := (Real.exp_pos (-(θ i).le p * (t - s.time))).le
    nlinarith
  have hc₁ : Continuous (fun v : ℝ => 9 * (θ i).le p * errorTailSensor θ s i p v) := by unfold errorTailSensor; fun_prop
  rw [show (fun v => errorTailWork θ s i p origin v) =
      (fun v => 9 * (θ i).le p * errorTailSensor θ s i p v + errorTailDrive θ s i p origin v) by rfl,
    intervalIntegral.integral_add (hc₁.intervalIntegrable s.time t)
      ((errorTailDrive_continuous (θ := θ) s i p origin).intervalIntegrable s.time t)]
  linarith

noncomputable def errorTailMain {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (t : ℝ) : ℝ :=
  relax (1 / 2) (1 / 10) (s.x i .q) s.time t +
    linearConvolution (1 / 2) (errorTailDrive θ s i p origin) s.time t

noncomputable def errorTailEnergy {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (t : ℝ) : ℝ :=
  relax 10 100 (s.x i .energy) s.time t - linearConvolution 10 (errorTailWork θ s i p origin) s.time t

theorem errorTailEnergy_positive {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 1 / 40 < s.x i (.m p)) (hupper : s.x i (.m p) ≤ 1 / 10)
    (hh : s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p))
    (he : 50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100)
    (origin : Option ℝ) {t : ℝ} (ht : s.time ≤ t) (hend : t ≤ s.time + errorTailDuration θ s i p)
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ t ≤ o + 1) :
    0 < errorTailEnergy θ s i p origin t := by
  have hexp : Real.exp (-10 * (t - s.time)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hcarry := mul_le_mul_of_nonpos_left hexp (sub_nonpos.mpr he.2)
  have hbase : 50 ≤ relax 10 100 (s.x i .energy) s.time t := by dsimp [relax]; nlinarith [he.1]
  have hconv := linearConvolution_le_mass (errorTailWork_continuous (θ := θ) s i p origin)
    (by norm_num : (0 : ℝ) ≤ 10) ht
    (fun v _ => errorTailWork_nonnegative hb s i p hm origin v)
  have hmass := errorTailWork_mass hb s i p hm hupper hh origin ht hend hsupport
  dsimp only [errorTailEnergy]
  linarith

theorem linearConvolution_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {rate start t : ℝ} (ht : start ≤ t) (hfg : ∀ v ∈ Icc start t, f v ≤ g v) :
    linearConvolution rate f start t ≤ linearConvolution rate g start t := by
  rw [linearConvolution_eq_integral,linearConvolution_eq_integral]
  apply intervalIntegral.integral_mono_on (μ := volume) ht
    (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)
  intro v hv
  exact mul_le_mul_of_nonneg_left (hfg v hv) (Real.exp_pos _).le

theorem linearConvolution_canonical {start t G : ℝ} (ht : start ≤ t) :
    linearConvolution (1 / 2) (fun v => G * a * Real.exp (-a * (v - start))) start t = G * response (t - start) := by
  let forcing : ℝ → ℝ := fun v => G * a * Real.exp (-a * (v - start))
  have hf : Continuous forcing := by dsimp [forcing]; fun_prop
  have hc₁ : ContinuousOn (linearConvolution (1 / 2) forcing start) (Icc start t) :=
    (linearConvolution_continuous hf (1 / 2) start).continuousOn
  have hc₂ : ContinuousOn (fun v => G * response (v - start)) (Icc start t) := by unfold response; fun_prop
  have hd₁ : ∀ x ∈ Ico start t, HasDerivWithinAt (linearConvolution (1 / 2) forcing start)
      (-(1 / 2) * linearConvolution (1 / 2) forcing start x + forcing x) (Ici x) x := by
    intro x hx
    exact ((linearConvolution_derivative hf (1 / 2) start x).congr_deriv (by ring)).hasDerivWithinAt
  have hd₂ : ∀ x ∈ Ico start t, HasDerivWithinAt (fun v => G * response (v - start))
      (-(1 / 2) * (G * response (x - start)) + forcing x) (Ici x) x := by
    intro x hx
    have hd := ((response_derivative (x - start)).comp x ((hasDerivAt_id x).sub_const start)).const_mul G
    exact (hd.congr_deriv (by dsimp [forcing]; ring)).hasDerivWithinAt
  exact linear_unique_of_right_derivatives hc₁ hc₂ hd₁ hd₂
    (by simp [linearConvolution_initial,response]) t ⟨ht,le_rfl⟩

/-- A physical cap bound controls the nonlinear gain-learning raw tail through
its explicit convolution, before any execution is available. -/
theorem errorTailMain_le_readyPulse {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 1 / 40 < s.x i (.m p))
    (hh : s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p))
    (origin : Option ℝ) {t : ℝ} (ht : s.time ≤ t) (hend : t ≤ s.time + errorTailDuration θ s i p) :
    errorTailMain θ s i p origin t ≤
      readyPulse (s.x i .q) ((22 / 5) * rawInputScale origin s.time) s.time t := by
  have hc : Continuous (fun v : ℝ => ((22 / 5) * rawInputScale origin s.time) * a * Real.exp (-a * (v - s.time))) := by fun_prop
  have hmono := linearConvolution_mono (rate := (1 / 2 : ℝ)) (errorTailDrive_continuous (θ := θ) s i p origin) hc ht
    (fun v hv => by simpa only [mul_assoc] using errorTailDrive_upper hb s i p hm hh origin (hv.2.trans hend))
  rw [linearConvolution_canonical ht] at hmono
  dsimp only [errorTailMain,readyPulse,relax]
  linarith

theorem errorTailSensor_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    HasDerivAt (errorTailSensor θ s i p) (-(θ i).le p * errorTailSensor θ s i p t) t := by
  have h := (((((hasDerivAt_id t).sub_const s.time).const_mul (-(θ i).le p)).exp).const_mul (s.x i (.m p)))
  convert h using 1
  · rfl
  · dsimp only [errorTailSensor,id_eq]
    ring

theorem errorTailGain_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    HasDerivAt (errorTailGain θ s i p) (8 * (θ i).le p * errorTailSensor θ s i p t) t := by
  exact ((((errorTailSensor_derivative (θ := θ) s i p t).const_sub (s.x i (.m p))).const_mul 8).const_add
    (s.x i (.z p))).congr_deriv (by ring)

theorem errorTailMain_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (origin : Option ℝ) (t : ℝ) :
    HasDerivAt (errorTailMain θ s i p origin)
      ((1 / 2) * (1 / 10 - errorTailMain θ s i p origin t) + errorTailDrive θ s i p origin t) t := by
  exact ((relax_derivative (1 / 2) (1 / 10) (s.x i .q) s.time t).add
    (linearConvolution_derivative (errorTailDrive_continuous (θ := θ) s i p origin) (1 / 2) s.time t)).congr_deriv
      (by dsimp only [errorTailMain]; ring)

theorem errorTailEnergy_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (origin : Option ℝ) (t : ℝ) :
    HasDerivAt (errorTailEnergy θ s i p origin)
      (10 * (100 - errorTailEnergy θ s i p origin t) - errorTailWork θ s i p origin t) t := by
  exact ((relax_derivative 10 100 (s.x i .energy) s.time t).sub
    (linearConvolution_derivative (errorTailWork_continuous (θ := θ) s i p origin) 10 s.time t)).congr_deriv
      (by dsimp only [errorTailEnergy]; ring)

noncomputable def errorTailValues {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (t : ℝ) : Values n := fun j c => match c with
  | .q => if j = i then errorTailMain θ s i p origin t else relax (1 / 2) (1 / 10) (s.x j .q) s.time t
  | .m q => if j = i ∧ q = p then errorTailSensor θ s i p t else relax (1 / 2) (1 / 40) (s.x j (.m q)) s.time t
  | .z q => if j = i ∧ q = p then errorTailGain θ s i p t else s.x j (.z q)
  | .b => s.x j .b
  | .energy => if j = i then errorTailEnergy θ s i p origin t else relax 10 100 (s.x j .energy) s.time t

noncomputable def errorTailEnd {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (T : ℝ) : Snapshot n :=
  {s with time := T, x := errorTailValues θ s i p origin T}

noncomputable def errorTailRhs {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (t : ℝ) (j : Fin n) : Coord → ℝ
  | .q => (1 / 2) * (1 / 10 - errorTailValues θ s i p origin t j .q) +
      if j = i then errorTailDrive θ s i p origin t else 0
  | .m q => if j = i ∧ q = p then -(θ i).le p * errorTailSensor θ s i p t
      else (1 / 2) * (1 / 40 - errorTailValues θ s i p origin t j (.m q))
  | .z q => if j = i ∧ q = p then 8 * (θ i).le p * errorTailSensor θ s i p t else 0
  | .b => 0
  | .energy => 10 * (100 - errorTailValues θ s i p origin t j .energy) -
      if j = i then errorTailWork θ s i p origin t else 0

theorem errorTailValues_initial {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (origin : Option ℝ) :
    errorTailValues θ s i p origin s.time = s.x := by
  funext j c
  cases c <;> simp [errorTailValues,errorTailMain,errorTailEnergy,errorTailGain,errorTailSensor,
    relax_initial,linearConvolution_initial]
  all_goals aesop

theorem errorTailValues_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (origin : Option ℝ)
    (t : ℝ) (j : Fin n) (c : Coord) :
    HasDerivAt (fun v => errorTailValues θ s i p origin v j c) (errorTailRhs θ s i p origin t j c) t := by
  cases c with
  | q =>
    by_cases hj : j = i
    · subst j
      simpa [errorTailValues,errorTailRhs] using errorTailMain_derivative (θ := θ) s i p origin t
    · simpa [errorTailValues,errorTailRhs,hj] using relax_derivative (1 / 2) (1 / 10) (s.x j .q) s.time t
  | m q =>
    by_cases h : j = i ∧ q = p
    · simpa [errorTailValues,errorTailRhs,h] using errorTailSensor_derivative (θ := θ) s i p t
    · simpa [errorTailValues,errorTailRhs,h] using relax_derivative (1 / 2) (1 / 40) (s.x j (.m q)) s.time t
  | z q =>
    by_cases h : j = i ∧ q = p
    · simpa [errorTailValues,errorTailRhs,h] using errorTailGain_derivative (θ := θ) s i p t
    · simpa [errorTailValues,errorTailRhs,h] using hasDerivAt_const t (s.x j (.z q))
  | b => exact hasDerivAt_const _ _
  | energy =>
    by_cases hj : j = i
    · subst j
      simpa [errorTailValues,errorTailRhs] using errorTailEnergy_derivative (θ := θ) s i p origin t
    · simpa [errorTailValues,errorTailRhs,hj] using relax_derivative 10 100 (s.x j .energy) s.time t

theorem errorTailRhs_continuous {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (origin : Option ℝ)
    (j : Fin n) (c : Coord) : Continuous (fun t => errorTailRhs θ s i p origin t j c) := by
  have hc₁ := errorTailDrive_continuous (θ := θ) s i p origin
  have hc₂ := errorTailWork_continuous (θ := θ) s i p origin
  cases c <;> simp only [errorTailRhs,errorTailValues,errorTailMain,errorTailEnergy,errorTailSensor,relax]
  all_goals (try split_ifs) <;> fun_prop

/-- The variable gain is retained inside the raw drive; no frozen-gain pulse
formula is substituted for ERROR learning. -/
theorem errorTail_field {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (hm : ∀ j, s.main j = .ready) (ha : s.aux i p = .error)
    (hao : ∀ j q, j ≠ i ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw i p = origin) (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hm0 : 1 / 40 < s.x i (.m p)) (hmu : s.x i (.m p) ≤ 1 / 10)
    (he : 50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100)
    (hh : s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p))
    (t : ℝ) (ht : s.time ≤ t) (hend : t ≤ s.time + errorTailDuration θ s i p)
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ t < o + 1) (j : Fin n) (c : Coord) :
    field θ s (errorTailValues θ s i p origin t) t j c = errorTailRhs θ s i p origin t j c := by
  classical
  have hpower : 0 < errorTailEnergy θ s i p origin t :=
    errorTailEnergy_positive hb s i p hm0 hmu hh he origin ht hend
      (fun o h => ⟨(hsupport o h).1,(hsupport o h).2.le⟩)
  have hcap : errorTailGain θ s i p t < Real.log ((θ i).cap p) :=
    errorTailGain_headroom hb s i p hm0 hh hend
  have hc0 : current s i p t = rawInputScale origin s.time * a * Real.exp (-a * (t - s.time)) := by
    cases origin with
    | none => simp [current,hr,rawInputScale]
    | some o =>
      have hs := hsupport o rfl
      have hex : Real.exp (-a * (s.time - o)) * Real.exp (-a * (t - s.time)) = Real.exp (-a * (t - o)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      simp only [current,hr]
      unfold pulse
      rw [ite_eq_left ⟨hs.1.trans ht,hs.2⟩]
      change a * Real.exp (-a * (t - o)) = Real.exp (-a * (s.time - o)) * a * Real.exp (-a * (t - s.time))
      calc
        _ = a * (Real.exp (-a * (s.time - o)) * Real.exp (-a * (t - s.time))) := congrArg (fun v => a * v) hex.symm
        _ = _ := by ring
  have hcurrent (k : Fin n) (q : Port) : current s k q t =
      if k = i ∧ q = p then rawInputScale origin s.time * a * Real.exp (-a * (t - s.time)) else 0 := by
    by_cases h : k = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩; simpa using hc0
    · simp [current,ho k q (by tauto),h]
  have hsum (H : Port → ℝ) : (∑ q, H q * current s j q t) =
      if j = i then H p * rawInputScale origin s.time * a * Real.exp (-a * (t - s.time)) else 0 := by
    by_cases hj : j = i
    · simp [hcurrent,hj,mul_ite,mul_assoc]
    · simp [hcurrent,hj]
  have herror (q : Port) : errorAct θ s (errorTailValues θ s i p origin t) j q =
      if j = i ∧ q = p then 8 * (θ i).le p * errorTailSensor θ s i p t else 0 := by
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      simp [errorAct,ha,hm,hpower,hcap,errorTailValues]
    · have hother := hao j q (by tauto)
      simp [errorAct,hother,h]
  have hmark (q : Port) : markAct θ s (errorTailValues θ s i p origin t) j q = 0 := by simp [markAct,hm]
  have hdrain (q : Port) :
      (if s.aux j q = .ready then (θ j).inputGain q * current s j q t
        else auxDrain (θ j) (s.aux j q) q (errorTailValues θ s i p origin t j (.m q))) =
      if j = i ∧ q = p then (θ i).le p * errorTailSensor θ s i p t else 0 := by
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      simp [ha,auxDrain,errorTailValues]
    · have hother := hao j q (by tauto)
      simp [hother,hcurrent,h]
  have hsingle (H : ℝ) : (∑ q : Port, if j = i ∧ q = p then H else 0) = if j = i then H else 0 := by
    by_cases hj : j = i <;> simp [hj]
  cases c with
  | q =>
    simp only [field,hm,drive,hsum,errorTailRhs]
    by_cases hj : j = i <;> simp [hj,errorTailValues,errorTailDrive,mul_assoc]
  | m q =>
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      simp [field,ha,auxDrain,errorTailRhs,errorTailValues]
    · have hother := hao j q (by tauto)
      simp [field,hother,hcurrent,errorTailRhs,errorTailValues,h]
  | z q => simp [field,herror,errorTailRhs]
  | b => simp [field,hmark,errorTailRhs]
  | energy =>
    simp only [field,work,hm,drive,hsum,hdrain,herror,hmark,Finset.sum_const_zero,hsingle,errorTailRhs]
    by_cases hj : j = i <;> simp [hj,errorTailValues,errorTailWork,errorTailDrive,mul_assoc]
    ring

/-- Construct an ERROR span with its original raw tag still present. Raw
expiry may be exactly the endpoint; removing the tag requires a rawEnd jump.
The only supplied active main preguard concerns the explicit scalar formula. -/
noncomputable def errorTailFlow {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) {T : ℝ} (hT : s.time < T) (hend : T ≤ s.time + errorTailDuration θ s i p)
    (hm : ∀ j, s.main j = .ready) (ha : s.aux i p = .error)
    (hao : ∀ j q, j ≠ i ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw i p = origin) (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hm0 : 1 / 40 < s.x i (.m p)) (hmu : s.x i (.m p) ≤ 1 / 10)
    (he : 50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100)
    (hh : s.x i (.z p) + 8 * (s.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p))
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ T ≤ o + 1)
    (hq0 : ∀ j, s.x j .q < 1) (hx0 : ∀ j q, j ≠ i ∨ q ≠ p → s.x j (.m q) < 1)
    (hq : ∀ t ∈ Ico s.time T, errorTailMain θ s i p origin t < 1)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) : Flow θ s (errorTailEnd θ s i p origin T) where
  positive := hT
  path := errorTailValues θ s i p origin
  initial := errorTailValues_initial (θ := θ) s i p origin
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := by
    intro j c
    exact (continuous_iff_continuousAt.mpr (fun t =>
      (errorTailValues_derivative (θ := θ) s i p origin t j c).continuousAt)).continuousOn
  integrable := by
    intro j c
    apply ((errorTailRhs_continuous (θ := θ) s i p origin j c).intervalIntegrable s.time T).congr_uIoo
    intro t ht
    rw [uIoo_of_lt hT] at ht
    exact (errorTail_field hb s i p origin hm ha hao hr ho hm0 hmu he hh t ht.1.le
      (ht.2.le.trans hend) (fun o h => ⟨(hsupport o h).1,ht.2.trans_le (hsupport o h).2⟩) j c).symm
  mark_integrable := by
    intro j q
    simp only [markAct,hm,ne_eq,not_true_eq_false,and_false,false_and,ite_false]
    exact intervalIntegrable_const
  integral_eq := by
    intro t ht j c
    have hode := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => errorTailValues_derivative (θ := θ) s i p origin v j c)
      ((errorTailRhs_continuous (θ := θ) s i p origin j c).intervalIntegrable s.time t)
    rw [errorTailValues_initial] at hode
    have hfield : (∫ v in s.time..t, field θ s (errorTailValues θ s i p origin v) v j c) =
        ∫ v in s.time..t, errorTailRhs θ s i p origin v j c := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro v hv
      exact errorTail_field hb s i p origin hm ha hao hr ho hm0 hmu he hh v hv.1.le
        ((hv.2.le.trans ht.2).trans hend)
        (fun o h => ⟨(hsupport o h).1,(hv.2.trans_le ht.2).trans_le (hsupport o h).2⟩) j c
    rw [hfield]
    linarith
  guards := by
    intro t ht
    constructor
    · intro j
      simp only [hm,errorTailValues]
      by_cases hj : j = i
      · subst j
        simpa using hq t ht
      · rw [ite_eq_right hj]
        exact relax_lt (by norm_num) ht.1 (hq0 j) (by norm_num)
    · intro j q
      by_cases h : j = i ∧ q = p
      · rcases h with ⟨rfl,rfl⟩
        simpa [ha,errorTailValues] using errorTailSensor_strict_floor hb s _ _ hm0 (ht.2.trans_le hend)
      · have hne : j ≠ i ∨ q ≠ p := by tauto
        simpa [hao j q hne,errorTailValues,h] using relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2)
          ht.1 (hx0 j q hne) (by norm_num : (1 / 40 : ℝ) < 1)
  raw_support := by
    intro j q o hactive
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      exact hsupport o (hr.symm.trans hactive)
    · rw [ho j q (by tauto)] at hactive
      contradiction
  pending_urgent := hp

end KernelR.Hybrid
