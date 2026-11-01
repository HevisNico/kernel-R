import KernelR.HybridErrorTailFlowExistence
import KernelR.HybridStableMemory
/-! Construct SLOW/MARK learning with the recovery change inside the main ODE. -/
namespace KernelR.Hybrid
open Set MeasureTheory

noncomputable def slowMarkSensor {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  s.x i (.m p) * Real.exp (-(θ i).lm p * (t - s.time))

noncomputable def slowMarkRecovery {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  s.x i .b + (1 / 2) * (s.x i (.m p) - slowMarkSensor θ s i p t)

noncomputable def slowMarkIntegral {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  s.x i .b * (t - s.time) + (1 / 2) * s.x i (.m p) *
    ((t - s.time) - (1 - Real.exp (-(θ i).lm p * (t - s.time))) / (θ i).lm p)

noncomputable def slowMarkMain {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  s.x i .q * Real.exp (-slowMarkIntegral θ s i p t)

noncomputable def slowMarkDuration {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port) : ℝ :=
  Real.log (s.x i (.m p) / (4 / 5)) / (θ i).lm p

noncomputable def slowMarkWork {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  11 / 10 + (3 / 2) * (θ i).lm p * slowMarkSensor θ s i p t

noncomputable def slowMarkEnergy {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  relax 10 100 (s.x i .energy) s.time t - linearConvolution 10 (slowMarkWork θ s i p) s.time t

theorem slowMarkSensor_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    HasDerivAt (slowMarkSensor θ s i p) (-(θ i).lm p * slowMarkSensor θ s i p t) t := by
  have h := (((((hasDerivAt_id t).sub_const s.time).const_mul (-(θ i).lm p)).exp).const_mul (s.x i (.m p)))
  convert h using 1
  · rfl
  · dsimp only [slowMarkSensor,id_eq]
    ring

theorem slowMarkRecovery_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    HasDerivAt (slowMarkRecovery θ s i p) ((1 / 2) * (θ i).lm p * slowMarkSensor θ s i p t) t := by
  exact ((((slowMarkSensor_derivative (θ := θ) s i p t).const_sub (s.x i (.m p))).const_mul (1 / 2)).const_add
    (s.x i .b)).congr_deriv (by ring)

theorem slowMarkIntegral_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ)
    (hr : (θ i).lm p ≠ 0) :
    HasDerivAt (slowMarkIntegral θ s i p) (slowMarkRecovery θ s i p t) t := by
  have hd := (hasDerivAt_id t).sub_const s.time
  have he := ((hd.const_mul (-(θ i).lm p)).exp)
  have h := (hd.const_mul (s.x i .b)).add
    ((hd.sub ((he.const_sub 1).div_const ((θ i).lm p))).const_mul ((1 / 2) * s.x i (.m p)))
  convert h using 1
  · rfl
  · dsimp only [slowMarkRecovery,slowMarkSensor,id_eq]
    field_simp [hr]

theorem slowMarkMain_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ)
    (hr : (θ i).lm p ≠ 0) :
    HasDerivAt (slowMarkMain θ s i p) (-slowMarkRecovery θ s i p t * slowMarkMain θ s i p t) t := by
  exact (((slowMarkIntegral_derivative (θ := θ) s i p t hr).neg.exp).const_mul (s.x i .q)).congr_deriv
    (by dsimp only [slowMarkMain,Pi.neg_apply]; ring)

@[fun_prop] theorem slowMarkWork_continuous {n θ} (s : Snapshot n) (i : Fin n) (p : Port) :
    Continuous (slowMarkWork θ s i p) := by unfold slowMarkWork slowMarkSensor; fun_prop

theorem slowMarkEnergy_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    HasDerivAt (slowMarkEnergy θ s i p)
      (10 * (100 - slowMarkEnergy θ s i p t) - slowMarkWork θ s i p t) t := by
  exact ((relax_derivative 10 100 (s.x i .energy) s.time t).sub
    (linearConvolution_derivative (slowMarkWork_continuous (θ := θ) s i p) 10 s.time t)).congr_deriv
      (by dsimp only [slowMarkEnergy]; ring)

theorem slowMarkDuration_positive {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 4 / 5 < s.x i (.m p)) : 0 < slowMarkDuration θ s i p :=
  div_pos (Real.log_pos ((lt_div_iff₀ (by norm_num : (0 : ℝ) < 4 / 5)).mpr (by linarith)))
    (hb.rates_positive i p).1

theorem slowMarkDuration_upper {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 4 / 5 < s.x i (.m p)) (hu : s.x i (.m p) ≤ 1) : slowMarkDuration θ s i p ≤ 1 / 45 := by
  have hlog : Real.log (s.x i (.m p) / (4 / 5)) ≤ Real.log (5 / 4 : ℝ) := by
    apply Real.log_le_log (div_pos (by linarith) (by norm_num))
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4 / 5)).mpr
    linarith
  exact (div_le_div_of_nonneg_right hlog (hb.rates_positive i p).1.le).trans (hb.mark_duration_upper i p)

theorem slowMarkSensor_endpoint {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 4 / 5 < s.x i (.m p)) :
    slowMarkSensor θ s i p (s.time + slowMarkDuration θ s i p) = 4 / 5 := by
  have hmpos : 0 < s.x i (.m p) / (4 / 5) := div_pos (by linarith) (by norm_num)
  have hr := ne_of_gt (hb.rates_positive i p).1
  have hexp : -(θ i).lm p * slowMarkDuration θ s i p = -Real.log (s.x i (.m p) / (4 / 5)) := by
    dsimp [slowMarkDuration]
    field_simp [hr]
  simp only [slowMarkSensor,add_sub_cancel_left,hexp,Real.exp_neg,Real.exp_log hmpos]
  field_simp

theorem slowMarkSensor_floor {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 4 / 5 < s.x i (.m p)) {t : ℝ} (ht : t ≤ s.time + slowMarkDuration θ s i p) :
    4 / 5 ≤ slowMarkSensor θ s i p t := by
  rw [← slowMarkSensor_endpoint hb s i p hm]
  apply mul_le_mul_of_nonneg_left ?_ (by linarith)
  apply Real.exp_le_exp.mpr
  simp only [add_sub_cancel_left]
  nlinarith [(hb.rates_positive i p).1]

theorem slowMarkSensor_strict_floor {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 4 / 5 < s.x i (.m p)) {t : ℝ} (ht : t < s.time + slowMarkDuration θ s i p) :
    4 / 5 < slowMarkSensor θ s i p t := by
  rw [← slowMarkSensor_endpoint hb s i p hm]
  apply mul_lt_mul_of_pos_left ?_ (by linarith)
  apply Real.exp_lt_exp.mpr
  simp only [add_sub_cancel_left]
  nlinarith [(hb.rates_positive i p).1]

theorem slowMarkRecovery_headroom {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 4 / 5 < s.x i (.m p)) (hh : s.x i .b + (1 / 2) * (s.x i (.m p) - 4 / 5) < 11 / 10)
    {t : ℝ} (ht : t ≤ s.time + slowMarkDuration θ s i p) : slowMarkRecovery θ s i p t < 11 / 10 := by
  have hfloor := slowMarkSensor_floor hb s i p hm ht
  dsimp only [slowMarkRecovery]
  linarith

theorem slowMarkWork_nonnegative {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 4 / 5 < s.x i (.m p)) (t : ℝ) : 0 ≤ slowMarkWork θ s i p t := by
  have hsensor : 0 ≤ slowMarkSensor θ s i p t := mul_nonneg (by linarith) (Real.exp_pos _).le
  dsimp only [slowMarkWork]
  exact add_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) (hb.rates_positive i p).1.le) hsensor)

theorem slowMarkWork_mass {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 4 / 5 < s.x i (.m p)) (hu : s.x i (.m p) ≤ 1)
    {t : ℝ} (_ht : s.time ≤ t) (hend : t ≤ s.time + slowMarkDuration θ s i p) :
    (∫ v in s.time..t, slowMarkWork θ s i p v) ≤ 1 / 3 := by
  have hmass : (∫ v in s.time..t, (3 / 2) * (θ i).lm p * slowMarkSensor θ s i p v) =
      (3 / 2) * (s.x i (.m p) - slowMarkSensor θ s i p t) := by
    have h := congrArg (fun v => (3 / 2) * s.x i (.m p) * v) (exp_rate_mass ((θ i).lm p) s.time t)
    simpa [slowMarkSensor,intervalIntegral.integral_const_mul,mul_assoc,mul_left_comm,mul_comm,mul_sub] using h
  have hc : Continuous (fun v : ℝ => (3 / 2) * (θ i).lm p * slowMarkSensor θ s i p v) := by unfold slowMarkSensor; fun_prop
  have htime : t - s.time ≤ 1 / 45 := by linarith [slowMarkDuration_upper hb s i p hm hu]
  have hfloor := slowMarkSensor_floor hb s i p hm hend
  have hsum : (∫ v in s.time..t, slowMarkWork θ s i p v) =
      (11 / 10) * (t - s.time) + (3 / 2) * (s.x i (.m p) - slowMarkSensor θ s i p t) := by
    rw [show (fun v => slowMarkWork θ s i p v) =
      (fun v => (11 / 10 : ℝ) + (3 / 2) * (θ i).lm p * slowMarkSensor θ s i p v) by rfl,
      intervalIntegral.integral_add intervalIntegrable_const (hc.intervalIntegrable s.time t),hmass]
    simp [intervalIntegral.integral_const,mul_comm]
    ring
  rw [hsum]
  linarith

theorem slowMarkEnergy_positive {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 4 / 5 < s.x i (.m p)) (hu : s.x i (.m p) ≤ 1)
    (he : 50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100)
    {t : ℝ} (ht : s.time ≤ t) (hend : t ≤ s.time + slowMarkDuration θ s i p) :
    0 < slowMarkEnergy θ s i p t := by
  have hexp : Real.exp (-10 * (t - s.time)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hcarry := mul_le_mul_of_nonpos_left hexp (sub_nonpos.mpr he.2)
  have hbase : 50 ≤ relax 10 100 (s.x i .energy) s.time t := by dsimp [relax]; nlinarith [he.1]
  have hconv := linearConvolution_le_mass (slowMarkWork_continuous (θ := θ) s i p)
    (by norm_num : (0 : ℝ) ≤ 10) ht (fun v _ => slowMarkWork_nonnegative hb s i p hm v)
  have hmass := slowMarkWork_mass hb s i p hm hu ht hend
  dsimp only [slowMarkEnergy]
  linarith

noncomputable def slowMarkValues {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : Values n :=
  fun j c => match c with
  | .q => if j = i then slowMarkMain θ s i p t else relax (1 / 2) (1 / 10) (s.x j .q) s.time t
  | .m q => if j = i ∧ q = p then slowMarkSensor θ s i p t else relax (1 / 2) (1 / 40) (s.x j (.m q)) s.time t
  | .z q => s.x j (.z q)
  | .b => if j = i then slowMarkRecovery θ s i p t else s.x j .b
  | .energy => if j = i then slowMarkEnergy θ s i p t else relax 10 100 (s.x j .energy) s.time t

noncomputable def slowMarkEnd {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port) (T : ℝ) : Snapshot n :=
  {s with time := T, x := slowMarkValues θ s i p T}

noncomputable def slowMarkRhs {n} (θ : Fin n → Parameters) (s : Snapshot n) (i : Fin n) (p : Port)
    (t : ℝ) (j : Fin n) : Coord → ℝ
  | .q => if j = i then -slowMarkRecovery θ s i p t * slowMarkMain θ s i p t
      else (1 / 2) * (1 / 10 - slowMarkValues θ s i p t j .q)
  | .m q => if j = i ∧ q = p then -(θ i).lm p * slowMarkSensor θ s i p t
      else (1 / 2) * (1 / 40 - slowMarkValues θ s i p t j (.m q))
  | .z _ => 0
  | .b => if j = i then (1 / 2) * (θ i).lm p * slowMarkSensor θ s i p t else 0
  | .energy => 10 * (100 - slowMarkValues θ s i p t j .energy) - if j = i then slowMarkWork θ s i p t else 0

theorem slowMarkValues_initial {n θ} (s : Snapshot n) (i : Fin n) (p : Port) :
    slowMarkValues θ s i p s.time = s.x := by
  funext j c
  cases c <;> simp [slowMarkValues,slowMarkMain,slowMarkIntegral,slowMarkRecovery,slowMarkSensor,
    slowMarkEnergy,relax_initial,linearConvolution_initial]
  all_goals aesop

theorem slowMarkValues_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (hr : (θ i).lm p ≠ 0) (t : ℝ) (j : Fin n) (c : Coord) :
    HasDerivAt (fun v => slowMarkValues θ s i p v j c) (slowMarkRhs θ s i p t j c) t := by
  cases c with
  | q =>
    by_cases hj : j = i
    · subst j
      simpa [slowMarkValues,slowMarkRhs] using slowMarkMain_derivative (θ := θ) s i p t hr
    · simpa [slowMarkValues,slowMarkRhs,hj] using relax_derivative (1 / 2) (1 / 10) (s.x j .q) s.time t
  | m q =>
    by_cases h : j = i ∧ q = p
    · simpa [slowMarkValues,slowMarkRhs,h] using slowMarkSensor_derivative (θ := θ) s i p t
    · simpa [slowMarkValues,slowMarkRhs,h] using relax_derivative (1 / 2) (1 / 40) (s.x j (.m q)) s.time t
  | z q => exact hasDerivAt_const _ _
  | b =>
    by_cases hj : j = i
    · subst j
      simpa [slowMarkValues,slowMarkRhs] using slowMarkRecovery_derivative (θ := θ) s i p t
    · simpa [slowMarkValues,slowMarkRhs,hj] using hasDerivAt_const t (s.x j .b)
  | energy =>
    by_cases hj : j = i
    · subst j
      simpa [slowMarkValues,slowMarkRhs] using slowMarkEnergy_derivative (θ := θ) s i p t
    · simpa [slowMarkValues,slowMarkRhs,hj] using relax_derivative 10 100 (s.x j .energy) s.time t

theorem slowMarkRhs_continuous {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (j : Fin n) (c : Coord) : Continuous (fun t => slowMarkRhs θ s i p t j c) := by
  have hc := slowMarkWork_continuous (θ := θ) s i p
  cases c <;> simp only [slowMarkRhs,slowMarkValues,slowMarkMain,slowMarkIntegral,slowMarkRecovery,
    slowMarkSensor,slowMarkEnergy,relax]
  all_goals (try split_ifs) <;> fun_prop

/-- The changing recovery acts inside SLOW's exponent. The actual MARK gate
opens by derived positive energy and initial recovery headroom. Active RAW
is irrelevant to this field, and is retained without an artificial expiry. -/
theorem slowMark_field {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : s.main i = .slow) (hmo : ∀ j, j ≠ i → s.main j = .ready)
    (ha : s.aux i p = .mark) (hao : ∀ j q, j ≠ i ∨ q ≠ p → s.aux j q = .ready)
    (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hm0 : 4 / 5 < s.x i (.m p)) (hmu : s.x i (.m p) ≤ 1)
    (he : 50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100)
    (hh : s.x i .b + (1 / 2) * (s.x i (.m p) - 4 / 5) < 11 / 10)
    (t : ℝ) (ht : s.time ≤ t) (hend : t ≤ s.time + slowMarkDuration θ s i p)
    (j : Fin n) (c : Coord) :
    field θ s (slowMarkValues θ s i p t) t j c = slowMarkRhs θ s i p t j c := by
  classical
  have hpower : 0 < slowMarkEnergy θ s i p t := slowMarkEnergy_positive hb s i p hm0 hmu he ht hend
  have hcap : slowMarkRecovery θ s i p t < 11 / 10 := slowMarkRecovery_headroom hb s i p hm0 hh hend
  have hcurrent (k : Fin n) (q : Port) (h : k ≠ i ∨ q ≠ p) : current s k q t = 0 := by simp [current,ho k q h]
  have hdrive (k : Fin n) (hk : k ≠ i) : drive s (slowMarkValues θ s i p t) k t = 0 := by
    simp [drive,hcurrent k _ (Or.inl hk)]
  have herror (q : Port) : errorAct θ s (slowMarkValues θ s i p t) j q = 0 := by
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      simp [errorAct,ha]
    · simp [errorAct,hao j q (by tauto)]
  have hmark (q : Port) : markAct θ s (slowMarkValues θ s i p t) j q =
      if j = i ∧ q = p then (1 / 2) * (θ i).lm p * slowMarkSensor θ s i p t else 0 := by
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      simp [markAct,ha,hm,hpower,hcap,slowMarkValues]
    · simp [markAct,hao j q (by tauto),h]
  have hdrain (q : Port) :
      (if s.aux j q = .ready then (θ j).inputGain q * current s j q t
        else auxDrain (θ j) (s.aux j q) q (slowMarkValues θ s i p t j (.m q))) =
      if j = i ∧ q = p then (θ i).lm p * slowMarkSensor θ s i p t else 0 := by
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      simp [ha,auxDrain,slowMarkValues]
    · simp [hao j q (by tauto),hcurrent j q (by tauto),h]
  have hsingle (H : ℝ) : (∑ q : Port, if j = i ∧ q = p then H else 0) = if j = i then H else 0 := by
    by_cases hj : j = i <;> simp [hj]
  cases c with
  | q =>
    by_cases hj : j = i
    · subst j
      simp [field,hm,slowMarkValues,slowMarkRhs]
    · simp [field,hmo j hj,hdrive j hj,slowMarkValues,slowMarkRhs,hj]
  | m q =>
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      simp [field,ha,auxDrain,slowMarkRhs,slowMarkValues]
    · simp [field,hao j q (by tauto),hcurrent j q (by tauto),slowMarkRhs,slowMarkValues,h]
  | z q => simp [field,herror,slowMarkRhs]
  | b => simp [field,hmark,hsingle,slowMarkRhs]
  | energy =>
    by_cases hj : j = i
    · subst j
      simp only [field,work,hm,hdrain,herror,hmark,Finset.sum_const_zero,slowMarkRhs]
      simp [slowMarkValues,slowMarkWork]
      ring
    · simp only [field,work,hmo j hj,hdrive j hj,hdrain,herror,hmark,Finset.sum_const_zero,hsingle,slowMarkRhs]
      simp [hj]

/-- A genuine integral SLOW/MARK flow. The supplied main preguard is an
inequality on the explicit scalar formula, not an assumed execution path. -/
noncomputable def slowMarkFlow {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) {T : ℝ} (hT : s.time < T) (hend : T ≤ s.time + slowMarkDuration θ s i p)
    (hm : s.main i = .slow) (hmo : ∀ j, j ≠ i → s.main j = .ready)
    (ha : s.aux i p = .mark) (hao : ∀ j q, j ≠ i ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw i p = origin) (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hm0 : 4 / 5 < s.x i (.m p)) (hmu : s.x i (.m p) ≤ 1)
    (he : 50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100)
    (hh : s.x i .b + (1 / 2) * (s.x i (.m p) - 4 / 5) < 11 / 10)
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ T ≤ o + 1)
    (hq0 : ∀ j, j ≠ i → s.x j .q < 1)
    (hx0 : ∀ j q, j ≠ i ∨ q ≠ p → s.x j (.m q) < 1)
    (hq : ∀ t ∈ Ico s.time T, 1 / 10 < slowMarkMain θ s i p t)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) : Flow θ s (slowMarkEnd θ s i p T) where
  positive := hT
  path := slowMarkValues θ s i p
  initial := slowMarkValues_initial (θ := θ) s i p
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := by
    intro j c
    exact (continuous_iff_continuousAt.mpr (fun t =>
      (slowMarkValues_derivative (θ := θ) s i p (ne_of_gt (hb.rates_positive i p).1) t j c).continuousAt)).continuousOn
  integrable := by
    intro j c
    have hc : ContinuousOn (fun t => field θ s (slowMarkValues θ s i p t) t j c) (Icc s.time T) := by
      apply (slowMarkRhs_continuous (θ := θ) s i p j c).continuousOn.congr
      intro t ht
      exact slowMark_field hb s i p hm hmo ha hao ho hm0 hmu he hh t ht.1 (ht.2.trans hend) j c
    exact hc.intervalIntegrable_of_Icc hT.le
  mark_integrable := by
    intro j q
    have hc : Continuous (fun t => if j = i ∧ q = p then (1 / 2) * (θ i).lm p * slowMarkSensor θ s i p t else 0) := by
      unfold slowMarkSensor
      split_ifs <;> fun_prop
    apply (hc.intervalIntegrable s.time T).congr_uIoo
    intro t ht
    rw [uIoo_of_lt hT] at ht
    have hpower := slowMarkEnergy_positive hb s i p hm0 hmu he ht.1.le (ht.2.le.trans hend)
    have hcap := slowMarkRecovery_headroom hb s i p hm0 hh (ht.2.le.trans hend)
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      simp [markAct,ha,hm,hpower,hcap,slowMarkValues]
    · simp [markAct,hao j q (by tauto),h]
  integral_eq := by
    intro t ht j c
    have hode := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => slowMarkValues_derivative (θ := θ) s i p (ne_of_gt (hb.rates_positive i p).1) v j c)
      ((slowMarkRhs_continuous (θ := θ) s i p j c).intervalIntegrable s.time t)
    rw [slowMarkValues_initial] at hode
    have hfield : (∫ v in s.time..t, field θ s (slowMarkValues θ s i p v) v j c) =
        ∫ v in s.time..t, slowMarkRhs θ s i p v j c := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro v hv
      exact slowMark_field hb s i p hm hmo ha hao ho hm0 hmu he hh v hv.1.le
        ((hv.2.le.trans ht.2).trans hend) j c
    rw [hfield]
    linarith
  guards := by
    intro t ht
    constructor
    · intro j
      by_cases hj : j = i
      · subst j
        simpa [hm,slowMarkValues] using hq t ht
      · simpa [hmo j hj,slowMarkValues,hj] using relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2)
          ht.1 (hq0 j hj) (by norm_num : (1 / 10 : ℝ) < 1)
    · intro j q
      by_cases h : j = i ∧ q = p
      · rcases h with ⟨rfl,rfl⟩
        simpa [ha,slowMarkValues] using slowMarkSensor_strict_floor hb s _ _ hm0 (ht.2.trans_le hend)
      · simpa [hao j q (by tauto),slowMarkValues,h] using relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2)
          ht.1 (hx0 j q (by tauto)) (by norm_num : (1 / 40 : ℝ) < 1)
  raw_support := by
    intro j q o hactive
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      exact hsupport o (hr.symm.trans hactive)
    · rw [ho j q (by tauto)] at hactive
      contradiction
  pending_urgent := hp

theorem slowMarkEnd_sensor {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 4 / 5 < s.x i (.m p)) :
    (slowMarkEnd θ s i p (s.time + slowMarkDuration θ s i p)).x i (.m p) = 4 / 5 := by
  simpa [slowMarkEnd,slowMarkValues] using slowMarkSensor_endpoint hb s i p hm

theorem slowMarkEnd_recovery {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 4 / 5 < s.x i (.m p)) :
    (slowMarkEnd θ s i p (s.time + slowMarkDuration θ s i p)).x i .b =
      s.x i .b + (1 / 2) * (s.x i (.m p) - 4 / 5) := by
  simp only [slowMarkEnd,slowMarkValues,ite_true,slowMarkRecovery]
  rw [slowMarkSensor_endpoint hb s i p hm]

theorem slowMarkEnd_gain_preserved {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (T : ℝ) (j : Fin n) (q : Port) :
    (slowMarkEnd θ s i p T).x j (.z q) = s.x j (.z q) := rfl

theorem slowMarkEnd_recovery_other {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (T : ℝ) (j : Fin n) (hj : j ≠ i) :
    (slowMarkEnd θ s i p T).x j .b = s.x j .b := by simp [slowMarkEnd,slowMarkValues,hj]

noncomputable def slowMarkEnd_silentJump {n θ ε route} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (ha : s.aux i p = .mark) (hm : 4 / 5 < s.x i (.m p)) :
    Jump route (slowMarkEnd θ s i p (s.time + slowMarkDuration θ s i p))
      (setAux (slowMarkEnd θ s i p (s.time + slowMarkDuration θ s i p)) i p .silent) :=
  .silent _ i p ha (slowMarkEnd_sensor hb s i p hm)

/-- The main guard can be checked from initial physical margins alone over
this short MARK span. No property of a desired trajectory is a premise. -/
theorem slowMarkMain_guard {n θ ε} (hb : @PhysicalBox n θ ε) (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : 4 / 5 < s.x i (.m p)) (hu : s.x i (.m p) ≤ 1)
    (hh : s.x i .b + (1 / 2) * (s.x i (.m p) - 4 / 5) < 11 / 10)
    (hq : 3 / 25 ≤ s.x i .q) {t : ℝ} (ht : s.time ≤ t) (hend : t ≤ s.time + slowMarkDuration θ s i p) :
    1 / 10 < slowMarkMain θ s i p t := by
  have hc : Continuous (slowMarkRecovery θ s i p) := by unfold slowMarkRecovery slowMarkSensor; fun_prop
  have hI : slowMarkIntegral θ s i p t = ∫ v in s.time..t, slowMarkRecovery θ s i p v := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => slowMarkIntegral_derivative (θ := θ) s i p v (ne_of_gt (hb.rates_positive i p).1))
      (hc.intervalIntegrable s.time t)
    simpa [slowMarkIntegral] using h.symm
  have hbound : slowMarkIntegral θ s i p t ≤ (11 / 10) * (t - s.time) := by
    rw [hI]
    have h := intervalIntegral.integral_mono_on (μ := volume) ht (hc.intervalIntegrable s.time t)
      (intervalIntegrable_const (c := (11 / 10 : ℝ)))
      (fun v hv => (slowMarkRecovery_headroom hb s i p hm hh (hv.2.trans hend)).le)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at h
    nlinarith
  have htime : t - s.time ≤ 1 / 45 := by linarith [slowMarkDuration_upper hb s i p hm hu]
  have hexp := Real.add_one_le_exp (-slowMarkIntegral θ s i p t)
  have hprod := mul_le_mul_of_nonneg_right hq (Real.exp_pos (-slowMarkIntegral θ s i p t)).le
  dsimp only [slowMarkMain]
  nlinarith

end KernelR.Hybrid
