import KernelR.HybridReadyFlowExistence

/-! Explicit MARK/SILENT flows while every main cell remains READY. Raw may
retain an older origin or be absent; even raw expiry is a legal endpoint. -/
namespace KernelR.Hybrid
open Set MeasureTheory

noncomputable def energyConvolution (rate start t : ℝ) : ℝ :=
  if rate = 10 then (t - start) * Real.exp (-10 * (t - start)) else
    (Real.exp (-rate * (t - start)) - Real.exp (-10 * (t - start))) / (10 - rate)

theorem energyConvolution_initial (rate start : ℝ) : energyConvolution rate start start = 0 := by
  simp [energyConvolution]

theorem energyConvolution_derivative (rate start t : ℝ) :
    HasDerivAt (energyConvolution rate start)
      (Real.exp (-rate * (t - start)) - 10 * energyConvolution rate start t) t := by
  by_cases h : rate = 10
  · subst rate
    convert ((hasDerivAt_id t).sub_const start).mul
      ((((hasDerivAt_id t).sub_const start).const_mul (-10)).exp) using 1
    · funext x; simp [energyConvolution]
    · simp [energyConvolution]
      ring
  · have hn : (10 : ℝ) - rate ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    convert (((((hasDerivAt_id t).sub_const start).const_mul (-rate)).exp).sub
      ((((hasDerivAt_id t).sub_const start).const_mul (-10)).exp)).div_const (10 - rate) using 1
    · funext x; simp only [energyConvolution,ite_eq_right h,Pi.sub_apply,id_eq]
    · simp only [energyConvolution,ite_eq_right h,id_eq]
      field_simp [hn]
      ring

noncomputable def twoForcingEnergy (initial coeff1 rate1 coeff2 rate2 start t : ℝ) : ℝ :=
  relax 10 100 initial start t - coeff1 * energyConvolution rate1 start t -
    coeff2 * energyConvolution rate2 start t

theorem twoForcingEnergy_initial (initial coeff1 rate1 coeff2 rate2 start : ℝ) :
    twoForcingEnergy initial coeff1 rate1 coeff2 rate2 start start = initial := by
  simp [twoForcingEnergy,relax_initial,energyConvolution_initial]

theorem twoForcingEnergy_derivative (initial coeff1 rate1 coeff2 rate2 start t : ℝ) :
    HasDerivAt (twoForcingEnergy initial coeff1 rate1 coeff2 rate2 start)
      (10 * (100 - twoForcingEnergy initial coeff1 rate1 coeff2 rate2 start t) -
        coeff1 * Real.exp (-rate1 * (t - start)) - coeff2 * Real.exp (-rate2 * (t - start))) t := by
  exact (((relax_derivative 10 100 initial start t).sub
    ((energyConvolution_derivative rate1 start t).const_mul coeff1)).sub
    ((energyConvolution_derivative rate2 start t).const_mul coeff2)).congr_deriv
      (by dsimp [twoForcingEnergy]; ring)

noncomputable def rawInputScale (origin : Option ℝ) (start : ℝ) : ℝ :=
  match origin with | none => 0 | some o => Real.exp (-a * (start - o))

def protectedReadyRate (θ : Parameters) (p : Port) : AuxMode → ℝ
  | .ready => 0 | .mark => θ.lm p | .silent => θ.ls p | .error => θ.le p

noncomputable def protectedRawAmplitude {n} (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : Option ℝ) (j : Fin n) : ℝ :=
  if j = i then Real.exp (s.x i (.z p)) * rawInputScale origin s.time else 0

noncomputable def protectedAuxCoeff {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (mode : AuxMode) (j : Fin n) : ℝ :=
  if j = i then protectedReadyRate (θ i) p mode * s.x i (.m p) else 0

noncomputable def readyProtectedValues {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (mode : AuxMode) (origin : Option ℝ) (t : ℝ) : Values n := fun j c => match c with
  | .q => readyPulse (s.x j .q) (protectedRawAmplitude s i p origin j) s.time t
  | .m q => if j = i ∧ q = p then s.x i (.m p) * Real.exp (-protectedReadyRate (θ i) p mode * (t - s.time))
      else relax (1 / 2) (1 / 40) (s.x j (.m q)) s.time t
  | .z q => s.x j (.z q)
  | .b => s.x j .b
  | .energy => twoForcingEnergy (s.x j .energy) (protectedRawAmplitude s i p origin j * a) a
      (protectedAuxCoeff θ s i p mode j) (protectedReadyRate (θ i) p mode) s.time t

noncomputable def readyProtectedEnd {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (mode : AuxMode) (origin : Option ℝ) (T : ℝ) : Snapshot n :=
  {s with time := T, x := readyProtectedValues θ s i p mode origin T}

noncomputable def readyProtectedRhs {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (mode : AuxMode) (origin : Option ℝ) (t : ℝ) (j : Fin n) : Coord → ℝ
  | .q => (1 / 2) * (1 / 10 - readyProtectedValues θ s i p mode origin t j .q) +
      protectedRawAmplitude s i p origin j * a * Real.exp (-a * (t - s.time))
  | .m q => if j = i ∧ q = p then
      -protectedReadyRate (θ i) p mode * readyProtectedValues θ s i p mode origin t j (.m q)
      else (1 / 2) * (1 / 40 - readyProtectedValues θ s i p mode origin t j (.m q))
  | .z _ => 0
  | .b => 0
  | .energy => 10 * (100 - readyProtectedValues θ s i p mode origin t j .energy) -
      protectedRawAmplitude s i p origin j * a * Real.exp (-a * (t - s.time)) -
      protectedAuxCoeff θ s i p mode j * Real.exp (-protectedReadyRate (θ i) p mode * (t - s.time))

theorem readyProtectedValues_initial {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (mode origin) :
    readyProtectedValues θ s i p mode origin s.time = s.x := by
  funext j c
  cases c <;> simp [readyProtectedValues,readyPulse_initial,twoForcingEnergy_initial,relax_initial]
  intro hj hq
  rw [hj,hq]

theorem readyProtectedValues_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (mode origin)
    (t : ℝ) (j : Fin n) (c : Coord) :
    HasDerivAt (fun v => readyProtectedValues θ s i p mode origin v j c)
      (readyProtectedRhs θ s i p mode origin t j c) t := by
  cases c with
  | q => exact readyPulse_derivative _ _ _ _
  | m q =>
    by_cases h : j = i ∧ q = p
    · simp only [readyProtectedValues,readyProtectedRhs,h]
      convert (((((hasDerivAt_id t).sub_const s.time).const_mul (-protectedReadyRate (θ i) p mode)).exp).const_mul
        (s.x i (.m p))) using 1 <;> dsimp; ring
    · simpa only [readyProtectedValues,readyProtectedRhs,h,ite_false] using
        relax_derivative (1 / 2) (1 / 40) (s.x j (.m q)) s.time t
  | z q => exact hasDerivAt_const _ _
  | b => exact hasDerivAt_const _ _
  | energy => exact twoForcingEnergy_derivative _ _ _ _ _ _ _

theorem readyProtectedRhs_continuous {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (mode origin)
    (j : Fin n) (c : Coord) : Continuous (fun t => readyProtectedRhs θ s i p mode origin t j c) := by
  cases c <;> simp only [readyProtectedRhs,readyProtectedValues,readyPulse,twoForcingEnergy,energyConvolution,relax,response]
  all_goals (try split_ifs) <;> fun_prop

/-- The two learning gates are closed by the actual READY main and non-ERROR
auxiliary modes. Raw support is retained at its original date. -/
theorem readyProtected_field {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (mode origin)
    (hmode : mode = .mark ∨ mode = .silent)
    (hm : ∀ j, s.main j = .ready) (ha : s.aux i p = mode)
    (hao : ∀ j q, j ≠ i ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw i p = origin) (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (t : ℝ) (ht : s.time ≤ t)
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ t < o + 1) (j : Fin n) (c : Coord) :
    field θ s (readyProtectedValues θ s i p mode origin t) t j c =
      readyProtectedRhs θ s i p mode origin t j c := by
  classical
  have haux (k : Fin n) (q : Port) : s.aux k q = if k = i ∧ q = p then mode else .ready := by
    by_cases h : k = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩; simpa using ha
    · rw [ite_eq_right h]; exact hao k q (by tauto)
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
  have he (q : Port) : errorAct θ s (readyProtectedValues θ s i p mode origin t) j q = 0 := by
    by_cases h : j = i ∧ q = p
    · rcases hmode with rfl | rfl <;> simp [errorAct,haux,h]
    · simp [errorAct,haux,h]
  have hb (q : Port) : markAct θ s (readyProtectedValues θ s i p mode origin t) j q = 0 := by simp [markAct,hm]
  have hauxWork (q : Port) : (if s.aux j q = .ready then (θ j).inputGain q * current s j q t
      else auxDrain (θ j) (s.aux j q) q (readyProtectedValues θ s i p mode origin t j (.m q))) =
      if j = i ∧ q = p then protectedReadyRate (θ i) p mode * s.x i (.m p) *
        Real.exp (-protectedReadyRate (θ i) p mode * (t - s.time)) else 0 := by
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      rcases hmode with rfl | rfl <;> simp [haux,readyProtectedValues,protectedReadyRate,auxDrain,mul_assoc]
    · simp [haux,hcurrent,h]
  cases c with
  | q =>
    simp only [field,hm,drive,hsum,readyProtectedRhs]
    by_cases hj : j = i <;> simp [protectedRawAmplitude,hj,readyProtectedValues,mul_assoc]
  | m q =>
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      rcases hmode with rfl | rfl <;> simp [field,haux,auxDrain,protectedReadyRate,readyProtectedValues,readyProtectedRhs]
    · simp [field,haux,hcurrent,readyProtectedValues,readyProtectedRhs,h]
  | z q => simp [field,he,readyProtectedRhs]
  | b => simp [field,hb,readyProtectedRhs]
  | energy =>
    simp only [field,work,hm,drive,hsum,hauxWork,he,hb,Finset.sum_const_zero,readyProtectedRhs]
    by_cases hj : j = i <;> simp [hj,protectedRawAmplitude,protectedAuxCoeff,readyProtectedValues,mul_assoc]
    ring

/-- No raw tag is removed by this constructor. At expiry the final tag is
still present, and a separate genuine rawEnd jump must consume it. -/
noncomputable def readyProtectedFlow {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (mode : AuxMode) (origin : Option ℝ) {T : ℝ}
    (hT : s.time < T) (hmode : mode = .mark ∨ mode = .silent)
    (hm : ∀ j, s.main j = .ready) (ha : s.aux i p = mode)
    (hao : ∀ j q, j ≠ i ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw i p = origin) (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ T ≤ o + 1)
    (hq0 : ∀ j, s.x j .q < 1)
    (hm0 : ∀ j q, j ≠ i ∨ q ≠ p → s.x j (.m q) < 1)
    (hq : ∀ t ∈ Ico s.time T, readyPulse (s.x i .q)
      (Real.exp (s.x i (.z p)) * rawInputScale origin s.time) s.time t < 1)
    (hx : ∀ t ∈ Ico s.time T, (if mode = .mark then (4 / 5 : ℝ) else 1 / 10) <
      s.x i (.m p) * Real.exp (-protectedReadyRate (θ i) p mode * (t - s.time)))
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    Flow θ s (readyProtectedEnd θ s i p mode origin T) where
  positive := hT
  path := readyProtectedValues θ s i p mode origin
  initial := readyProtectedValues_initial (θ := θ) s i p mode origin
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := by
    intro j c
    exact (continuous_iff_continuousAt.mpr (fun t =>
      (readyProtectedValues_derivative (θ := θ) s i p mode origin t j c).continuousAt)).continuousOn
  integrable := by
    intro j c
    apply ((readyProtectedRhs_continuous (θ := θ) s i p mode origin j c).intervalIntegrable s.time T).congr_uIoo
    intro t ht
    rw [uIoo_of_lt hT] at ht
    exact (readyProtected_field s i p mode origin hmode hm ha hao hr ho t ht.1.le
      (fun o he => ⟨(hsupport o he).1,ht.2.trans_le (hsupport o he).2⟩) j c).symm
  mark_integrable := by
    intro j q
    simp only [markAct,hm,ne_eq,not_true_eq_false,and_false,false_and,ite_false]
    exact intervalIntegrable_const
  integral_eq := by
    intro t ht j c
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => readyProtectedValues_derivative (θ := θ) s i p mode origin v j c)
      ((readyProtectedRhs_continuous (θ := θ) s i p mode origin j c).intervalIntegrable s.time t)
    rw [readyProtectedValues_initial] at he
    have hi : (∫ v in s.time..t, field θ s (readyProtectedValues θ s i p mode origin v) v j c) =
        ∫ v in s.time..t, readyProtectedRhs θ s i p mode origin v j c := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro v hv
      exact readyProtected_field s i p mode origin hmode hm ha hao hr ho v hv.1.le
        (fun o h => ⟨(hsupport o h).1,(hv.2.trans_le ht.2).trans_le (hsupport o h).2⟩) j c
    rw [hi]
    linarith
  guards := by
    intro t ht
    constructor
    · intro j
      simp only [hm,readyProtectedValues]
      by_cases hj : j = i
      · subst j
        simpa [protectedRawAmplitude] using hq t ht
      · rw [protectedRawAmplitude,ite_eq_right hj,readyPulse_zero_eq_relax]
        exact relax_lt (by norm_num) ht.1 (hq0 j) (by norm_num)
    · intro j q
      by_cases h : j = i ∧ q = p
      · rcases h with ⟨rfl,rfl⟩
        rcases hmode with rfl | rfl <;> simpa [ha,readyProtectedValues] using hx t ht
      · rw [hao j q (by tauto)]
        simpa [readyProtectedValues,h] using
          (relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2) ht.1 (hm0 j q (by tauto)) (by norm_num : (1 / 40 : ℝ) < 1))
  raw_support := by
    intro j q o hactive
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      exact hsupport o (hr.symm.trans hactive)
    · rw [ho j q (by tauto)] at hactive
      contradiction
  pending_urgent := hp

end KernelR.Hybrid
