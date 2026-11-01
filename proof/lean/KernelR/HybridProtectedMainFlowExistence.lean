import KernelR.HybridReadyProtectedFlowExistence

/-! Actual protected FAST/SLOW flows with a single optional raw origin. -/
namespace KernelR.Hybrid
open Set MeasureTheory

noncomputable def protectedMainRate {n} (s : Snapshot n) (i : Fin n) (mode : MainMode) : ℝ :=
  if mode = .fast then a else s.x i .b

noncomputable def protectedMainCoeff {n} (s : Snapshot n) (i : Fin n) (mode : MainMode) (j : Fin n) : ℝ :=
  if j = i then if mode = .fast then a * s.x i .q else 11 / 10 else 0

noncomputable def protectedMainEnergyRate {n} (_s : Snapshot n) (_i : Fin n) (mode : MainMode) : ℝ :=
  if mode = .fast then a else 0

noncomputable def protectedMainAuxCoeff {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (mode : AuxMode) (origin : Option ℝ) (j : Fin n) : ℝ :=
  if j = i then if mode = .ready then (θ i).inputGain p * rawInputScale origin s.time * a
    else protectedReadyRate (θ i) p mode * s.x i (.m p) else 0

noncomputable def protectedMainAuxRate (θ : Parameters) (p : Port) (mode : AuxMode) : ℝ :=
  if mode = .ready then a else protectedReadyRate θ p mode

noncomputable def protectedMainValues {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (mainMode : MainMode) (auxMode : AuxMode) (origin : Option ℝ) (t : ℝ) : Values n := fun j c => match c with
  | .q => if j = i then s.x i .q * Real.exp (-protectedMainRate s i mainMode * (t - s.time))
      else relax (1 / 2) (1 / 10) (s.x j .q) s.time t
  | .m q => if j = i ∧ q = p then
      if auxMode = .ready then auxPulse (s.x i (.m p)) ((θ i).inputGain p * rawInputScale origin s.time) s.time t
      else s.x i (.m p) * Real.exp (-protectedReadyRate (θ i) p auxMode * (t - s.time))
      else relax (1 / 2) (1 / 40) (s.x j (.m q)) s.time t
  | .z q => s.x j (.z q)
  | .b => s.x j .b
  | .energy => twoForcingEnergy (s.x j .energy) (protectedMainCoeff s i mainMode j)
      (protectedMainEnergyRate s i mainMode) (protectedMainAuxCoeff θ s i p auxMode origin j)
      (protectedMainAuxRate (θ i) p auxMode) s.time t

noncomputable def protectedMainEnd {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (mainMode : MainMode) (auxMode : AuxMode) (origin : Option ℝ) (T : ℝ) : Snapshot n :=
  {s with time := T, x := protectedMainValues θ s i p mainMode auxMode origin T}

noncomputable def protectedMainRhs {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (mainMode : MainMode) (auxMode : AuxMode) (origin : Option ℝ) (t : ℝ) (j : Fin n) : Coord → ℝ
  | .q => if j = i then -protectedMainRate s i mainMode * protectedMainValues θ s i p mainMode auxMode origin t j .q
      else (1 / 2) * (1 / 10 - protectedMainValues θ s i p mainMode auxMode origin t j .q)
  | .m q => if j = i ∧ q = p then
      if auxMode = .ready then (1 / 2) * (1 / 40 - protectedMainValues θ s i p mainMode auxMode origin t j (.m q)) +
        (θ i).inputGain p * rawInputScale origin s.time * a * Real.exp (-a * (t - s.time))
      else -protectedReadyRate (θ i) p auxMode * protectedMainValues θ s i p mainMode auxMode origin t j (.m q)
      else (1 / 2) * (1 / 40 - protectedMainValues θ s i p mainMode auxMode origin t j (.m q))
  | .z _ => 0
  | .b => 0
  | .energy => 10 * (100 - protectedMainValues θ s i p mainMode auxMode origin t j .energy) -
      protectedMainCoeff s i mainMode j * Real.exp (-protectedMainEnergyRate s i mainMode * (t - s.time)) -
      protectedMainAuxCoeff θ s i p auxMode origin j * Real.exp (-protectedMainAuxRate (θ i) p auxMode * (t - s.time))

theorem protectedMainValues_initial {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (mm am origin) :
    protectedMainValues θ s i p mm am origin s.time = s.x := by
  funext j c
  cases c <;> simp [protectedMainValues,auxPulse_initial,twoForcingEnergy_initial,relax_initial]
  all_goals (try intro h); (try intro hq); subst_vars; rfl

theorem protectedMainValues_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (mm am origin)
    (t : ℝ) (j : Fin n) (c : Coord) :
    HasDerivAt (fun v => protectedMainValues θ s i p mm am origin v j c)
      (protectedMainRhs θ s i p mm am origin t j c) t := by
  cases c with
  | q =>
    by_cases h : j = i
    · subst j
      simp only [protectedMainValues,protectedMainRhs,ite_true]
      convert (((((hasDerivAt_id t).sub_const s.time).const_mul (-protectedMainRate s i mm)).exp).const_mul (s.x i .q)) using 1 <;> dsimp; ring
    · simpa only [protectedMainValues,protectedMainRhs,h,ite_false] using relax_derivative (1 / 2) (1 / 10) (s.x j .q) s.time t
  | m q =>
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨hj,hq⟩
      subst j
      subst q
      by_cases ha : am = .ready
      · simpa [protectedMainValues,protectedMainRhs,ha,mul_assoc] using auxPulse_derivative (s.x i (.m p)) ((θ i).inputGain p * rawInputScale origin s.time) s.time t
      · simp only [protectedMainValues,protectedMainRhs,ha,ite_false]
        convert (((((hasDerivAt_id t).sub_const s.time).const_mul (-protectedReadyRate (θ i) p am)).exp).const_mul (s.x i (.m p))) using 1 <;> dsimp; ring
    · simpa only [protectedMainValues,protectedMainRhs,h,ite_false] using relax_derivative (1 / 2) (1 / 40) (s.x j (.m q)) s.time t
  | z q => exact hasDerivAt_const _ _
  | b => exact hasDerivAt_const _ _
  | energy => exact twoForcingEnergy_derivative _ _ _ _ _ _ _

theorem protectedMainRhs_continuous {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (mm am origin)
    (j : Fin n) (c : Coord) : Continuous (fun t => protectedMainRhs θ s i p mm am origin t j c) := by
  cases c <;> simp only [protectedMainRhs,protectedMainValues,auxPulse,readyPulse,twoForcingEnergy,energyConvolution,relax,response]
  all_goals (try split_ifs) <;> fun_prop

theorem protectedMain_field {n θ} (s : Snapshot n) (i : Fin n) (p : Port) (mm am origin)
    (hmain : mm = .fast ∨ mm = .slow) (haux : am = .ready ∨ am = .silent ∨ am = .error)
    (hm : s.main i = mm) (hmo : ∀ j, j ≠ i → s.main j = .ready)
    (ha : s.aux i p = am) (hao : ∀ j q, j ≠ i ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw i p = origin) (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (t : ℝ) (ht : s.time ≤ t)
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ t < o + 1) (j : Fin n) (c : Coord) :
    field θ s (protectedMainValues θ s i p mm am origin t) t j c =
      protectedMainRhs θ s i p mm am origin t j c := by
  classical
  have hmainMode (k : Fin n) : s.main k = if k = i then mm else .ready := by
    by_cases h : k = i
    · subst k; simpa using hm
    · simpa [h] using hmo k h
  have hauxMode (k : Fin n) (q : Port) : s.aux k q = if k = i ∧ q = p then am else .ready := by
    by_cases h : k = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩; simpa using ha
    · rw [ite_eq_right h]; exact hao k q (by tauto)
  have hc0 : current s i p t = rawInputScale origin s.time * a * Real.exp (-a * (t - s.time)) := by
    cases origin with
    | none => simp [current,hr,rawInputScale]
    | some o =>
      have hs := hsupport o rfl
      have hex : Real.exp (-a * (s.time - o)) * Real.exp (-a * (t - s.time)) = Real.exp (-a * (t - o)) := by
        rw [← Real.exp_add]; congr 1; ring
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
  have he (q : Port) : errorAct θ s (protectedMainValues θ s i p mm am origin t) j q = 0 := by
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      rcases hmain with rfl | rfl <;> simp [errorAct,hm]
    · simp [errorAct,hauxMode,h]
  have hb (q : Port) : markAct θ s (protectedMainValues θ s i p mm am origin t) j q = 0 := by
    by_cases h : j = i ∧ q = p
    · rcases haux with rfl | rfl | rfl <;> simp [markAct,hauxMode,h]
    · simp [markAct,hauxMode,h]
  have hauxWork (q : Port) : (if s.aux j q = .ready then (θ j).inputGain q * current s j q t
      else auxDrain (θ j) (s.aux j q) q (protectedMainValues θ s i p mm am origin t j (.m q))) =
      if j = i ∧ q = p then protectedMainAuxCoeff θ s i p am origin i *
        Real.exp (-protectedMainAuxRate (θ i) p am * (t - s.time)) else 0 := by
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      rcases haux with rfl | rfl | rfl <;> simp [hauxMode,hcurrent,protectedMainValues,protectedMainAuxCoeff,protectedMainAuxRate,protectedReadyRate,auxDrain,mul_assoc]
    · simp [hauxMode,hcurrent,h]
  cases c with
  | q =>
    by_cases hj : j = i
    · subst j
      rcases hmain with rfl | rfl <;> simp [field,hm,protectedMainRhs,protectedMainRate,protectedMainValues]
    · have hd : drive s (protectedMainValues θ s i p mm am origin t) j t = 0 := by simp [drive,hcurrent,hj]
      simp [field,hmo j hj,hd,protectedMainRhs,hj]
  | m q =>
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      rcases haux with rfl | rfl | rfl <;> simp [field,hauxMode,hcurrent,auxDrain,protectedReadyRate,protectedMainValues,protectedMainRhs,mul_assoc]
    · simp [field,hauxMode,hcurrent,protectedMainRhs,h]
  | z q => simp [field,he,protectedMainRhs]
  | b => simp [field,hb,protectedMainRhs]
  | energy =>
    simp only [field,work,hauxWork,he,hb,Finset.sum_const_zero,protectedMainRhs]
    by_cases hj : j = i
    · subst j
      rcases hmain with rfl | rfl <;> simp [hm,protectedMainValues,protectedMainCoeff,protectedMainEnergyRate,protectedMainRate]
      all_goals ring
    · have hd : drive s (protectedMainValues θ s i p mm am origin t) j t = 0 := by simp [drive,hcurrent,hj]
      simp [hmo j hj,hd,hj,protectedMainCoeff,protectedMainAuxCoeff]

/-- Analytic active guards are explicit. Other cells and ports remain strictly
below their READY guards; raw expiry is allowed only as the endpoint. -/
noncomputable def protectedMainFlow {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (mm : MainMode) (am : AuxMode) (origin : Option ℝ) {T : ℝ}
    (hT : s.time < T) (hmain : mm = .fast ∨ mm = .slow) (haux : am = .ready ∨ am = .silent ∨ am = .error)
    (hm : s.main i = mm) (hmo : ∀ j, j ≠ i → s.main j = .ready)
    (ha : s.aux i p = am) (hao : ∀ j q, j ≠ i ∨ q ≠ p → s.aux j q = .ready)
    (hr : s.raw i p = origin) (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ T ≤ o + 1)
    (hq0 : ∀ j, j ≠ i → s.x j .q < 1)
    (hm0 : ∀ j q, j ≠ i ∨ q ≠ p → s.x j (.m q) < 1)
    (hq : ∀ t ∈ Ico s.time T, (if mm = .fast then (1 / 4 : ℝ) else 1 / 10) <
      s.x i .q * Real.exp (-protectedMainRate s i mm * (t - s.time)))
    (hx : ∀ t ∈ Ico s.time T, if am = .ready then
      auxPulse (s.x i (.m p)) ((θ i).inputGain p * rawInputScale origin s.time) s.time t < 1
      else (if am = .silent then (1 / 10 : ℝ) else 1 / 40) <
        s.x i (.m p) * Real.exp (-protectedReadyRate (θ i) p am * (t - s.time)))
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    Flow θ s (protectedMainEnd θ s i p mm am origin T) where
  positive := hT
  path := protectedMainValues θ s i p mm am origin
  initial := protectedMainValues_initial (θ := θ) s i p mm am origin
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := by
    intro j c
    exact (continuous_iff_continuousAt.mpr (fun t =>
      (protectedMainValues_derivative (θ := θ) s i p mm am origin t j c).continuousAt)).continuousOn
  integrable := by
    intro j c
    apply ((protectedMainRhs_continuous (θ := θ) s i p mm am origin j c).intervalIntegrable s.time T).congr_uIoo
    intro t ht
    rw [uIoo_of_lt hT] at ht
    exact (protectedMain_field s i p mm am origin hmain haux hm hmo ha hao hr ho t ht.1.le
      (fun o he => ⟨(hsupport o he).1,ht.2.trans_le (hsupport o he).2⟩) j c).symm
  mark_integrable := by
    intro j q
    have hzero : ∀ t, markAct θ s (protectedMainValues θ s i p mm am origin t) j q = 0 := by
      intro t
      have hnot : s.aux j q ≠ .mark := by
        by_cases h : j = i ∧ q = p
        · rcases h with ⟨rfl,rfl⟩
          rcases haux with rfl | rfl | rfl <;> simp [ha]
        · simp [hao j q (by tauto)]
      simp [markAct,hnot]
    simp_rw [hzero]
    exact intervalIntegrable_const
  integral_eq := by
    intro t ht j c
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => protectedMainValues_derivative (θ := θ) s i p mm am origin v j c)
      ((protectedMainRhs_continuous (θ := θ) s i p mm am origin j c).intervalIntegrable s.time t)
    rw [protectedMainValues_initial] at he
    have hi : (∫ v in s.time..t, field θ s (protectedMainValues θ s i p mm am origin v) v j c) =
        ∫ v in s.time..t, protectedMainRhs θ s i p mm am origin v j c := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro v hv
      exact protectedMain_field s i p mm am origin hmain haux hm hmo ha hao hr ho v hv.1.le
        (fun o h => ⟨(hsupport o h).1,(hv.2.trans_le ht.2).trans_le (hsupport o h).2⟩) j c
    rw [hi]; linarith
  guards := by
    intro t ht
    constructor
    · intro j
      by_cases hj : j = i
      · subst j
        rcases hmain with rfl | rfl <;> simpa [hm,protectedMainValues] using hq t ht
      · rw [hmo j hj]
        simpa [protectedMainValues,hj] using relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2) ht.1 (hq0 j hj) (by norm_num : (1 / 10 : ℝ) < 1)
    · intro j q
      by_cases h : j = i ∧ q = p
      · rcases h with ⟨rfl,rfl⟩
        rcases haux with rfl | rfl | rfl <;> simpa [ha,protectedMainValues] using hx t ht
      · rw [hao j q (by tauto)]
        simpa [protectedMainValues,h] using relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2) ht.1 (hm0 j q (by tauto)) (by norm_num : (1 / 40 : ℝ) < 1)
  raw_support := by
    intro j q o hactive
    by_cases h : j = i ∧ q = p
    · rcases h with ⟨rfl,rfl⟩
      exact hsupport o (hr.symm.trans hactive)
    · rw [ho j q (by tauto)] at hactive; contradiction
  pending_urgent := hp

end KernelR.Hybrid
