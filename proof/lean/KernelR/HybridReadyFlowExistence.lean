import KernelR.HybridQuietFlowExistence

/-! Construct a real all-READY input flow, including its energy coordinate,
without taking an existing execution or integral trajectory as a premise. -/
namespace KernelR.Hybrid
open Set MeasureTheory

noncomputable def readyInputEnergy (initial coeff start t : ℝ) : ℝ :=
  100 + (initial - 100) * Real.exp (-10 * (t - start)) -
    coeff * a / (10 - a) * (Real.exp (-a * (t - start)) - Real.exp (-10 * (t - start)))

theorem readyInputEnergy_initial (initial coeff start : ℝ) :
    readyInputEnergy initial coeff start start = initial := by simp [readyInputEnergy]

theorem readyInputEnergy_derivative (initial coeff start t : ℝ) :
    HasDerivAt (readyInputEnergy initial coeff start)
      (10 * (100 - readyInputEnergy initial coeff start t) - coeff * a * Real.exp (-a * (t - start))) t := by
  have hfast := ((((hasDerivAt_id t).sub_const start).const_mul (-10)).exp)
  have hraw := ((((hasDerivAt_id t).sub_const start).const_mul (-a)).exp)
  have h := ((hfast.const_mul (initial - 100)).const_add 100).sub
    ((hraw.sub hfast).const_mul (coeff * a / (10 - a)))
  convert h using 1
  · rfl
  · have hn : (10 : ℝ) - a ≠ 0 := by dsimp [a]; linarith [KernelR.log_four_bounds.2]
    dsimp [readyInputEnergy]
    field_simp [hn]
    ring

noncomputable def readyInputMainAmplitude {n} (s : Snapshot n) (i : Fin n) (p : Port) (j : Fin n) : ℝ :=
  if j = i then Real.exp (s.x i (.z p)) else 0

noncomputable def readyInputAuxAmplitude {n} (θ : Fin n → Parameters) (i : Fin n) (p : Port)
    (j : Fin n) (q : Port) : ℝ := if j = i ∧ q = p then (θ i).inputGain p else 0

noncomputable def readyInputWorkCoeff {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (j : Fin n) : ℝ :=
  if j = i then Real.exp (s.x i (.z p)) + (θ i).inputGain p else 0

noncomputable def readyInputValues {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (t : ℝ) : Values n := fun j c => match c with
  | .q => readyPulse (s.x j .q) (readyInputMainAmplitude s i p j) s.time t
  | .m q => auxPulse (s.x j (.m q)) (readyInputAuxAmplitude θ i p j q) s.time t
  | .z q => s.x j (.z q)
  | .b => s.x j .b
  | .energy => readyInputEnergy (s.x j .energy) (readyInputWorkCoeff θ s i p j) s.time t

noncomputable def readyInputEnd {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (T : ℝ) : Snapshot n :=
  {s with time := T, x := readyInputValues θ s i p T}

noncomputable def readyInputRhs {n} (θ : Fin n → Parameters) (s : Snapshot n)
    (i : Fin n) (p : Port) (t : ℝ) (j : Fin n) : Coord → ℝ
  | .q => (1 / 2) * (1 / 10 - readyInputValues θ s i p t j .q) +
      readyInputMainAmplitude s i p j * a * Real.exp (-a * (t - s.time))
  | .m q => (1 / 2) * (1 / 40 - readyInputValues θ s i p t j (.m q)) +
      readyInputAuxAmplitude θ i p j q * a * Real.exp (-a * (t - s.time))
  | .z _ => 0
  | .b => 0
  | .energy => 10 * (100 - readyInputValues θ s i p t j .energy) -
      readyInputWorkCoeff θ s i p j * a * Real.exp (-a * (t - s.time))

theorem readyInputValues_initial {n θ} (s : Snapshot n) (i : Fin n) (p : Port) :
    readyInputValues θ s i p s.time = s.x := by
  funext j c
  cases c <;> simp [readyInputValues,readyPulse_initial,auxPulse_initial,readyInputEnergy_initial]

theorem readyInputValues_derivative {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (t : ℝ) (j : Fin n) (c : Coord) :
    HasDerivAt (fun v => readyInputValues θ s i p v j c) (readyInputRhs θ s i p t j c) t := by
  cases c with
  | q => exact readyPulse_derivative _ _ _ _
  | m q => exact auxPulse_derivative _ _ _ _
  | z q => exact hasDerivAt_const _ _
  | b => exact hasDerivAt_const _ _
  | energy => exact readyInputEnergy_derivative _ _ _ _

theorem readyInputRhs_continuous {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (j : Fin n) (c : Coord) : Continuous (fun t => readyInputRhs θ s i p t j c) := by
  cases c <;> simp only [readyInputRhs,readyInputValues,readyPulse,auxPulse,readyInputEnergy,response] <;> fun_prop

/-- The real raw support is retained; the smooth RHS is equal to the physical
field on this entire pre-expiry interval, not just an assumed equation. -/
theorem readyInput_field {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (hm : ∀ j, s.main j = .ready) (ha : ∀ j q, s.aux j q = .ready)
    (hr : s.raw i p = some s.time)
    (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (t : ℝ) (ht : s.time ≤ t ∧ t < s.time + 1) (j : Fin n) (c : Coord) :
    field θ s (readyInputValues θ s i p t) t j c = readyInputRhs θ s i p t j c := by
  classical
  have hcurrent (k : Fin n) (q : Port) : current s k q t =
      if k = i ∧ q = p then a * Real.exp (-a * (t - s.time)) else 0 := by
    by_cases hk : k = i
    · subst k
      by_cases hq : q = p
      · subst q; simp [current,hr,pulse,ht.1,ht.2]
      · simp [current,ho i q (Or.inr hq),hq]
    · simp [current,ho k q (Or.inl hk),hk]
  have hsum (H : Port → ℝ) : (∑ q, H q * current s j q t) =
      if j = i then H p * a * Real.exp (-a * (t - s.time)) else 0 := by
    by_cases hj : j = i
    · simp [hcurrent,hj,mul_ite,mul_assoc]
    · simp [hcurrent,hj]
  have herror (q : Port) : errorAct θ s (readyInputValues θ s i p t) j q = 0 := by simp [errorAct,ha]
  have hmark (q : Port) : markAct θ s (readyInputValues θ s i p t) j q = 0 := by simp [markAct,ha]
  cases c with
  | q =>
    simp only [field,hm,drive,hsum,readyInputRhs]
    by_cases hj : j = i <;> simp [readyInputMainAmplitude,hj,readyInputValues,mul_assoc]
  | m q =>
    simp only [field,ha,ite_true,readyInputRhs,hcurrent]
    by_cases hj : j = i <;> by_cases hq : q = p <;>
      simp [readyInputAuxAmplitude,hj,hq,mul_assoc]
  | z q => simp [field,herror,readyInputRhs]
  | b => simp [field,hmark,readyInputRhs]
  | energy =>
    simp only [field,work,hm,ha,ite_true,drive,hsum,herror,hmark,Finset.sum_const_zero,readyInputRhs]
    by_cases hj : j = i <;> simp [readyInputWorkCoeff,hj,readyInputValues]; ring

theorem readyPulse_zero_eq_relax (initial start t : ℝ) :
    readyPulse initial 0 start t = relax (1 / 2) (1 / 10) initial start t := by simp [readyPulse,relax]

theorem auxPulse_zero_eq_relax (initial start t : ℝ) :
    auxPulse initial 0 start t = relax (1 / 2) (1 / 40) initial start t := by
  simp only [auxPulse,readyPulse,zero_mul,add_zero,relax]
  ring

/-- Construct the full physical integral flow up to the selected pre-expiry
cut. The two active guard bounds can later come from a scalar first crossing. -/
noncomputable def readyInputFlow {n θ} (s : Snapshot n) (i : Fin n) (p : Port) {T : ℝ}
    (hT : s.time < T) (hraw : T < s.time + 1)
    (hm : ∀ j, s.main j = .ready) (ha : ∀ j q, s.aux j q = .ready)
    (hr : s.raw i p = some s.time)
    (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hq0 : ∀ j, s.x j .q < 1) (hm0 : ∀ j q, s.x j (.m q) < 1)
    (hq : ∀ t ∈ Ico s.time T, readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time t < 1)
    (hx : ∀ t ∈ Ico s.time T, auxPulse (s.x i (.m p)) ((θ i).inputGain p) s.time t < 1)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) : Flow θ s (readyInputEnd θ s i p T) where
  positive := hT
  path := readyInputValues θ s i p
  initial := readyInputValues_initial (θ := θ) s i p
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := by
    intro j c
    exact (continuous_iff_continuousAt.mpr (fun t =>
      (readyInputValues_derivative (θ := θ) s i p t j c).continuousAt)).continuousOn
  integrable := by
    intro j c
    have hc : ContinuousOn (fun t => field θ s (readyInputValues θ s i p t) t j c) (Icc s.time T) := by
      apply (readyInputRhs_continuous (θ := θ) s i p j c).continuousOn.congr
      intro t ht
      exact readyInput_field s i p hm ha hr ho t ⟨ht.1,ht.2.trans_lt hraw⟩ j c
    exact hc.intervalIntegrable_of_Icc hT.le
  mark_integrable := by
    intro j q
    simp only [markAct,ha,reduceCtorEq,false_and,ite_false]
    exact intervalIntegrable_const
  integral_eq := by
    intro t ht j c
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => readyInputValues_derivative (θ := θ) s i p v j c)
      ((readyInputRhs_continuous (θ := θ) s i p j c).intervalIntegrable s.time t)
    rw [readyInputValues_initial] at he
    have hi : (∫ v in s.time..t, field θ s (readyInputValues θ s i p v) v j c) =
        ∫ v in s.time..t, readyInputRhs θ s i p v j c := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le ht.1] at hv
      exact readyInput_field s i p hm ha hr ho v ⟨hv.1,(hv.2.trans ht.2).trans_lt hraw⟩ j c
    rw [hi]
    linarith
  guards := by
    intro t ht
    constructor
    · intro j
      simp only [hm,readyInputValues]
      by_cases hj : j = i
      · subst j
        simpa [readyInputMainAmplitude] using hq t ht
      · rw [readyInputMainAmplitude,ite_eq_right hj,readyPulse_zero_eq_relax]
        exact relax_lt (by norm_num) ht.1 (hq0 j) (by norm_num)
    · intro j q
      simp only [ha,readyInputValues]
      by_cases h : j = i ∧ q = p
      · rcases h with ⟨rfl,rfl⟩
        simpa [readyInputAuxAmplitude] using hx t ht
      · rw [readyInputAuxAmplitude,ite_eq_right h,auxPulse_zero_eq_relax]
        exact relax_lt (by norm_num) ht.1 (hm0 j q) (by norm_num)
  raw_support := by
    intro j q origin hactive
    by_cases hj : j = i
    · subst j
      by_cases hq : q = p
      · subst q
        have he : origin = s.time := Option.some.inj (hactive.symm.trans hr)
        subst origin
        exact ⟨le_rfl,hraw.le⟩
      · rw [ho i q (Or.inr hq)] at hactive
        contradiction
    · rw [ho j q (Or.inl hj)] at hactive
      contradiction
  pending_urgent := hp

end KernelR.Hybrid
