import CircuitInverter

/-! Leak asymmetry. The theorems of `CircuitInverter` assume one leak `a` for the
actual response and for the reference. Here the actual leak `a` and the reference
leak `a'` may differ, with `|a - a'| ≤ α`. The price is an added state error
`α * L`, where `L` bounds `t * (|r₀| + ∫₀ᵗ |H₀|)` on the slot for the reference
initial state `r₀` and nominal help `H₀`, and, for silence, the inhibitory charge
is discounted at the worst leak `a' + α`. Conditional statements about declared
scalar responses, as before. -/

namespace KernelR.Circuit
open MeasureTheory Set

/-- `exp` is 1-Lipschitz on the nonpositive half-line: two decay factors at the
same age `s ≥ 0` differ by at most `|a - b| * s`. -/
theorem decay_factor_gap {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    |Real.exp (-a * s) - Real.exp (-b * s)| ≤ |a - b| * s := by
  have key : ∀ {p q : ℝ}, 0 ≤ p → p ≤ q →
      |Real.exp (-p * s) - Real.exp (-q * s)| ≤ |p - q| * s := by
    intro p q hp hpq
    have d : 0 ≤ (q - p) * s := mul_nonneg (by linarith) hs
    have one := Real.add_one_le_exp (-((q - p) * s))
    have split : Real.exp (-q * s) = Real.exp (-p * s) * Real.exp (-((q - p) * s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have bound : Real.exp (-p * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have pos := Real.exp_pos (-p * s)
    have le1 : Real.exp (-((q - p) * s)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [split, abs_of_nonneg (by nlinarith), abs_of_nonpos (by linarith)]
    nlinarith
  rcases le_total a b with h | h
  · exact key ha h
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact key hb h

/-- Two leaks, same initial state and current: the responses differ by at most
`|a - b| * t * (|x| + ∫₀ᵗ |I|)`. -/
theorem leaky_response_leak_error {a b t x : ℝ} {current : ℝ → ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (time : 0 ≤ t)
    (currentInt : IntervalIntegrable current volume 0 t) :
    |leakyResponse a x current t - leakyResponse b x current t| ≤
      |a - b| * t * (|x| + ∫ u in 0..t, |current u|) := by
  have wa : ContinuousOn (fun u => Real.exp (-a * (t - u))) (uIcc 0 t) := by fun_prop
  have wb : ContinuousOn (fun u => Real.exp (-b * (t - u))) (uIcc 0 t) := by fun_prop
  have ia := currentInt.continuousOn_mul wa
  have ib := currentInt.continuousOn_mul wb
  have difference : leakyResponse a x current t - leakyResponse b x current t =
      (Real.exp (-a * t) - Real.exp (-b * t)) * x +
        ∫ u in 0..t, (Real.exp (-a * (t - u)) - Real.exp (-b * (t - u))) * current u := by
    have split : (∫ u in 0..t, (Real.exp (-a * (t - u)) - Real.exp (-b * (t - u))) * current u) =
        (∫ u in 0..t, Real.exp (-a * (t - u)) * current u) -
          ∫ u in 0..t, Real.exp (-b * (t - u)) * current u := by
      rw [← intervalIntegral.integral_sub ia ib]
      exact intervalIntegral.integral_congr (fun u _ => by ring)
    simp only [leakyResponse, split]
    ring
  have first : |(Real.exp (-a * t) - Real.exp (-b * t)) * x| ≤ |a - b| * t * |x| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (decay_factor_gap ha hb time) (abs_nonneg x)
  have second : |∫ u in 0..t, (Real.exp (-a * (t - u)) - Real.exp (-b * (t - u))) * current u| ≤
      |a - b| * t * ∫ u in 0..t, |current u| := by
    apply (intervalIntegral.abs_integral_le_integral_abs time).trans
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on time (ia.sub ib |>.congr ?_).abs
      (currentInt.abs.const_mul _)
    · intro u hu
      rw [abs_mul]
      have gap := decay_factor_gap ha hb (s := t - u) (by linarith [hu.2])
      have age : |a - b| * (t - u) ≤ |a - b| * t :=
        mul_le_mul_of_nonneg_left (by linarith [hu.1]) (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right (gap.trans age) (abs_nonneg _)
    · exact fun u _ => by ring
  rw [difference]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ |a - b| * t * |x| + |a - b| * t * ∫ u in 0..t, |current u| := add_le_add first second
    _ = _ := by ring

/-- On the slot, the reference computed with the actual leak `a` stays within
`α * L` of the reference with leak `a'`. -/
theorem reference_leak_gap {a a' α L D r₀ : ℝ} {nominalHelp : ℝ → ℝ}
    (leak : 0 ≤ a) (leak' : 0 ≤ a') (gap : |a - a'| ≤ α)
    (nominalInt : IntervalIntegrable nominalHelp volume 0 D)
    (leakBudget : ∀ t ∈ Icc 0 D, t * (|r₀| + ∫ u in 0..t, |nominalHelp u|) ≤ L)
    (t : ℝ) (ht : t ∈ Icc 0 D) :
    |leakyResponse a r₀ nominalHelp t - leakyResponse a' r₀ nominalHelp t| ≤ α * L := by
  have sub : uIcc (0 : ℝ) t ⊆ uIcc 0 D := by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2
  have e := leaky_response_leak_error (x := r₀) leak leak' ht.1 (nominalInt.mono_set sub)
  have nonneg : 0 ≤ t * (|r₀| + ∫ u in 0..t, |nominalHelp u|) :=
    mul_nonneg ht.1 (add_nonneg (abs_nonneg _)
      (intervalIntegral.integral_nonneg ht.1 (fun _ _ => abs_nonneg _)))
  have α0 : 0 ≤ α := (abs_nonneg _).trans gap
  calc _ ≤ |a - a'| * t * (|r₀| + ∫ u in 0..t, |nominalHelp u|) := e
    _ = |a - a'| * (t * (|r₀| + ∫ u in 0..t, |nominalHelp u|)) := by ring
    _ ≤ α * (t * (|r₀| + ∫ u in 0..t, |nominalHelp u|)) := mul_le_mul_of_nonneg_right gap nonneg
    _ ≤ α * L := mul_le_mul_of_nonneg_left (leakBudget t ht) α0

/-- Silence under inhibition with an actual leak `a` and a reference leak `a'`,
`|a - a'| ≤ α`. The margins carry the added state error `α * L`, and the
inhibitory charge is discounted at the worst leak `a' + α`. -/
theorem inhibited_silence_leaks {actual reference help nominalHelp inhibitory wrongSign : ℝ → ℝ}
    {a a' α L initial referenceInitial τ D level actualLevel ε₀ ηH ηm δ Q : ℝ}
    (leak : 0 ≤ a) (leak' : 0 ≤ a') (gap : |a - a'| ≤ α) (order : 0 ≤ τ ∧ τ ≤ D)
    (helpInt : IntervalIntegrable help volume 0 D)
    (nominalInt : IntervalIntegrable nominalHelp volume 0 D)
    (inhibitoryInt : IntervalIntegrable inhibitory volume 0 D)
    (wrongInt : IntervalIntegrable wrongSign volume 0 D)
    (actualLaw : ∀ t ∈ Icc 0 D, actual t =
      leakyResponse a initial (fun u => help u - inhibitory u + wrongSign u) t)
    (referenceLaw : ∀ t ∈ Icc 0 D, reference t = leakyResponse a' referenceInitial nominalHelp t)
    (leakBudget : ∀ t ∈ Icc 0 D, t * (|referenceInitial| + ∫ u in 0..t, |nominalHelp u|) ≤ L)
    (initialError : |initial - referenceInitial| ≤ ε₀)
    (helpError : ∀ t ∈ Icc 0 D, (∫ u in 0..t, |help u - nominalHelp u|) ≤ ηH)
    (inhibitorySign : ∀ u ∈ Icc 0 D, 0 ≤ inhibitory u)
    (wrongSignNonneg : ∀ u ∈ Icc 0 D, 0 ≤ wrongSign u)
    (wrongCharge : (∫ u in 0..D, wrongSign u) ≤ ηm)
    (charge : Q ≤ ∫ u in 0..τ, inhibitory u)
    (chargeNonneg : 0 ≤ Q)
    (thresholdError : |actualLevel - level| ≤ δ)
    (before : ∀ t ∈ Icc 0 τ, reference t + (ε₀ + ηH + ηm) + δ + α * L < level)
    (after : ∀ t ∈ Icc τ D,
      reference t + (ε₀ + ηH + ηm) + δ + α * L < level + Real.exp (-(a' + α) * D) * Q) :
    ∀ t ∈ Icc 0 D, actual t < actualLevel := by
  have close := reference_leak_gap leak leak' gap nominalInt leakBudget
  have worst : Real.exp (-(a' + α) * D) ≤ Real.exp (-a * D) := by
    apply Real.exp_le_exp.mpr
    have : a ≤ a' + α := by linarith [(abs_le.mp gap).2]
    nlinarith [order.1.trans order.2]
  apply inhibited_silence (reference := fun t => leakyResponse a referenceInitial nominalHelp t)
    leak order helpInt nominalInt inhibitoryInt wrongInt actualLaw (fun _ _ => rfl) initialError
    helpError inhibitorySign wrongSignNonneg wrongCharge charge thresholdError
  · intro t ht
    have c := (abs_le.mp (close t ⟨ht.1, ht.2.trans order.2⟩)).2
    have b := before t ht
    rw [referenceLaw t ⟨ht.1, ht.2.trans order.2⟩] at b
    linarith
  · intro t ht
    have c := (abs_le.mp (close t ⟨order.1.trans ht.1, ht.2⟩)).2
    have b := after t ht
    rw [referenceLaw t ⟨order.1.trans ht.1, ht.2⟩] at b
    have q := mul_le_mul_of_nonneg_right worst chargeNonneg
    linarith

/-- Firing without inhibition with an actual leak `a` and a reference leak `a'`,
`|a - a'| ≤ α`: the margins carry the added state error `α * L`. -/
theorem uninhibited_first_crossing_leaks {actual reference help nominalHelp inhibitory : ℝ → ℝ}
    {a a' α L initial referenceInitial early deadline level actualLevel ε₀ ηH ηJ δ : ℝ}
    (leak : 0 ≤ a) (leak' : 0 ≤ a') (gap : |a - a'| ≤ α) (actualCont : Continuous actual)
    (helpInt : IntervalIntegrable help volume 0 deadline)
    (nominalInt : IntervalIntegrable nominalHelp volume 0 deadline)
    (inhibitoryInt : IntervalIntegrable inhibitory volume 0 deadline)
    (order : 0 ≤ early ∧ early < deadline)
    (actualLaw : ∀ t ∈ Icc 0 deadline, actual t =
      leakyResponse a initial (fun u => help u - inhibitory u) t)
    (referenceLaw : ∀ t ∈ Icc 0 deadline,
      reference t = leakyResponse a' referenceInitial nominalHelp t)
    (leakBudget : ∀ t ∈ Icc 0 deadline,
      t * (|referenceInitial| + ∫ u in 0..t, |nominalHelp u|) ≤ L)
    (initialError : |initial - referenceInitial| ≤ ε₀)
    (helpError : ∀ t ∈ Icc 0 deadline, (∫ u in 0..t, |help u - nominalHelp u|) ≤ ηH)
    (offCharge : (∫ u in 0..deadline, |inhibitory u|) ≤ ηJ)
    (thresholdError : |actualLevel - level| ≤ δ)
    (before : ∀ t ∈ Icc 0 early, reference t + (ε₀ + (ηH + ηJ)) + δ + α * L < level)
    (after : level + (ε₀ + (ηH + ηJ)) + δ + α * L < reference deadline) :
    ∃ root, early < root ∧ root < deadline ∧ actual root = actualLevel ∧
      ∀ t ∈ Ico 0 root, actual t < actualLevel := by
  have close := reference_leak_gap leak leak' gap nominalInt leakBudget
  have span : (0 : ℝ) ≤ deadline := order.1.trans order.2.le
  apply uninhibited_first_crossing (reference := fun t => leakyResponse a referenceInitial nominalHelp t)
    leak actualCont helpInt nominalInt inhibitoryInt order actualLaw (fun _ _ => rfl) initialError
    helpError offCharge thresholdError
  · intro t ht
    have c := (abs_le.mp (close t ⟨ht.1, ht.2.trans order.2.le⟩)).2
    have b := before t ht
    rw [referenceLaw t ⟨ht.1, ht.2.trans order.2.le⟩] at b
    linarith
  · have c := (abs_le.mp (close deadline ⟨span, le_rfl⟩)).1
    rw [referenceLaw deadline ⟨span, le_rfl⟩] at after
    linarith

end KernelR.Circuit
