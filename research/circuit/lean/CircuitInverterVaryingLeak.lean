import CircuitInverter

/-! A leak that varies along the trajectory. The actual cell leaks at a rate
`leak t` that may depend on time, or on the state through the trajectory (for
instance a different rate above and below rest: `leak t = side (actual t)`), with
`|leak t - a'| ≤ α` against the reference's constant leak `a'`.

The actual response is stated in integral form relative to the constant leak `a'`:
the varying part of the leak acts as an extra current `-(leak u - a') * actual u`.
`varying_leak_integral_form` derives this form from the differential law
`actual' = -leak * actual + I` where the trajectory is differentiable; the integral
form itself, like the charge balances of the bridge, also admits switched currents.

The price is an a priori bound `|actual u| ≤ X` along the slot: the varying leak
then adds at most `α * X * D` to the help error. -/

namespace KernelR.Circuit
open MeasureTheory Set

/-- The differential law with a varying leak gives the integral form relative to a
constant leak `a'`: the leak difference becomes an extra current. Sufficient
constructor for a differentiable trajectory; not required by the theorems below. -/
theorem varying_leak_integral_form {actual leak current : ℝ → ℝ} {a' t : ℝ} (time : 0 ≤ t)
    (continuous : ContinuousOn actual (Icc 0 t))
    (derivative : ∀ u ∈ Ioo 0 t, HasDerivAt actual (-leak u * actual u + current u) u)
    (integrable : IntervalIntegrable
      (fun u => Real.exp (a' * u) * (current u - (leak u - a') * actual u)) volume 0 t) :
    actual t = leakyResponse a' (actual 0) (fun u => current u - (leak u - a') * actual u) t := by
  set g : ℝ → ℝ := fun u => current u - (leak u - a') * actual u
  have scaledCont : ContinuousOn (fun u => Real.exp (a' * u) * actual u) (Icc 0 t) :=
    (Continuous.continuousOn (by fun_prop)).mul continuous
  have scaledDeriv : ∀ u ∈ Ioo 0 t,
      HasDerivAt (fun u => Real.exp (a' * u) * actual u) (Real.exp (a' * u) * g u) u := by
    intro u hu
    have e : HasDerivAt (fun u => Real.exp (a' * u)) (Real.exp (a' * u) * a') u := by
      simpa using ((hasDerivAt_id u).const_mul a').exp
    convert e.mul (derivative u hu) using 1
    simp only [g]
    ring
  have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le time scaledCont scaledDeriv integrable
  simp only [mul_zero, Real.exp_zero, one_mul] at ftc
  have split : (∫ u in 0..t, Real.exp (-a' * (t - u)) * g u) =
      Real.exp (-a' * t) * ∫ u in 0..t, Real.exp (a' * u) * g u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    simp only
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp only [leakyResponse]
  rw [split, ftc]
  have cancel : Real.exp (-a' * t) * Real.exp (a' * t) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (-(actual t)) * cancel

/-- The extra current of the varying leak is small in L1 on every prefix. -/
theorem varying_leak_drift {actual leak : ℝ → ℝ} {a' α X D : ℝ}
    (driftInt : IntervalIntegrable (fun u => (leak u - a') * actual u) volume 0 D)
    (gap : ∀ u ∈ Icc 0 D, |leak u - a'| ≤ α) (stateBound : ∀ u ∈ Icc 0 D, |actual u| ≤ X)
    (t : ℝ) (ht : t ∈ Icc 0 D) :
    (∫ u in 0..t, |(leak u - a') * actual u|) ≤ α * X * D := by
  have sub : uIcc (0 : ℝ) t ⊆ uIcc 0 D := by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2
  have α0 : 0 ≤ α := (abs_nonneg _).trans (gap 0 ⟨le_rfl, ht.1.trans ht.2⟩)
  have X0 : 0 ≤ X := (abs_nonneg _).trans (stateBound 0 ⟨le_rfl, ht.1.trans ht.2⟩)
  calc (∫ u in 0..t, |(leak u - a') * actual u|) ≤ ∫ _ in (0 : ℝ)..t, α * X := by
        apply intervalIntegral.integral_mono_on ht.1 ((driftInt.mono_set sub).abs) intervalIntegrable_const
        intro u hu
        rw [abs_mul]
        exact mul_le_mul (gap u ⟨hu.1, hu.2.trans ht.2⟩) (stateBound u ⟨hu.1, hu.2.trans ht.2⟩)
          (abs_nonneg _) α0
    _ = α * X * t := by simp; ring
    _ ≤ α * X * D := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg α0 X0)

/-- The help error with the varying leak folded in. -/
private theorem folded_help_error {actual leak help nominalHelp : ℝ → ℝ} {a' α X D ηH : ℝ}
    (helpInt : IntervalIntegrable help volume 0 D)
    (nominalInt : IntervalIntegrable nominalHelp volume 0 D)
    (driftInt : IntervalIntegrable (fun u => (leak u - a') * actual u) volume 0 D)
    (gap : ∀ u ∈ Icc 0 D, |leak u - a'| ≤ α) (stateBound : ∀ u ∈ Icc 0 D, |actual u| ≤ X)
    (helpError : ∀ t ∈ Icc 0 D, (∫ u in 0..t, |help u - nominalHelp u|) ≤ ηH) :
    ∀ t ∈ Icc 0 D,
      (∫ u in 0..t, |(help u - (leak u - a') * actual u) - nominalHelp u|) ≤ ηH + α * X * D := by
  intro t ht
  have sub : uIcc (0 : ℝ) t ⊆ uIcc 0 D := by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2
  have hH := helpInt.mono_set sub
  have hN := nominalInt.mono_set sub
  have hD := driftInt.mono_set sub
  have triangle : (∫ u in 0..t, |(help u - (leak u - a') * actual u) - nominalHelp u|) ≤
      ∫ u in 0..t, (|help u - nominalHelp u| + |(leak u - a') * actual u|) := by
    apply intervalIntegral.integral_mono_on ht.1 ((hH.sub hD).sub hN).abs ((hH.sub hN).abs.add hD.abs)
    intro u _
    calc |(help u - (leak u - a') * actual u) - nominalHelp u|
        = |(help u - nominalHelp u) + (-((leak u - a') * actual u))| := by ring_nf
      _ ≤ |help u - nominalHelp u| + |-((leak u - a') * actual u)| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  rw [intervalIntegral.integral_add (hH.sub hN).abs hD.abs] at triangle
  have d := varying_leak_drift driftInt gap stateBound t ht
  linarith [helpError t ht]

/-- Silence under inhibition with a varying leak, `|leak t - a'| ≤ α` along the
slot, against the reference with constant leak `a'`. The margins are those of
`inhibited_silence` with `ηH` replaced by `ηH + α * X * D`. -/
theorem inhibited_silence_varying
    {actual reference leak help nominalHelp inhibitory wrongSign : ℝ → ℝ}
    {a' α X initial referenceInitial τ D level actualLevel ε₀ ηH ηm δ Q : ℝ}
    (leak' : 0 ≤ a') (order : 0 ≤ τ ∧ τ ≤ D)
    (helpInt : IntervalIntegrable help volume 0 D)
    (nominalInt : IntervalIntegrable nominalHelp volume 0 D)
    (inhibitoryInt : IntervalIntegrable inhibitory volume 0 D)
    (wrongInt : IntervalIntegrable wrongSign volume 0 D)
    (driftInt : IntervalIntegrable (fun u => (leak u - a') * actual u) volume 0 D)
    (gap : ∀ u ∈ Icc 0 D, |leak u - a'| ≤ α) (stateBound : ∀ u ∈ Icc 0 D, |actual u| ≤ X)
    (actualLaw : ∀ t ∈ Icc 0 D, actual t = leakyResponse a' initial
      (fun u => (help u - (leak u - a') * actual u) - inhibitory u + wrongSign u) t)
    (referenceLaw : ∀ t ∈ Icc 0 D, reference t = leakyResponse a' referenceInitial nominalHelp t)
    (initialError : |initial - referenceInitial| ≤ ε₀)
    (helpError : ∀ t ∈ Icc 0 D, (∫ u in 0..t, |help u - nominalHelp u|) ≤ ηH)
    (inhibitorySign : ∀ u ∈ Icc 0 D, 0 ≤ inhibitory u)
    (wrongSignNonneg : ∀ u ∈ Icc 0 D, 0 ≤ wrongSign u)
    (wrongCharge : (∫ u in 0..D, wrongSign u) ≤ ηm)
    (charge : Q ≤ ∫ u in 0..τ, inhibitory u)
    (thresholdError : |actualLevel - level| ≤ δ)
    (before : ∀ t ∈ Icc 0 τ, reference t + (ε₀ + (ηH + α * X * D) + ηm) + δ < level)
    (after : ∀ t ∈ Icc τ D,
      reference t + (ε₀ + (ηH + α * X * D) + ηm) + δ < level + Real.exp (-a' * D) * Q) :
    ∀ t ∈ Icc 0 D, actual t < actualLevel :=
  inhibited_silence (help := fun u => help u - (leak u - a') * actual u) leak' order
    (helpInt.sub driftInt) nominalInt inhibitoryInt wrongInt actualLaw referenceLaw initialError
    (folded_help_error helpInt nominalInt driftInt gap stateBound helpError)
    inhibitorySign wrongSignNonneg wrongCharge charge thresholdError before after

/-- Firing without inhibition with a varying leak: the margins of
`uninhibited_first_crossing` with `ηH` replaced by `ηH + α * X * D`. -/
theorem uninhibited_first_crossing_varying
    {actual reference leak help nominalHelp inhibitory : ℝ → ℝ}
    {a' α X initial referenceInitial early deadline level actualLevel ε₀ ηH ηJ δ : ℝ}
    (leak' : 0 ≤ a') (actualCont : Continuous actual)
    (helpInt : IntervalIntegrable help volume 0 deadline)
    (nominalInt : IntervalIntegrable nominalHelp volume 0 deadline)
    (inhibitoryInt : IntervalIntegrable inhibitory volume 0 deadline)
    (driftInt : IntervalIntegrable (fun u => (leak u - a') * actual u) volume 0 deadline)
    (gap : ∀ u ∈ Icc 0 deadline, |leak u - a'| ≤ α)
    (stateBound : ∀ u ∈ Icc 0 deadline, |actual u| ≤ X)
    (order : 0 ≤ early ∧ early < deadline)
    (actualLaw : ∀ t ∈ Icc 0 deadline, actual t = leakyResponse a' initial
      (fun u => (help u - (leak u - a') * actual u) - inhibitory u) t)
    (referenceLaw : ∀ t ∈ Icc 0 deadline,
      reference t = leakyResponse a' referenceInitial nominalHelp t)
    (initialError : |initial - referenceInitial| ≤ ε₀)
    (helpError : ∀ t ∈ Icc 0 deadline, (∫ u in 0..t, |help u - nominalHelp u|) ≤ ηH)
    (offCharge : (∫ u in 0..deadline, |inhibitory u|) ≤ ηJ)
    (thresholdError : |actualLevel - level| ≤ δ)
    (before : ∀ t ∈ Icc 0 early, reference t + (ε₀ + ((ηH + α * X * deadline) + ηJ)) + δ < level)
    (after : level + (ε₀ + ((ηH + α * X * deadline) + ηJ)) + δ < reference deadline) :
    ∃ root, early < root ∧ root < deadline ∧ actual root = actualLevel ∧
      ∀ t ∈ Ico 0 root, actual t < actualLevel :=
  uninhibited_first_crossing (help := fun u => help u - (leak u - a') * actual u) leak' actualCont
    (helpInt.sub driftInt) nominalInt inhibitoryInt order actualLaw referenceLaw initialError
    (folded_help_error helpInt nominalInt driftInt gap stateBound helpError)
    offCharge thresholdError before after

end KernelR.Circuit
