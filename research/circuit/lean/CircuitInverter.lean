import CircuitTiming

/-! An inverter cell in the scalar response model of `CircuitTiming`. A fixed help
current drives the state toward threshold; an inhibitory current of the opposite
sign, admitted from the cell's single input, holds it below. These are conditional
statements about declared scalar responses. They do not establish the response law,
the current bounds, or a comparator/latch event for any circuit. -/

namespace KernelR.Circuit
open MeasureTheory Set

/-- The response is affine in the pair (initial state, current): the difference of
two responses with the same leak is the response to the differences. It is kept for
the later composition step; the two theorems of this file do not use it. -/
theorem leakyResponse_sub {a t initial referenceInitial : ℝ} {current reference : ℝ → ℝ}
    (currentInt : IntervalIntegrable current volume 0 t)
    (referenceInt : IntervalIntegrable reference volume 0 t) :
    leakyResponse a initial current t - leakyResponse a referenceInitial reference t =
      leakyResponse a (initial - referenceInitial) (fun u => current u - reference u) t := by
  have weight : ContinuousOn (fun u => Real.exp (-a * (t - u))) (uIcc 0 t) := by fun_prop
  have hi := currentInt.continuousOn_mul weight
  have hr := referenceInt.continuousOn_mul weight
  have split : (∫ u in 0..t, Real.exp (-a * (t - u)) * (current u - reference u)) =
      (∫ u in 0..t, Real.exp (-a * (t - u)) * current u) -
      (∫ u in 0..t, Real.exp (-a * (t - u)) * reference u) := by
    calc
      _ = ∫ u in 0..t, (Real.exp (-a * (t - u)) * current u -
          Real.exp (-a * (t - u)) * reference u) :=
        intervalIntegral.integral_congr (fun u _ => mul_sub _ _ _)
      _ = _ := intervalIntegral.integral_sub hi hr
  simp only [leakyResponse, split]
  ring

/-- Silence under inhibition. The net current is `help - inhibitory + wrongSign`,
with `inhibitory ≥ 0` and `wrongSign ≥ 0` of total charge at most `ηm`. If at least
`Q` of inhibitory charge arrives by `τ`, the strict margins below keep the actual
state under the actual threshold during the whole slot `[0, D]`. Inhibitory charge
decays with the leak, hence the factor `exp (-a * D)` on `Q`. -/
theorem inhibited_silence {actual reference help nominalHelp inhibitory wrongSign : ℝ → ℝ}
    {a initial referenceInitial τ D level actualLevel ε₀ ηH ηm δ Q : ℝ}
    (leak : 0 ≤ a) (order : 0 ≤ τ ∧ τ ≤ D)
    (helpInt : IntervalIntegrable help volume 0 D)
    (nominalInt : IntervalIntegrable nominalHelp volume 0 D)
    (inhibitoryInt : IntervalIntegrable inhibitory volume 0 D)
    (wrongInt : IntervalIntegrable wrongSign volume 0 D)
    (actualLaw : ∀ t ∈ Icc 0 D, actual t =
      leakyResponse a initial (fun u => help u - inhibitory u + wrongSign u) t)
    (referenceLaw : ∀ t ∈ Icc 0 D, reference t = leakyResponse a referenceInitial nominalHelp t)
    (initialError : |initial - referenceInitial| ≤ ε₀)
    (helpError : ∀ t ∈ Icc 0 D, (∫ u in 0..t, |help u - nominalHelp u|) ≤ ηH)
    (inhibitorySign : ∀ u ∈ Icc 0 D, 0 ≤ inhibitory u)
    (wrongSignNonneg : ∀ u ∈ Icc 0 D, 0 ≤ wrongSign u)
    (wrongCharge : (∫ u in 0..D, wrongSign u) ≤ ηm)
    (charge : Q ≤ ∫ u in 0..τ, inhibitory u)
    (thresholdError : |actualLevel - level| ≤ δ)
    (before : ∀ t ∈ Icc 0 τ, reference t + (ε₀ + ηH + ηm) + δ < level)
    (after : ∀ t ∈ Icc τ D, reference t + (ε₀ + ηH + ηm) + δ < level + Real.exp (-a * D) * Q) :
    ∀ t ∈ Icc 0 D, actual t < actualLevel := by
  intro t ht
  have sub : uIcc (0 : ℝ) t ⊆ uIcc 0 D := by
    rw [uIcc_of_le ht.1, uIcc_of_le (order.1.trans order.2)]
    exact Icc_subset_Icc le_rfl ht.2
  have hH := helpInt.mono_set sub
  have hN := nominalInt.mono_set sub
  have hJ := inhibitoryInt.mono_set sub
  have hW := wrongInt.mono_set sub
  have weight : ContinuousOn (fun u => Real.exp (-a * (t - u))) (uIcc 0 t) := by fun_prop
  have wH := hH.continuousOn_mul weight
  have wJ := hJ.continuousOn_mul weight
  have wW := hW.continuousOn_mul weight
  -- Separate the three currents.
  have decompose : actual t = leakyResponse a initial help t -
      (∫ u in 0..t, Real.exp (-a * (t - u)) * inhibitory u) +
      (∫ u in 0..t, Real.exp (-a * (t - u)) * wrongSign u) := by
    rw [actualLaw t ht]
    have parts : (∫ u in 0..t, Real.exp (-a * (t - u)) * (help u - inhibitory u + wrongSign u)) =
        (∫ u in 0..t, Real.exp (-a * (t - u)) * help u) -
        (∫ u in 0..t, Real.exp (-a * (t - u)) * inhibitory u) +
        (∫ u in 0..t, Real.exp (-a * (t - u)) * wrongSign u) := by
      rw [← intervalIntegral.integral_sub wH wJ, ← intervalIntegral.integral_add (wH.sub wJ) wW]
      exact intervalIntegral.integral_congr (fun u _ => by ring)
    simp only [leakyResponse, parts]
    ring
  -- The help part is within ε₀ + ηH of the reference.
  have helpBound : leakyResponse a initial help t - reference t ≤ ε₀ + ηH := by
    rw [referenceLaw t ht]
    have e := leaky_response_error (initial := initial) (referenceInitial := referenceInitial)
      leak ht.1 hH hN
    have := (abs_le.mp (e.trans (add_le_add initialError (helpError t ht)))).2
    linarith
  -- Weights lie in [exp (-a * D), 1] on the prefix.
  have weightLe (u : ℝ) (hu : u ∈ Icc 0 t) : Real.exp (-a * (t - u)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hu.2])
  have weightGe (u : ℝ) (hu : u ∈ Icc 0 t) : Real.exp (-a * D) ≤ Real.exp (-a * (t - u)) :=
    Real.exp_le_exp.mpr (by nlinarith [hu.1, ht.2])
  -- The wrong-sign part is at most ηm.
  have wrongBound : (∫ u in 0..t, Real.exp (-a * (t - u)) * wrongSign u) ≤ ηm := by
    have pointwise : (∫ u in 0..t, Real.exp (-a * (t - u)) * wrongSign u) ≤
        ∫ u in 0..t, wrongSign u := by
      apply intervalIntegral.integral_mono_on ht.1 wW hW
      intro u hu
      have w := wrongSignNonneg u ⟨hu.1, hu.2.trans ht.2⟩
      simpa using mul_le_mul_of_nonneg_right (weightLe u hu) w
    have longer : (∫ u in 0..t, wrongSign u) ≤ ∫ u in 0..D, wrongSign u := by
      apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 _ wrongInt
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact wrongSignNonneg u ⟨hu.1.le, hu.2⟩
    linarith
  have threshold := (abs_le.mp thresholdError).1
  -- The inhibitory part is nonnegative, and at least exp (-a * D) * Q after τ.
  have weightedNonneg (u : ℝ) (hu : u ∈ Icc 0 t) :
      0 ≤ Real.exp (-a * (t - u)) * inhibitory u :=
    mul_nonneg (Real.exp_pos _).le (inhibitorySign u ⟨hu.1, hu.2.trans ht.2⟩)
  have inhibitionNonneg : 0 ≤ ∫ u in 0..t, Real.exp (-a * (t - u)) * inhibitory u :=
    intervalIntegral.integral_nonneg ht.1 weightedNonneg
  rw [decompose]
  by_cases early : t ≤ τ
  · have b := before t ⟨ht.1, early⟩
    linarith
  · have late : τ ≤ t := le_of_not_ge early
    have hτ : uIcc (0 : ℝ) τ ⊆ uIcc 0 t := by
      rw [uIcc_of_le order.1, uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl late
    have prefixCharge : (∫ u in 0..τ, Real.exp (-a * (t - u)) * inhibitory u) ≤
        ∫ u in 0..t, Real.exp (-a * (t - u)) * inhibitory u := by
      apply intervalIntegral.integral_mono_interval le_rfl order.1 late _ wJ
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact weightedNonneg u ⟨hu.1.le, hu.2⟩
    have floor : Real.exp (-a * D) * (∫ u in 0..τ, inhibitory u) ≤
        ∫ u in 0..τ, Real.exp (-a * (t - u)) * inhibitory u := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on order.1 ((hJ.mono_set hτ).const_mul _)
        (wJ.mono_set hτ)
      intro u hu
      exact mul_le_mul_of_nonneg_right (weightGe u ⟨hu.1, hu.2.trans late⟩)
        (inhibitorySign u ⟨hu.1, hu.2.trans order.2⟩)
    have scaled : Real.exp (-a * D) * Q ≤ Real.exp (-a * D) * (∫ u in 0..τ, inhibitory u) :=
      mul_le_mul_of_nonneg_left charge (Real.exp_pos _).le
    have b := after t ⟨late, ht.2⟩
    linarith

/-- Firing without inhibition. When the input is absent, the inhibitory path still
carries a parasitic current `inhibitory`, of total absolute charge at most `ηJ`. Its
budget adds to the help error, and the existing first-contact theorem applies. -/
theorem uninhibited_first_crossing {actual reference help nominalHelp inhibitory : ℝ → ℝ}
    {a initial referenceInitial early deadline level actualLevel ε₀ ηH ηJ δ : ℝ}
    (leak : 0 ≤ a) (actualCont : Continuous actual)
    (helpInt : IntervalIntegrable help volume 0 deadline)
    (nominalInt : IntervalIntegrable nominalHelp volume 0 deadline)
    (inhibitoryInt : IntervalIntegrable inhibitory volume 0 deadline)
    (order : 0 ≤ early ∧ early < deadline)
    (actualLaw : ∀ t ∈ Icc 0 deadline, actual t =
      leakyResponse a initial (fun u => help u - inhibitory u) t)
    (referenceLaw : ∀ t ∈ Icc 0 deadline,
      reference t = leakyResponse a referenceInitial nominalHelp t)
    (initialError : |initial - referenceInitial| ≤ ε₀)
    (helpError : ∀ t ∈ Icc 0 deadline, (∫ u in 0..t, |help u - nominalHelp u|) ≤ ηH)
    (offCharge : (∫ u in 0..deadline, |inhibitory u|) ≤ ηJ)
    (thresholdError : |actualLevel - level| ≤ δ)
    (before : ∀ t ∈ Icc 0 early, reference t + (ε₀ + (ηH + ηJ)) + δ < level)
    (after : level + (ε₀ + (ηH + ηJ)) + δ < reference deadline) :
    ∃ root, early < root ∧ root < deadline ∧ actual root = actualLevel ∧
      ∀ t ∈ Ico 0 root, actual t < actualLevel := by
  apply current_error_first_crossing leak actualCont (helpInt.sub inhibitoryInt) nominalInt order
    actualLaw referenceLaw initialError ?_ thresholdError before after
  intro t ht
  have sub : uIcc (0 : ℝ) t ⊆ uIcc 0 deadline := by
    rw [uIcc_of_le ht.1, uIcc_of_le (order.1.trans order.2.le)]
    exact Icc_subset_Icc le_rfl ht.2
  have hH := helpInt.mono_set sub
  have hN := nominalInt.mono_set sub
  have hJ := inhibitoryInt.mono_set sub
  have triangle : (∫ u in 0..t, |help u - inhibitory u - nominalHelp u|) ≤
      ∫ u in 0..t, (|help u - nominalHelp u| + |inhibitory u|) := by
    apply intervalIntegral.integral_mono_on ht.1 ((hH.sub hJ).sub hN).abs
      ((hH.sub hN).abs.add hJ.abs)
    intro u _
    calc |help u - inhibitory u - nominalHelp u|
        = |(help u - nominalHelp u) + (-inhibitory u)| := by ring_nf
      _ ≤ |help u - nominalHelp u| + |-inhibitory u| := abs_add_le _ _
      _ = |help u - nominalHelp u| + |inhibitory u| := by rw [abs_neg]
  have split : (∫ u in 0..t, (|help u - nominalHelp u| + |inhibitory u|)) =
      (∫ u in 0..t, |help u - nominalHelp u|) + ∫ u in 0..t, |inhibitory u| :=
    intervalIntegral.integral_add (hH.sub hN).abs hJ.abs
  have longer : (∫ u in 0..t, |inhibitory u|) ≤ ∫ u in 0..deadline, |inhibitory u| := by
    apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 _ inhibitoryInt.abs
    exact Filter.Eventually.of_forall (fun u => abs_nonneg _)
  have h := helpError t ht
  linarith

end KernelR.Circuit
