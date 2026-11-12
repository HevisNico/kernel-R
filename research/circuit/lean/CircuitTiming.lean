import CircuitRobustness
import KernelR.HybridScalarFirstCrossing

/-! From admitted-current error to a robust first threshold contact.
The paths are uncut continuous scalar responses before hybrid reset.
A contact is not identified with a comparator/latch output event here. -/

namespace KernelR.Circuit
open MeasureTheory Set

/-- Linear leaky response, in a state coordinate relative to a common
rest level. Establishing this response law for a circuit is an obligation. -/
noncomputable def leakyResponse (a initial : ℝ) (current : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-a * t) * initial + ∫ u in 0..t, Real.exp (-a * (t - u)) * current u

/-- For equal nonnegative leak rates, input error is not amplified in
the scalar response: initial error plus the L1 admitted-current error
bounds the charge discrepancy. This does not assume a constant time lag. -/
theorem leaky_response_error {a t initial referenceInitial : ℝ} {current reference : ℝ → ℝ}
    (leak : 0 ≤ a) (time : 0 ≤ t)
    (currentInt : IntervalIntegrable current volume 0 t)
    (referenceInt : IntervalIntegrable reference volume 0 t) :
    |leakyResponse a initial current t - leakyResponse a referenceInitial reference t| ≤
      |initial - referenceInitial| + ∫ u in 0..t, |current u - reference u| := by
  have weight : ContinuousOn (fun u => Real.exp (-a * (t - u))) (uIcc 0 t) := by fun_prop
  have hi := currentInt.continuousOn_mul weight
  have hr := referenceInt.continuousOn_mul weight
  have hd := (currentInt.sub referenceInt).continuousOn_mul weight
  have ha := (currentInt.sub referenceInt).abs
  have difference :
      leakyResponse a initial current t - leakyResponse a referenceInitial reference t =
        Real.exp (-a * t) * (initial - referenceInitial) +
          ∫ u in 0..t, Real.exp (-a * (t - u)) * (current u - reference u) := by
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
  have decay : Real.exp (-a * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have integralBound :
      |∫ u in 0..t, Real.exp (-a * (t - u)) * (current u - reference u)| ≤
        ∫ u in 0..t, |current u - reference u| := by
    apply (intervalIntegral.abs_integral_le_integral_abs time).trans
    apply intervalIntegral.integral_mono_on time hd.abs ha
    intro u hu
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have factor : Real.exp (-a * (t - u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hu.2])
    simpa using mul_le_mul_of_nonneg_right factor (abs_nonneg (current u - reference u))
  rw [difference]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have initialBound := mul_le_mul_of_nonneg_right decay (abs_nonneg (initial - referenceInitial))
  linarith

/-- Model margins before `early` and at `deadline`, together with uniform
state and threshold errors, construct an actual FIRST contact in between.
Earlier spurious scalar contacts are excluded by the strict preguard. -/
theorem robust_first_crossing {actual reference : ℝ → ℝ}
    {start early deadline level actualLevel ε δ : ℝ}
    (continuous : Continuous actual)
    (order : start ≤ early ∧ early < deadline)
    (stateError : ∀ t ∈ Icc start deadline, |actual t - reference t| ≤ ε)
    (thresholdError : |actualLevel - level| ≤ δ)
    (before : ∀ t ∈ Icc start early, reference t + ε + δ < level)
    (after : level + ε + δ < reference deadline) :
    ∃ root, early < root ∧ root < deadline ∧ actual root = actualLevel ∧
      ∀ t ∈ Ico start root, actual t < actualLevel := by
  have ht : start < deadline := order.1.trans_lt order.2
  have threshold := abs_le.mp thresholdError
  have lower : actual start < actualLevel := by
    have e := abs_le.mp (stateError start ⟨le_rfl, ht.le⟩)
    have b := before start ⟨le_rfl, order.1⟩
    linarith [e.2, threshold.1]
  have upper : actualLevel < actual deadline := by
    have e := abs_le.mp (stateError deadline ⟨ht.le, le_rfl⟩)
    linarith [e.1, threshold.2]
  obtain ⟨root, first, last, hit, prior⟩ :=
    KernelR.Hybrid.scalar_first_crossing continuous ht lower upper
  refine ⟨root, ?_, last, hit, prior⟩
  by_contra tooEarly
  have e := abs_le.mp (stateError root ⟨first.le, last.le⟩)
  have b := before root ⟨first.le, le_of_not_gt tooEarly⟩
  rw [hit] at e
  linarith [e.2, threshold.1]

/-- A positive lower slope of the reference trajectory converts state and
threshold errors into a latency bound. It does not assume that the actual
trajectory is monotone, or that its perturbation is a time shift. -/
theorem contact_time_error {actual reference : ℝ → ℝ}
    {start deadline root nominal level actualLevel ε δ speed : ℝ}
    (continuous : ContinuousOn reference (Icc start deadline))
    (differentiable : DifferentiableOn ℝ reference (interior (Icc start deadline)))
    (slope : ∀ t ∈ interior (Icc start deadline), speed ≤ deriv reference t)
    (positive : 0 < speed)
    (rootIn : root ∈ Icc start deadline) (nominalIn : nominal ∈ Icc start deadline)
    (modelHit : reference nominal = level) (actualHit : actual root = actualLevel)
    (stateError : |actual root - reference root| ≤ ε)
    (thresholdError : |actualLevel - level| ≤ δ) :
    |root - nominal| ≤ (ε + δ) / speed := by
  have e := abs_le.mp stateError
  have h := abs_le.mp thresholdError
  rw [actualHit] at e
  apply (le_div_iff₀ positive).mpr
  by_cases order : root ≤ nominal
  · have separation := (convex_Icc start deadline).mul_sub_le_image_sub_of_le_deriv
      continuous differentiable slope root rootIn nominal nominalIn order
    rw [modelHit] at separation
    rw [abs_of_nonpos (sub_nonpos.mpr order)]
    nlinarith [e.2, h.1]
  · have separation := (convex_Icc start deadline).mul_sub_le_image_sub_of_le_deriv
      continuous differentiable slope nominal nominalIn root rootIn (le_of_not_ge order)
    rw [modelHit] at separation
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge order))]
    nlinarith [e.1, h.2]

/-- The existence and latency statements are composed for the SAME first
contact. The reference slope is a separate resource from the error budget. -/
theorem robust_first_crossing_with_latency {actual reference : ℝ → ℝ}
    {start early deadline nominal level actualLevel ε δ speed : ℝ}
    (actualCont : Continuous actual)
    (order : start ≤ early ∧ early < deadline)
    (stateError : ∀ t ∈ Icc start deadline, |actual t - reference t| ≤ ε)
    (thresholdError : |actualLevel - level| ≤ δ)
    (before : ∀ t ∈ Icc start early, reference t + ε + δ < level)
    (after : level + ε + δ < reference deadline)
    (referenceCont : ContinuousOn reference (Icc start deadline))
    (differentiable : DifferentiableOn ℝ reference (interior (Icc start deadline)))
    (slope : ∀ t ∈ interior (Icc start deadline), speed ≤ deriv reference t)
    (positive : 0 < speed) (nominalIn : nominal ∈ Icc start deadline)
    (modelHit : reference nominal = level) :
    ∃ root, early < root ∧ root < deadline ∧ actual root = actualLevel ∧
      (∀ t ∈ Ico start root, actual t < actualLevel) ∧
      |root - nominal| ≤ (ε + δ) / speed := by
  obtain ⟨root, lo, hi, hit, prior⟩ :=
    robust_first_crossing actualCont order stateError thresholdError before after
  have rootIn : root ∈ Icc start deadline := ⟨(order.1.trans_lt lo).le, hi.le⟩
  exact ⟨root, lo, hi, hit, prior, contact_time_error referenceCont differentiable slope
    positive rootIn nominalIn modelHit hit (stateError root rootIn) thresholdError⟩

/-- A whole-interval admitted-current budget supplies the state-error
hypothesis of the first-contact theorem. Both paths must satisfy the
declared same-leak scalar response law. -/
theorem current_error_first_crossing {actual reference current referenceCurrent : ℝ → ℝ}
    {a initial referenceInitial early deadline level actualLevel ε₀ η δ : ℝ}
    (leak : 0 ≤ a) (actualCont : Continuous actual)
    (currentInt : IntervalIntegrable current volume 0 deadline)
    (referenceInt : IntervalIntegrable referenceCurrent volume 0 deadline)
    (order : 0 ≤ early ∧ early < deadline)
    (actualLaw : ∀ t ∈ Icc 0 deadline, actual t = leakyResponse a initial current t)
    (referenceLaw : ∀ t ∈ Icc 0 deadline,
      reference t = leakyResponse a referenceInitial referenceCurrent t)
    (initialError : |initial - referenceInitial| ≤ ε₀)
    (currentError : ∀ t ∈ Icc 0 deadline, (∫ u in 0..t, |current u - referenceCurrent u|) ≤ η)
    (thresholdError : |actualLevel - level| ≤ δ)
    (before : ∀ t ∈ Icc 0 early, reference t + (ε₀ + η) + δ < level)
    (after : level + (ε₀ + η) + δ < reference deadline) :
    ∃ root, early < root ∧ root < deadline ∧ actual root = actualLevel ∧
      ∀ t ∈ Ico 0 root, actual t < actualLevel := by
  apply robust_first_crossing actualCont order ?_ thresholdError before after
  intro t ht
  rw [actualLaw t ht, referenceLaw t ht]
  have sub : uIcc (0 : ℝ) t ⊆ uIcc 0 deadline := by
    rw [uIcc_of_le ht.1, uIcc_of_le (order.1.trans order.2.le)]
    exact Icc_subset_Icc le_rfl ht.2
  have bound := leaky_response_error (initial := initial) (referenceInitial := referenceInitial)
    leak ht.1 (currentInt.mono_set sub) (referenceInt.mono_set sub)
  exact bound.trans (add_le_add initialError (currentError t ht))

/-- A grazing reference contact can disappear under an arbitrarily small
uniform perturbation. A contact alone cannot replace strict margins or
the lower-slope hypothesis in the transfer theorems. -/
theorem grazing_contact_counterexample {ε : ℝ} (positive : 0 < ε) :
    -((0 : ℝ) ^ 2) = 0 ∧
      (∀ t : ℝ, |(-(t ^ 2) - ε) - (-(t ^ 2))| = ε) ∧
      (∀ t : ℝ, -(t ^ 2) - ε < 0) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro t
    rw [show (-(t ^ 2) - ε) - (-(t ^ 2)) = -ε by ring, abs_neg, abs_of_pos positive]
  · intro t
    nlinarith [sq_nonneg t]

end KernelR.Circuit
