import PhysicalEvaluator.MeasuredGains

/-! Transfer a supplied additive amplitude-error budget to a log-gain budget.
The amplitude is the positive response-scaled drive after any rest-charge
correction. The error premise must cover its physical/model discrepancy;
these analytic results do not measure that discrepancy from reported peaks. -/
namespace ReusableController.PhysicalEvaluator
open RecursiveLearning.Native KernelR.Hybrid

private theorem log_sub_le_of_amplitude {x y floor eps : ℝ}
    (floorPositive : 0 < floor) (xFloor : floor ≤ x) (yFloor : floor ≤ y)
    (epsNonnegative : 0 ≤ eps) (difference : x - y ≤ eps) :
    Real.log x - Real.log y ≤ eps / floor := by
  have xpos : 0 < x := lt_of_lt_of_le floorPositive xFloor
  have ypos : 0 < y := lt_of_lt_of_le floorPositive yFloor
  have bound := Real.log_le_sub_one_of_pos (div_pos xpos ypos)
  rw [Real.log_div xpos.ne' ypos.ne'] at bound
  have quotient : x / y - 1 = (x - y) / y := by
    field_simp
  calc
    Real.log x - Real.log y ≤ (x - y) / y := quotient ▸ bound
    _ ≤ eps / y := div_le_div_of_nonneg_right difference ypos.le
    _ ≤ eps / floor := by gcongr

/-- A positive lower bound on the reported amplitude and an additive error
smaller than that bound ensure positivity of the true amplitude and control
the logarithmic error. No transcendental numerical estimate is assumed. -/
theorem log_error_of_amplitude {L measured truth eps : ℝ}
    (positive : 0 < L) (measuredFloor : L ≤ measured)
    (epsNonnegative : 0 ≤ eps) (epsSmall : eps < L)
    (amplitudeError : |truth - measured| ≤ eps) :
    0 < truth ∧ |Real.log truth - Real.log measured| ≤ eps / (L - eps) := by
  have difference := abs_le.mp amplitudeError
  have floorPositive : 0 < L - eps := by linarith [positive]
  have truthFloor : L - eps ≤ truth := by linarith [difference.1]
  have reportFloor : L - eps ≤ measured := by linarith
  have forward := log_sub_le_of_amplitude floorPositive truthFloor reportFloor
    epsNonnegative difference.2
  have reverse := log_sub_le_of_amplitude floorPositive reportFloor truthFloor
    epsNonnegative (show measured - truth ≤ eps by linarith [difference.1])
  exact ⟨lt_of_lt_of_le floorPositive truthFloor,
    abs_le.mpr ⟨by linarith, forward⟩⟩

/-- Normalize by the scalar response. The supplied amplitude residual is
against `response 1 * exp trueGain`, not against an independently certified
transistor gain. Its physical validity is an explicit obligation. -/
theorem scalarGain_error_of_amplitude {L measured trueGain eps : ℝ}
    (positive : 0 < L) (measuredFloor : L ≤ measured)
    (epsNonnegative : 0 ≤ eps) (epsSmall : eps < L)
    (amplitudeError : |response 1 * Real.exp trueGain - measured| ≤ eps) :
    |trueGain - scalarGain (Real.log measured)| ≤ eps / (L - eps) := by
  have bound := (log_error_of_amplitude positive measuredFloor epsNonnegative epsSmall
    amplitudeError).2
  rw [Real.log_mul response_one_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at bound
  have identity : Real.log (response 1) + trueGain - Real.log measured =
      trueGain - scalarGain (Real.log measured) := by
    unfold scalarGain
    ring
  rwa [identity] at bound

/-- An uncertain additive readout correction contributes its own error
budget in addition to the amplitude-to-log conversion. -/
theorem corrected_log_error_of_amplitude
    {L measured truth eps trueKappa measuredKappa epsK : ℝ}
    (positive : 0 < L) (measuredFloor : L ≤ measured)
    (epsNonnegative : 0 ≤ eps) (epsSmall : eps < L)
    (amplitudeError : |truth - measured| ≤ eps)
    (correctionError : |trueKappa - measuredKappa| ≤ epsK) :
    |(Real.log truth + trueKappa) - (Real.log measured + measuredKappa)| ≤
      eps / (L - eps) + epsK := by
  have logarithm := abs_le.mp ((log_error_of_amplitude positive measuredFloor
    epsNonnegative epsSmall amplitudeError).2)
  have correction := abs_le.mp correctionError
  exact abs_le.mpr ⟨by linarith [logarithm.1, correction.1],
    by linarith [logarithm.2, correction.2]⟩

/-- If the ideal readout includes a correction `trueKappa`, its amplitude
is `response 1 * exp (trueGain - trueKappa)`. The reported correction need
only approximate it within the separately supplied `epsK` budget. -/
theorem scalarGain_error_of_amplitude_with_correction
    {L measured trueGain eps trueKappa measuredKappa epsK : ℝ}
    (positive : 0 < L) (measuredFloor : L ≤ measured)
    (epsNonnegative : 0 ≤ eps) (epsSmall : eps < L)
    (amplitudeError : |response 1 * Real.exp (trueGain - trueKappa) - measured| ≤ eps)
    (correctionError : |trueKappa - measuredKappa| ≤ epsK) :
    |trueGain - scalarGain (Real.log measured + measuredKappa)| ≤
      eps / (L - eps) + epsK := by
  have bound := corrected_log_error_of_amplitude positive measuredFloor epsNonnegative
    epsSmall amplitudeError correctionError
  rw [Real.log_mul response_one_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at bound
  have identity : (Real.log (response 1) + (trueGain - trueKappa) + trueKappa) -
      (Real.log measured + measuredKappa) =
      trueGain - scalarGain (Real.log measured + measuredKappa) := by
    unfold scalarGain
    ring
  rwa [identity] at bound

end ReusableController.PhysicalEvaluator
