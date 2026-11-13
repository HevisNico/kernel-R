import PhysicalEvaluator.Readout
import PhysicalEvaluator.MeasuredGains
import PhysicalEvaluator.PeakError

namespace ReusableController.PhysicalEvaluator
open KernelR.Hybrid

noncomputable def correctedPeak (q c duration kappa : ℝ) : ℝ :=
  Real.exp kappa * (q - 1 / 10 - (c - 1 / 10) * Real.exp (-duration))

theorem correctedPeak_eq_exp_reportedReadGain {q c duration kappa : ℝ}
    (positive : 0 < q - 1 / 10 - (c - 1 / 10) * Real.exp (-duration)) :
    correctedPeak q c duration kappa = Real.exp (reportedReadGain q c duration kappa) := by
  rw [reportedReadGain, Real.exp_add, Real.exp_log positive]
  unfold correctedPeak
  ring

theorem correctedPeak_measurement_error
    {qTrue qMeasured cTrue cMeasured duration kappa epsilonQ epsilonC : ℝ}
    (peakError : |qTrue - qMeasured| ≤ epsilonQ)
    (chargeError : |cTrue - cMeasured| ≤ epsilonC) :
    |correctedPeak qTrue cTrue duration kappa -
        correctedPeak qMeasured cMeasured duration kappa| ≤
      Real.exp kappa * (epsilonQ + Real.exp (-duration) * epsilonC) := by
  have identity : correctedPeak qTrue cTrue duration kappa -
      correctedPeak qMeasured cMeasured duration kappa =
      Real.exp kappa * ((qTrue - qMeasured) - (cTrue - cMeasured) * Real.exp (-duration)) := by
    unfold correctedPeak
    ring
  rw [identity, abs_mul, abs_of_pos (Real.exp_pos kappa)]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos kappa))
  calc
    |(qTrue - qMeasured) - (cTrue - cMeasured) * Real.exp (-duration)| ≤
        |qTrue - qMeasured| + |(cTrue - cMeasured) * Real.exp (-duration)| := abs_sub _ _
    _ = |qTrue - qMeasured| + Real.exp (-duration) * |cTrue - cMeasured| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos (-duration))]
      ring
    _ ≤ epsilonQ + Real.exp (-duration) * epsilonC :=
      add_le_add peakError (mul_le_mul_of_nonneg_left chargeError (le_of_lt (Real.exp_pos _)))

theorem peak_residual_of_measurements
    {trueGain qTrue qMeasured cTrue cMeasured duration kappa epsilonModel epsilonQ epsilonC : ℝ}
    (modelError : |response 1 * Real.exp trueGain - correctedPeak qTrue cTrue duration kappa| ≤
      epsilonModel)
    (peakError : |qTrue - qMeasured| ≤ epsilonQ)
    (chargeError : |cTrue - cMeasured| ≤ epsilonC) :
    |response 1 * Real.exp trueGain - correctedPeak qMeasured cMeasured duration kappa| ≤
      epsilonModel + Real.exp kappa * (epsilonQ + Real.exp (-duration) * epsilonC) := by
  calc
    |response 1 * Real.exp trueGain - correctedPeak qMeasured cMeasured duration kappa| ≤
        |response 1 * Real.exp trueGain - correctedPeak qTrue cTrue duration kappa| +
          |correctedPeak qTrue cTrue duration kappa - correctedPeak qMeasured cMeasured duration kappa| :=
      abs_sub_le _ _ _
    _ ≤ epsilonModel + Real.exp kappa * (epsilonQ + Real.exp (-duration) * epsilonC) :=
      add_le_add modelError (correctedPeak_measurement_error peakError chargeError)

theorem gain_error_of_measurements
    {trueGain qTrue qMeasured cTrue cMeasured duration kappa epsilonModel epsilonQ epsilonC L epsilon : ℝ}
    (positive : 0 < L)
    (measuredFloor : L ≤ correctedPeak qMeasured cMeasured duration kappa)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonSmall : epsilon < L)
    (modelError : |response 1 * Real.exp trueGain - correctedPeak qTrue cTrue duration kappa| ≤
      epsilonModel)
    (peakError : |qTrue - qMeasured| ≤ epsilonQ)
    (chargeError : |cTrue - cMeasured| ≤ epsilonC)
    (budget : epsilonModel + Real.exp kappa * (epsilonQ + Real.exp (-duration) * epsilonC) ≤ epsilon) :
    |trueGain - scalarGain (reportedReadGain qMeasured cMeasured duration kappa)| ≤
      epsilon / (L - epsilon) := by
  have amplitudePositive : 0 < correctedPeak qMeasured cMeasured duration kappa :=
    lt_of_lt_of_le positive measuredFloor
  have signalPositive : 0 < qMeasured - 1 / 10 - (cMeasured - 1 / 10) * Real.exp (-duration) := by
    by_contra notPositive
    have nonpositive : correctedPeak qMeasured cMeasured duration kappa ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos kappa)) (not_lt.mp notPositive)
    linarith
  have residual := (peak_residual_of_measurements modelError peakError chargeError).trans budget
  have gainBound := scalarGain_error_of_amplitude positive measuredFloor epsilonNonnegative
    epsilonSmall residual
  rw [correctedPeak_eq_exp_reportedReadGain signalPositive, Real.log_exp] at gainBound
  exact gainBound

end ReusableController.PhysicalEvaluator
