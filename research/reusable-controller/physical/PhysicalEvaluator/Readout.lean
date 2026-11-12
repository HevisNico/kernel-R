import PhysicalEvaluator.LogIntervals

/-! Certified arithmetic for the reported scalar readout formula.
These results bound that formula; they do not identify it with an actual
transistor-state gain without a separate physical correspondence premise. -/
noncomputable section
namespace ReusableController.PhysicalEvaluator

def reportedReadGain (q c duration kappa : ℝ) : ℝ :=
  Real.log (q - 1 / 10 - (c - 1 / 10) * Real.exp (-duration)) + kappa

theorem expMinusHalf_bounds :
    (60653065 / 100000000 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) ∧
      Real.exp (-(1 / 2 : ℝ)) ≤ (60653067 / 100000000 : ℝ) := by
  apply expInterval 7 7 (by norm_num) (by norm_num)
  all_goals norm_num [logTaylor, logTail, logArgument, Finset.sum_range_succ]

theorem expMinusThreeEighths_bounds :
    (68728927 / 100000000 : ℝ) ≤ Real.exp (-(3 / 8 : ℝ)) ∧
      Real.exp (-(3 / 8 : ℝ)) ≤ (68728929 / 100000000 : ℝ) := by
  apply expInterval 6 6 (by norm_num) (by norm_num)
  all_goals norm_num [logTaylor, logTail, logArgument, Finset.sum_range_succ]

/-- Bound the scalar gain formula from an exponential enclosure and two
rational logarithm endpoint checks. Charge above rest makes the exponential
correction monotone, so its upper bound gives the lower logarithm argument.
`q` and `c` can be exact reported values or variables with separately proved
argument bounds. -/
theorem reportedReadGain_bounds (nL nU : ℕ)
    {q c duration kappa eLo eHi xLo xHi yLo yHi : ℝ}
    (chargeRest : 1 / 10 ≤ c)
    (expLower : eLo ≤ Real.exp (-duration))
    (expUpper : Real.exp (-duration) ≤ eHi)
    (argumentPositive : 0 < xLo)
    (argumentLower : xLo ≤ q - 1 / 10 - (c - 1 / 10) * eHi)
    (argumentUpper : q - 1 / 10 - (c - 1 / 10) * eLo ≤ xHi)
    (logLower : yLo ≤ logTaylor nL xLo - logTail nL xLo)
    (logUpper : logTaylor nU xHi + logTail nU xHi ≤ yHi) :
    yLo + kappa ≤ reportedReadGain q c duration kappa ∧
      reportedReadGain q c duration kappa ≤ yHi + kappa := by
  have coefficient : 0 ≤ c - 1 / 10 := sub_nonneg.mpr chargeRest
  have correctionLower := mul_le_mul_of_nonneg_left expLower coefficient
  have correctionUpper := mul_le_mul_of_nonneg_left expUpper coefficient
  have actualLower : xLo ≤ q - 1 / 10 - (c - 1 / 10) * Real.exp (-duration) := by
    linarith
  have actualUpper : q - 1 / 10 - (c - 1 / 10) * Real.exp (-duration) ≤ xHi := by
    linarith
  have bounds := logInterval nL nU argumentPositive actualLower actualUpper logLower logUpper
  dsimp [reportedReadGain]
  constructor <;> linarith [bounds.1, bounds.2]

end ReusableController.PhysicalEvaluator
