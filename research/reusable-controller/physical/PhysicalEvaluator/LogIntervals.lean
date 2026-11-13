import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Rationally checkable logarithm enclosures. The only transcendental step
is Mathlib's proved finite-series remainder estimate. For rational inputs,
the endpoint conditions below contain only rational arithmetic. -/
noncomputable section
namespace ReusableController.PhysicalEvaluator

/-- Transform a positive argument to the open unit interval. -/
def logArgument (x : ℝ) : ℝ := (x - 1) / (x + 1)

/-- Twice the odd Taylor sum, evaluated at `(x - 1) / (x + 1)`. -/
def logTaylor (n : ℕ) (x : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range n, logArgument x ^ (2 * i + 1) / (2 * i + 1)

/-- A proved bound on the absolute remainder of `logTaylor`. -/
def logTail (n : ℕ) (x : ℝ) : ℝ :=
  2 * |logArgument x| ^ (2 * n + 1) / (1 - logArgument x ^ 2)

theorem logArgument_abs_lt_one {x : ℝ} (positive : 0 < x) :
    |logArgument x| < 1 := by
  have denominator : 0 < x + 1 := by linarith
  rw [abs_lt]
  constructor
  · dsimp [logArgument]
    rw [lt_div_iff₀ denominator]
    linarith
  · dsimp [logArgument]
    rw [div_lt_iff₀ denominator]
    linarith

theorem logArgument_inverse {x : ℝ} (positive : 0 < x) :
    (1 + logArgument x) / (1 - logArgument x) = x := by
  have denominator : x + 1 ≠ 0 := by linarith
  dsimp [logArgument]
  field_simp
  ring

theorem logTaylor_error (n : ℕ) {x : ℝ} (positive : 0 < x) :
    |Real.log x - logTaylor n x| ≤ logTail n x := by
  have estimate := Real.sum_range_sub_log_div_le (logArgument_abs_lt_one positive) n
  rw [logArgument_inverse positive] at estimate
  have scaled := mul_le_mul_of_nonneg_left estimate (by norm_num : (0 : ℝ) ≤ 2)
  have identity : Real.log x - logTaylor n x =
      2 * (1 / 2 * Real.log x -
        ∑ i ∈ Finset.range n, logArgument x ^ (2 * i + 1) / (2 * i + 1)) := by
    dsimp [logTaylor]
    ring
  rw [identity, abs_mul]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [logTail, mul_div_assoc] using scaled

/-- Both numerical hypotheses can be discharged with `norm_num` after
unfolding the finite sum, for rational `x`, `lo`, and `hi`. -/
theorem log_bounds_of_taylor (n : ℕ) {x lo hi : ℝ}
    (positive : 0 < x)
    (lower : lo ≤ logTaylor n x - logTail n x)
    (upper : logTaylor n x + logTail n x ≤ hi) :
    lo ≤ Real.log x ∧ Real.log x ≤ hi := by
  have bounds := abs_le.mp (logTaylor_error n positive)
  constructor <;> linarith [bounds.1, bounds.2]

/-- Enclose the logarithm of an unknown positive value using two rational
endpoints. Each endpoint may use its own finite truncation length. -/
theorem logInterval (nL nU : ℕ) {L x U lo hi : ℝ}
    (positive : 0 < L) (lowerEndpoint : L ≤ x) (upperEndpoint : x ≤ U)
    (lower : lo ≤ logTaylor nL L - logTail nL L)
    (upper : logTaylor nU U + logTail nU U ≤ hi) :
    lo ≤ Real.log x ∧ Real.log x ≤ hi := by
  have xpos : 0 < x := lt_of_lt_of_le positive lowerEndpoint
  have upos : 0 < U := lt_of_lt_of_le xpos upperEndpoint
  have left := abs_le.mp (logTaylor_error nL positive)
  have right := abs_le.mp (logTaylor_error nU upos)
  have logLeft := Real.log_le_log positive lowerEndpoint
  have logRight := Real.log_le_log xpos upperEndpoint
  constructor <;> linarith [left.1, right.2]

/-- Invert rationally checked logarithm enclosures to bound an exponential.
This also applies when the exponent is negative. -/
theorem expInterval (nL nU : ℕ) {L x U : ℝ}
    (lowerPositive : 0 < L) (upperPositive : 0 < U)
    (lower : logTaylor nL L + logTail nL L ≤ x)
    (upper : x ≤ logTaylor nU U - logTail nU U) :
    L ≤ Real.exp x ∧ Real.exp x ≤ U := by
  have left := abs_le.mp (logTaylor_error nL lowerPositive)
  have right := abs_le.mp (logTaylor_error nU upperPositive)
  have logLeft : Real.log L ≤ x := by linarith [left.2]
  have logRight : x ≤ Real.log U := by linarith [right.1]
  constructor
  · simpa only [Real.exp_log lowerPositive] using Real.exp_le_exp.mpr logLeft
  · simpa only [Real.exp_log upperPositive] using Real.exp_le_exp.mpr logRight

/-- A rational arithmetic check of the six-term formula at the lower end of
the intended gain-input range. No floating-point logarithm is used. -/
theorem log_seven_tenths_bounds :
    -(356674945 / 1000000000 : ℝ) ≤ Real.log (7 / 10 : ℝ) ∧
      Real.log (7 / 10 : ℝ) ≤ -(356674943 / 1000000000 : ℝ) := by
  apply log_bounds_of_taylor 6 (by norm_num)
  all_goals norm_num [logTaylor, logTail, logArgument, Finset.sum_range_succ]

end ReusableController.PhysicalEvaluator
