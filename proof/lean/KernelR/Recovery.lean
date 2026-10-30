import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Recovery estimates proved over ℝ, using Mathlib's proved logarithm bounds.
Unlike the certificate endpoint checks, these bounds refer to the actual log.
The bounds on accumulated SLOW integrals are explicit hypotheses about a flow. -/
namespace KernelR

theorem log_recovery_bounds :
    (9162907315 / 10000000000 : ℝ) < Real.log (5 / 2) ∧
    Real.log (5 / 2) < 9162907323 / 10000000000 := by
  rw [Real.log_div (by norm_num : (5 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  constructor
  · linarith [Real.log_five_gt_d9, Real.log_two_lt_d9]
  · linarith [Real.log_five_lt_d9, Real.log_two_gt_d9]

theorem log_four_bounds :
    (13862943606 / 10000000000 : ℝ) < Real.log 4 ∧
    Real.log 4 < 13862943616 / 10000000000 := by
  rw [Real.log_four_eq]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

theorem stable_return_bound {b f : ℝ}
    (hb : (17999 / 100000 : ℝ) ≤ b) (hf : f ≤ 9 / 10) :
    f + 1 + Real.log (5 / 2) / b < 6990787 / 1000000 := by
  have hbpos : 0 < b := by linarith
  have hquot : Real.log (5 / 2) / b < 5090787 / 1000000 := by
    apply (div_lt_iff₀ hbpos).2
    nlinarith [log_recovery_bounds.2]
  linarith

theorem low_recovery_not_returned {integral : ℝ}
    (h : integral ≤ (8001 / 100000 : ℝ) * (17 / 2 - 1 - 3 / 10)) :
    integral < Real.log (5 / 2) := by linarith [log_recovery_bounds.1]

theorem whole_mark_and_error_protected {integral : ℝ}
    (h : integral ≤ (8001 / 100000 : ℝ) * (17 / 2 - 1 - 3 / 10) +
      (18001 / 100000 : ℝ) * (419 / 300)) :
    integral < Real.log (5 / 2) := by linarith [log_recovery_bounds.1]

theorem return_target_exceeded_by_three {integral : ℝ}
    (h : (7999 / 100000 : ℝ) * (15 / 2 - 1 - 9 / 10) +
      (17999 / 100000 : ℝ) * (3 - 47 / 900) ≤ integral) :
    Real.log (5 / 2) < integral := by linarith [log_recovery_bounds.2]

/-- The comparison bounds hold for every point in the independent parameter boxes. -/
theorem slow_upper_from_boxes {b₀ b₁ gap fire finish integral : ℝ}
    (hb₀ : 0 ≤ b₀ ∧ b₀ ≤ 8001 / 100000)
    (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 18001 / 100000)
    (hg : gap ≤ 17 / 2) (hf : (3 / 10 : ℝ) ≤ fire)
    (hu : 0 ≤ finish ∧ finish ≤ 419 / 300)
    (hflow : integral ≤ b₀ * (gap - 1 - fire) + b₁ * finish) :
    integral < Real.log (5 / 2) := by
  apply whole_mark_and_error_protected
  have hfirst : b₀ * (gap - 1 - fire) ≤ (8001 / 100000 : ℝ) * (17 / 2 - 1 - 3 / 10) := by
    calc
      _ ≤ b₀ * (17 / 2 - 1 - 3 / 10) := mul_le_mul_of_nonneg_left (by linarith) hb₀.1
      _ ≤ _ := mul_le_mul_of_nonneg_right hb₀.2 (by norm_num)
  have hsecond : b₁ * finish ≤ (18001 / 100000 : ℝ) * (419 / 300) :=
    mul_le_mul hb₁.2 hu.2 hu.1 (by norm_num)
  linarith

end KernelR
