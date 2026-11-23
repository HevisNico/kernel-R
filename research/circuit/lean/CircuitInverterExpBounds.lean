import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! Rational bounds of `exp (-q)` for rational `q ∈ [0, 1]`, from Mathlib's
`Real.exp_bound`: the degree-`n - 1` Taylor polynomial, plus or minus the
remainder `q ^ n * (n + 1) / (n! * n)`. Both bounds are rationals that a gate can
evaluate by `decide`. -/

namespace KernelR.Circuit

open Finset

/-- The Taylor polynomial of `exp (-q)` with `n` terms, over `ℚ`, by recursion so
that the kernel evaluates it. -/
def expNegTaylor (q : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => expNegTaylor q n + (-q) ^ n / (n.factorial : ℚ)

theorem expNegTaylor_eq (q : ℚ) (n : ℕ) :
    expNegTaylor q n = ∑ m ∈ range n, (-q) ^ m / (m.factorial : ℚ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [expNegTaylor, ih, sum_range_succ]

/-- The remainder bound of `Real.exp_bound`, over `ℚ`. -/
def expNegRemainder (q : ℚ) (n : ℕ) : ℚ := q ^ n * ((n + 1 : ℚ) / ((n.factorial : ℚ) * n))

/-- A rational lower bound of `exp (-q)`. -/
def expNegLower (q : ℚ) (n : ℕ) : ℚ := expNegTaylor q n - expNegRemainder q n

/-- A rational upper bound of `exp (-q)`. -/
def expNegUpper (q : ℚ) (n : ℕ) : ℚ := expNegTaylor q n + expNegRemainder q n

theorem exp_neg_rat_bounds {q : ℚ} (nonneg : 0 ≤ q) (atMostOne : q ≤ 1) {n : ℕ} (positive : 0 < n) :
    ((expNegLower q n : ℚ) : ℝ) ≤ Real.exp (-(q : ℝ)) ∧
      Real.exp (-(q : ℝ)) ≤ ((expNegUpper q n : ℚ) : ℝ) := by
  have hq : |(-(q : ℝ))| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by exact_mod_cast nonneg)]
    exact_mod_cast atMostOne
  have bound := Real.exp_bound hq positive
  rw [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ q by exact_mod_cast nonneg)] at bound
  have taylor : ((expNegTaylor q n : ℚ) : ℝ) = ∑ m ∈ range n, (-(q : ℝ)) ^ m / (m.factorial : ℝ) := by
    simp [expNegTaylor_eq]
  have remainder : ((expNegRemainder q n : ℚ) : ℝ) =
      (q : ℝ) ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n)) := by
    simp [expNegRemainder]
  obtain ⟨lo, hi⟩ := abs_le.mp bound
  constructor
  · simp only [expNegLower, Rat.cast_sub, taylor, remainder]
    linarith
  · simp only [expNegUpper, Rat.cast_add, taylor, remainder]
    linarith

/-- Example: `exp (-1/2)` lies between the degree-5 bounds. -/
example : ((expNegLower (1 / 2) 6 : ℚ) : ℝ) ≤ Real.exp (-((1 / 2 : ℚ) : ℝ)) :=
  (exp_neg_rat_bounds (by norm_num) (by norm_num) (by norm_num)).1

example : expNegLower (1 / 2) 6 = 167681 / 276480 := by decide +kernel
example : expNegUpper (1 / 2) 6 = 33539 / 55296 := by decide +kernel

end KernelR.Circuit
