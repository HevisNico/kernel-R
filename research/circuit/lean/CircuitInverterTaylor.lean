import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Alternating Taylor bounds of `exp (-x)` for every `x ≥ 0`: the partial sums
with an even number of terms are lower bounds and those with an odd number are
upper bounds. In particular the degree-5 sum is a lower bound and the degree-6
sum an upper bound, the `expLo` and `expHi` of the instance gate. The proof is by
induction on the derivative: `(-1)^n (exp (-x) - T_n x)` has derivative
`(-1)^(n-1) (exp (-x) - T_(n-1) x)` and vanishes at `0`. -/

namespace KernelR.Circuit

open Finset

/-- The partial sum of `exp (-x)` with `n` terms. -/
noncomputable def expNegSum (n : ℕ) (x : ℝ) : ℝ := ∑ m ∈ range n, (-x) ^ m / (m.factorial : ℝ)

theorem expNegSum_zero_point (n : ℕ) : expNegSum (n + 1) 0 = 1 := by
  simp [expNegSum, sum_range_succ']

theorem hasDerivAt_expNegSum (n : ℕ) (x : ℝ) :
    HasDerivAt (expNegSum (n + 1)) (-expNegSum n x) x := by
  induction n with
  | zero =>
    have : expNegSum 1 = fun _ => 1 := by funext y; simp [expNegSum]
    rw [this]; simpa [expNegSum] using hasDerivAt_const x (1 : ℝ)
  | succ n ih =>
    have split : expNegSum (n + 2) = fun y => expNegSum (n + 1) y + (-y) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
      funext y; simp only [expNegSum, sum_range_succ]
    rw [split]
    have term : HasDerivAt (fun y : ℝ => (-y) ^ (n + 1) / ((n + 1).factorial : ℝ))
        (-((-x) ^ n / (n.factorial : ℝ))) x := by
      have p := ((hasDerivAt_neg' x).fun_pow (n + 1)).div_const ((n + 1).factorial : ℝ)
      convert p using 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    convert ih.add term using 1
    simp only [expNegSum, sum_range_succ]
    ring

/-- The signed remainder `(-1)^n (exp (-x) - T_n x)` is nonnegative for `x ≥ 0`. -/
theorem expNeg_signed_remainder_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (-1 : ℝ) ^ n * (Real.exp (-x) - expNegSum n x) := by
  induction n generalizing x with
  | zero => simp [expNegSum, (Real.exp_pos _).le]
  | succ n ih =>
    set f : ℝ → ℝ := fun y => (-1 : ℝ) ^ (n + 1) * (Real.exp (-y) - expNegSum (n + 1) y)
    have deriv : ∀ y, HasDerivAt f ((-1 : ℝ) ^ n * (Real.exp (-y) - expNegSum n y)) y := by
      intro y
      have e : HasDerivAt (fun y => Real.exp (-y)) (-Real.exp (-y)) y := by
        simpa using (hasDerivAt_neg y).exp
      have d := (e.sub (hasDerivAt_expNegSum n y)).const_mul ((-1 : ℝ) ^ (n + 1))
      convert d using 1
      ring
    have mono : MonotoneOn f (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact (fun y _ => (deriv y).continuousAt.continuousWithinAt)
      · exact (fun y _ => (deriv y).differentiableAt.differentiableWithinAt)
      · intro y hy
        rw [interior_Ici] at hy
        rw [(deriv y).deriv]
        exact ih (le_of_lt hy)
    have atZero : f 0 = 0 := by
      simp only [f, neg_zero, Real.exp_zero, expNegSum_zero_point, sub_self, mul_zero]
    have := mono (Set.self_mem_Ici) (show x ∈ Set.Ici (0 : ℝ) from hx) hx
    rw [atZero] at this
    exact this

/-- The gate's degree-5 lower bound. -/
theorem expNegSum_six_le {x : ℝ} (hx : 0 ≤ x) : expNegSum 6 x ≤ Real.exp (-x) := by
  have := expNeg_signed_remainder_nonneg 6 hx
  norm_num at this
  linarith

/-- The gate's degree-6 upper bound. -/
theorem exp_le_expNegSum_seven {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ expNegSum 7 x := by
  have := expNeg_signed_remainder_nonneg 7 hx
  norm_num at this
  linarith

/-- The two sums in the explicit form of the gate. -/
theorem expNegSum_six_eq (x : ℝ) :
    expNegSum 6 x = 1 - x + x * x / 2 - x * x * x / 6 + x * x * x * x / 24 - x * x * x * x * x / 120 := by
  simp [expNegSum, sum_range_succ, Nat.factorial]
  ring

theorem expNegSum_seven_eq (x : ℝ) :
    expNegSum 7 x = expNegSum 6 x + x * x * x * x * x * x / 720 := by
  simp [expNegSum, sum_range_succ, Nat.factorial]
  ring

end KernelR.Circuit
