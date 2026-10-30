import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

namespace KernelR

def reserveDerivative (E W : ℝ) : ℝ := 10 * (100 - E) - W

theorem reserve_lower_points_inward {W : ℝ} (hW : W < 500) :
    0 < reserveDerivative 50 W := by dsimp [reserveDerivative]; linarith

theorem reserve_upper_points_inward {W : ℝ} (hW : 0 ≤ W) :
    reserveDerivative 100 W ≤ 0 := by dsimp [reserveDerivative]; linarith

theorem gate_open_on_reserve_interval {E : ℝ} (h : 50 ≤ E ∧ E ≤ 100) : 0 < E := by linarith [h.1]

/-- Constant worst-case work gives an explicit comparison trajectory. -/
noncomputable def reserveEnvelope (E₀ W t : ℝ) : ℝ :=
  (100 - W / 10) + (E₀ - (100 - W / 10)) * Real.exp (-10 * t)

theorem reserve_envelope_lower {E₀ W t : ℝ}
    (hE : 50 ≤ E₀) (hW : W ≤ 500) (ht : 0 ≤ t) :
    50 ≤ reserveEnvelope E₀ W t := by
  have he0 := (Real.exp_pos (-10 * t)).le
  have he1 : Real.exp (-10 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hbase : 50 ≤ 100 - W / 10 := by linarith
  have h₁ := mul_nonneg (sub_nonneg.mpr hE) he0
  have h₂ := mul_nonneg (sub_nonneg.mpr hbase) (sub_nonneg.mpr he1)
  dsimp [reserveEnvelope]; nlinarith

theorem reserve_envelope_upper {E₀ W t : ℝ}
    (hE : E₀ ≤ 100) (hW : 0 ≤ W) (ht : 0 ≤ t) :
    reserveEnvelope E₀ W t ≤ 100 := by
  have he0 := (Real.exp_pos (-10 * t)).le
  have he1 : Real.exp (-10 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h₁ := mul_nonneg (sub_nonneg.mpr hE) he0
  have h₂ := mul_nonneg hW (sub_nonneg.mpr he1)
  dsimp [reserveEnvelope]; nlinarith

/-- Explicit comparison is a hypothesis, not an unproved global ODE invariant. -/
theorem reserve_positive_of_comparison {E E₀ W t : ℝ}
    (hE₀ : 50 ≤ E₀) (hW : W ≤ 500) (ht : 0 ≤ t)
    (hcomparison : reserveEnvelope E₀ W t ≤ E) : 0 < E := by
  have h := reserve_envelope_lower hE₀ hW ht
  linarith

/-- Integrating-factor barrier on an interval where a derivative is available. -/
theorem nonnegative_of_linear_barrier {f d : ℝ → ℝ} {c T : ℝ}
    (hT : 0 ≤ T) (hinit : 0 ≤ f 0)
    (hd : ∀ t ∈ Set.Icc 0 T, HasDerivAt f (d t) t)
    (hbarrier : ∀ t ∈ Set.Icc 0 T, -c * f t ≤ d t) : 0 ≤ f T := by
  let F : ℝ → ℝ := fun t => f t * Real.exp (c * t)
  have hD (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      HasDerivAt F ((d t + c * f t) * Real.exp (c * t)) t := by
    convert (hd t ht).mul (((hasDerivAt_id t).const_mul c).exp) using 1 <;>
      dsimp [F] <;> first | rfl | ring
  have hm : MonotoneOn F (Set.Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (hD t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hD t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => mul_nonneg (by linarith [hbarrier t (interior_subset ht)])
        (Real.exp_pos _).le)
  have h := hm (show (0 : ℝ) ∈ Set.Icc 0 T from ⟨le_rfl, hT⟩)
    (show T ∈ Set.Icc 0 T from ⟨hT, le_rfl⟩) hT
  have hprod : 0 ≤ f T * Real.exp (c * T) := by
    simpa [F] using hinit.trans (by simpa [F] using h)
  exact nonneg_of_mul_nonneg_left hprod (Real.exp_pos _)

/-- A genuine ODE consequence on a smooth interval. Hybrid event boundaries
still require piecewise composition and proof that the work bound holds. -/
theorem reserve_invariant_on_smooth_interval {E W : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hinit : 50 ≤ E 0 ∧ E 0 ≤ 100)
    (hflow : ∀ t ∈ Set.Icc 0 T, HasDerivAt E (10 * (100 - E t) - W t) t)
    (hwork : ∀ t ∈ Set.Icc 0 T, 0 ≤ W t ∧ W t ≤ 500) :
    50 ≤ E T ∧ E T ≤ 100 := by
  have hlo := nonnegative_of_linear_barrier (c := 10) (f := fun t => E t - 50)
    (d := fun t => 10 * (100 - E t) - W t) hT (by linarith [hinit.1])
    (fun t ht => (hflow t ht).sub_const 50)
    (fun t ht => by linarith [(hwork t ht).2])
  have hhi := nonnegative_of_linear_barrier (c := 10) (f := fun t => 100 - E t)
    (d := fun t => -(10 * (100 - E t) - W t)) hT (by linarith [hinit.2])
    (fun t ht => (hflow t ht).const_sub 100)
    (fun t ht => by linarith [(hwork t ht).1])
  constructor <;> linarith

end KernelR
