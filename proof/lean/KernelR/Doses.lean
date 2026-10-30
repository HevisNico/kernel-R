import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! Endpoint identities and retained memory. The integral-to-charge balance is
derived from a derivative assumption using the fundamental theorem of calculus. -/
namespace KernelR
open MeasureTheory intervalIntegral

noncomputable def errorDose : ℝ := 8 * ((1 / 10 : ℝ) - 1 / 40)
noncomputable def markDose : ℝ := (1 / 2 : ℝ) * (1 - 4 / 5)

theorem errorDose_exact : errorDose = 3 / 5 := by norm_num [errorDose]
theorem markDose_exact : markDose = 1 / 10 := by norm_num [markDose]
theorem three_error_doses : 3 * errorDose = 9 / 5 := by norm_num [errorDose]

/-- Charge balance is sufficient for a full ERROR dose, independently of its rate. -/
theorem error_dose_of_balance {currentIntegral : ℝ}
    (hbalance : currentIntegral = (1 / 10 : ℝ) - 1 / 40) :
    8 * currentIntegral = 3 / 5 := by rw [hbalance]; norm_num

theorem mark_dose_of_balance {currentIntegral : ℝ}
    (hbalance : currentIntegral = (1 : ℝ) - 4 / 5) :
    (1 / 2 : ℝ) * currentIntegral = 1 / 10 := by rw [hbalance]; norm_num

/-- The general endpoint identity, with the analytic hypotheses exposed. -/
theorem drain_integral {charge current : ℝ → ℝ} {s t : ℝ}
    (hd : ∀ x ∈ Set.uIcc s t, HasDerivAt charge (-current x) x)
    (hi : IntervalIntegrable (fun x => -current x) volume s t) :
    (∫ x in s..t, current x) = charge s - charge t := by
  have h := integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem full_error_integral {charge current : ℝ → ℝ} {s t : ℝ}
    (hd : ∀ x ∈ Set.uIcc s t, HasDerivAt charge (-current x) x)
    (hi : IntervalIntegrable (fun x => -current x) volume s t)
    (hs : charge s = 1 / 10) (ht : charge t = 1 / 40) :
    8 * (∫ x in s..t, current x) = 3 / 5 := by
  rw [drain_integral hd hi, hs, ht]; norm_num

theorem full_mark_integral {charge current : ℝ → ℝ} {s t : ℝ}
    (hd : ∀ x ∈ Set.uIcc s t, HasDerivAt charge (-current x) x)
    (hi : IntervalIntegrable (fun x => -current x) volume s t)
    (hs : charge s = 1) (ht : charge t = 4 / 5) :
    (1 / 2 : ℝ) * (∫ x in s..t, current x) = 1 / 10 := by
  rw [drain_integral hd hi, hs, ht]; norm_num

theorem partial_error_dose {m₁ m₂ : ℝ} (h₁ : m₁ ≤ 1 / 10)
    (h₂ : 1 / 40 ≤ m₂) (horder : m₂ ≤ m₁) :
    0 ≤ 8 * (m₁ - m₂) ∧ 8 * (m₁ - m₂) ≤ 3 / 5 := by constructor <;> linarith

theorem gain_after_three_doses (z : ℝ) :
    Real.exp (z + errorDose + errorDose + errorDose) = Real.exp z * Real.exp (9 / 5) := by
  have h : z + errorDose + errorDose + errorDose = z + 9 / 5 := by
    rw [errorDose_exact]; ring
  rw [h, Real.exp_add]

theorem gain_strictly_increases (z : ℝ) : Real.exp z < Real.exp (z + 9 / 5) := by
  apply Real.exp_lt_exp.mpr; linarith

theorem no_cap_change {x cap : ℝ} (h : x ≤ cap) : min cap x = x := min_eq_right h

theorem recovery_entry {b : ℝ} (h : (7999 / 100000 : ℝ) ≤ b ∧ b ≤ 8001 / 100000) :
    (17999 / 100000 : ℝ) ≤ b + markDose ∧ b + markDose ≤ 18001 / 100000 := by
  rw [markDose_exact]; constructor <;> linarith [h.1, h.2]

theorem exact_learning_preserves_initial_variation {z₀ z₁ η : ℝ}
    (h₀ : z₀ = Real.log (3 / 10) + η) (h₁ : z₁ = z₀ + 9 / 5) :
    Real.exp z₁ = (3 / 10 : ℝ) * Real.exp η * Real.exp (9 / 5) := by
  rw [h₁, h₀, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 10)]

end KernelR
