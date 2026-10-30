import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import KernelR.Recovery

/-! Closed forms on a single uninterrupted mode. Mode changes, routing and
existence of a complete hybrid execution remain outside this file. -/
namespace KernelR

noncomputable def decay (rate initial t : ℝ) : ℝ := initial * Real.exp (-rate * t)

theorem decay_initial (rate initial : ℝ) : decay rate initial 0 = initial := by
  simp [decay]

theorem decay_derivative (rate initial t : ℝ) :
    HasDerivAt (decay rate initial) (-rate * decay rate initial t) t := by
  unfold decay
  convert (((hasDerivAt_id t).const_mul (-rate)).exp).const_mul initial using 1 <;>
    dsimp <;> ring

theorem fast_finishes_at_quarter : decay (Real.log 4) 1 1 = 1 / 4 := by
  simp [decay, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]

theorem constant_slow_returns {b : ℝ} (hb : 0 < b) :
    decay b (1 / 4) (Real.log (5 / 2) / b) = 1 / 10 := by
  have h : -b * (Real.log (5 / 2) / b) = -Real.log (5 / 2) := by
    field_simp [ne_of_gt hb]
  rw [decay, h, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]
  norm_num

/-- SLOW charge as a function of accumulated recovery, allowing varying b. -/
noncomputable def slowCharge (accumulated : ℝ) : ℝ := (1 / 4) * Real.exp (-accumulated)

theorem slow_charge_above_rest_iff (accumulated : ℝ) :
    (1 / 10 : ℝ) < slowCharge accumulated ↔ accumulated < Real.log (5 / 2) := by
  have he : Real.exp (-Real.log (5 / 2)) = (2 / 5 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]; norm_num
  dsimp [slowCharge]
  constructor
  · intro hx
    have : Real.exp (-Real.log (5 / 2)) < Real.exp (-accumulated) := by rw [he]; linarith
    have := Real.exp_lt_exp.mp this
    linarith
  · intro hx
    have : Real.exp (-Real.log (5 / 2)) < Real.exp (-accumulated) :=
      Real.exp_lt_exp.mpr (by linarith)
    rw [he] at this
    linarith

theorem variable_slow_derivative {accumulated : ℝ → ℝ} {b t : ℝ}
    (h : HasDerivAt accumulated b t) :
    HasDerivAt (fun u => slowCharge (accumulated u))
      (-b * slowCharge (accumulated t)) t := by
  have hd := h.neg.exp.const_mul (1 / 4 : ℝ)
  convert hd using 1 <;> simp [slowCharge] <;> ring

theorem protected_charge_during_full_doses {accumulated : ℝ}
    (h : accumulated ≤ (8001 / 100000 : ℝ) * (17 / 2 - 1 - 3 / 10) +
      (18001 / 100000 : ℝ) * (419 / 300)) :
    (1 / 10 : ℝ) < slowCharge accumulated :=
  (slow_charge_above_rest_iff accumulated).2 (whole_mark_and_error_protected h)

end KernelR
