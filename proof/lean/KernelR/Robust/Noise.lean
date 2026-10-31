import KernelR.Doses

/-! Noise accounting in integral form. The balance premise applies also to
absolutely continuous solutions with measurable coefficients; no pointwise
derivative is required at a switching time. -/
namespace KernelR.Robust
open MeasureTheory intervalIntegral

theorem bounded_noise_integral {w : ℝ → ℝ} {s t ν : ℝ}
    (hst : s ≤ t) (hw : IntervalIntegrable w volume s t)
    (bound : ∀ x ∈ Set.Icc s t, -ν ≤ w x ∧ w x ≤ ν) :
    -ν * (t-s) ≤ (∫ x in s..t, w x) ∧ (∫ x in s..t, w x) ≤ ν * (t-s) := by
  have hlo := integral_mono_on hst (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ => -ν) volume s t) hw (fun x hx => (bound x hx).1)
  have hhi := integral_mono_on hst hw (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ => ν) volume s t) (fun x hx => (bound x hx).2)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
  constructor <;> nlinarith

theorem noisy_drain_integral {q current w : ℝ → ℝ} {s t : ℝ}
    (balance : q t - q s = -(∫ x in s..t, current x) + ∫ x in s..t, w x) :
    (∫ x in s..t, current x) = q s - q t + ∫ x in s..t, w x := by
  linarith

theorem noisy_error_dose {current noise ν duration : ℝ}
    (balance : current = 1 / 10 - 1 / 40 + noise)
    (bound : -ν * duration ≤ noise ∧ noise ≤ ν * duration) :
    3 / 5 - 8 * ν * duration ≤ 8 * current ∧
      8 * current ≤ 3 / 5 + 8 * ν * duration := by
  constructor <;> linarith [bound.1, bound.2]

theorem noisy_mark_dose {current noise ν duration : ℝ}
    (balance : current = 1 - 4 / 5 + noise)
    (bound : -ν * duration ≤ noise ∧ noise ≤ ν * duration) :
    1 / 10 - (1 / 2) * ν * duration ≤ current / 2 ∧
      current / 2 ≤ 1 / 10 + (1 / 2) * ν * duration := by
  constructor <;> linarith [bound.1, bound.2]

/-- The decayed initial error and the forcing share one invariant radius. -/
theorem ready_error_bound {initial forcing decay radius : ℝ}
    (hd : 0 ≤ decay ∧ decay ≤ 1)
    (hi : |initial| ≤ radius)
    (hf : |forcing| ≤ radius * (1 - decay)) :
    |decay * initial + forcing| ≤ radius := by
  calc
    |decay * initial + forcing| ≤ |decay * initial| + |forcing| := abs_add_le _ _
    _ = decay * |initial| + |forcing| := by rw [abs_mul, abs_of_nonneg hd.1]
    _ ≤ decay * radius + radius * (1 - decay) :=
      add_le_add (mul_le_mul_of_nonneg_left hi hd.1) hf
    _ = radius := by ring

theorem amplitude_error_bound {c α gain response : ℝ}
    (hc : |c - 1| ≤ α) (hg : 0 ≤ gain) (hr : 0 ≤ response) :
    |(c - 1) * gain * response| ≤ α * gain * response := by
  rw [abs_mul, abs_mul, abs_of_nonneg hg, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hg) hr

theorem charge_envelope {q reference additive amplitude radius α gain response : ℝ}
    (balance : q - reference = additive + amplitude)
    (ha : |additive| ≤ radius) (hb : |amplitude| ≤ α * gain * response) :
    |q - reference| ≤ radius + α * gain * response := by
  rw [balance]
  exact (abs_add_le _ _).trans (add_le_add ha hb)

end KernelR.Robust
