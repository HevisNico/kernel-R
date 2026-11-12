import KernelR.Doses

/-! A conditional, observable-level bridge from capacitor charge balance to
the ERROR dose of Kernel R. This file does not formalize SKY130 devices,
certify SPICE traces, or construct a hybrid execution. Charge is in coulombs;
the positive coefficient k converts a decrease of storage charge to log-gain.
For constant feedback capacitance Cf and inverse-voltage gain slope beta,
k = beta / Cf. The affine log-gain law is a calibration assumption. -/

namespace KernelR.Circuit
open MeasureTheory Set

/-- Two charge balances on a single write window. The sensor and the storage
capacitor may have different currents: their discrepancy is not hidden. -/
structure ChargeWindow (s t : ℝ) where
  ordered : s ≤ t
  sensorCharge : ℝ → ℝ
  storageCharge : ℝ → ℝ
  sensorCurrent : ℝ → ℝ
  writeCurrent : ℝ → ℝ
  sensor_derivative : ∀ x ∈ uIcc s t,
    HasDerivAt sensorCharge (-sensorCurrent x) x
  storage_derivative : ∀ x ∈ uIcc s t,
    HasDerivAt storageCharge (-writeCurrent x) x
  sensor_integrable : IntervalIntegrable (fun x => -sensorCurrent x) volume s t
  write_integrable : IntervalIntegrable (fun x => -writeCurrent x) volume s t

noncomputable def ChargeWindow.logGainStep {s t} (w : ChargeWindow s t) (k : ℝ) : ℝ :=
  k * (w.storageCharge s - w.storageCharge t)

noncomputable def ChargeWindow.residual {s t} (w : ChargeWindow s t) : ℝ :=
  (∫ x in s..t, w.writeCurrent x) - (∫ x in s..t, w.sensorCurrent x)

/-- Under the declared affine log-gain calibration, the storage step
multiplies gain by exp(step). This does not establish the calibration. -/
theorem ChargeWindow.calibrated_gain {s t} (w : ChargeWindow s t) (k reference : ℝ) :
    Real.exp (reference - k * w.storageCharge t) =
      Real.exp (reference - k * w.storageCharge s) * Real.exp (w.logGainStep k) := by
  rw [← Real.exp_add]
  congr 1
  simp only [ChargeWindow.logGainStep]
  ring

/-- Rate independence follows from the existing kernel charge-balance
theorem, with a separate term for imperfect current transfer. -/
theorem ChargeWindow.balance {s t} (w : ChargeWindow s t) (k : ℝ) :
    w.logGainStep k = k * (w.sensorCharge s - w.sensorCharge t) + k * w.residual := by
  have hs := KernelR.drain_integral w.sensor_derivative w.sensor_integrable
  have hw := KernelR.drain_integral w.storage_derivative w.write_integrable
  simp only [ChargeWindow.logGainStep, ChargeWindow.residual]
  rw [hs, hw]
  ring

/-- Ideal exposed steering transfers the whole sensor current. -/
theorem ChargeWindow.exposed_dose {s t} (w : ChargeWindow s t) (k : ℝ)
    (steering : ∀ x ∈ uIcc s t, w.writeCurrent x = w.sensorCurrent x) :
    w.logGainStep k = k * (w.sensorCharge s - w.sensorCharge t) := by
  have equal : (∫ x in s..t, w.writeCurrent x) = (∫ x in s..t, w.sensorCurrent x) :=
    intervalIntegral.integral_congr steering
  rw [w.balance, ChargeWindow.residual, equal]
  ring

/-- An ideal protected window writes no charge. This hypothesis concerns
the actual current, not merely the digital steering command. -/
theorem ChargeWindow.protected_step {s t} (w : ChargeWindow s t) (k : ℝ)
    (blocked : ∀ x ∈ uIcc s t, w.writeCurrent x = 0) :
    w.logGainStep k = 0 := by
  have zero : (∫ x in s..t, w.writeCurrent x) = 0 := by
    calc
      _ = ∫ _ in s..t, (0 : ℝ) := intervalIntegral.integral_congr blocked
      _ = 0 := by simp
  have hw := KernelR.drain_integral w.storage_derivative w.write_integrable
  simp only [ChargeWindow.logGainStep]
  rw [← hw, zero, mul_zero]

/-- A bound on transferred-charge error gives a log-gain dose budget. -/
theorem ChargeWindow.dose_error {s t} (w : ChargeWindow s t) {k η : ℝ}
    (scale : 0 ≤ k) (budget : |w.residual| ≤ η) :
    |w.logGainStep k - k * (w.sensorCharge s - w.sensorCharge t)| ≤ k * η := by
  rw [w.balance, add_sub_cancel_left, abs_mul, abs_of_nonneg scale]
  exact mul_le_mul_of_nonneg_left budget scale

/-- For protection with leakage, it is the total residual write charge
that matters; exact zero is unnecessary. -/
theorem ChargeWindow.protected_drift {s t} (w : ChargeWindow s t) {k η : ℝ}
    (scale : 0 ≤ k) (budget : |∫ x in s..t, w.writeCurrent x| ≤ η) :
    |w.logGainStep k| ≤ k * η := by
  have hw := KernelR.drain_integral w.storage_derivative w.write_integrable
  simp only [ChargeWindow.logGainStep]
  rw [← hw, abs_mul, abs_of_nonneg scale]
  exact mul_le_mul_of_nonneg_left budget scale

/-- With Cs in farads and beta in inverse volts, the physical dose is
beta * Cs / Cf times the realized voltage window. No value 0.6 is imposed. -/
theorem ChargeWindow.capacitor_dose {s t} (w : ChargeWindow s t)
    (β Cs Cf upper lower : ℝ)
    (steering : ∀ x ∈ uIcc s t, w.writeCurrent x = w.sensorCurrent x)
    (entry : w.sensorCharge s = Cs * upper)
    (exit : w.sensorCharge t = Cs * lower) :
    w.logGainStep (β / Cf) = (β * Cs / Cf) * (upper - lower) := by
  rw [w.exposed_dose (β / Cf) steering, entry, exit]
  ring

/-- This projection matches the kernel coefficient 8 at arbitrary endpoints.
It is an identity of the dose observable, not a full state refinement. -/
theorem ChargeWindow.kernel_dose_projection {s t} (w : ChargeWindow s t) (k : ℝ)
    (steering : ∀ x ∈ uIcc s t, w.writeCurrent x = w.sensorCurrent x) :
    w.logGainStep k = 8 * ((k / 8) * w.sensorCharge s - (k / 8) * w.sensorCharge t) := by
  rw [w.exposed_dose k steering]
  ring

/-- Recover the nominal kernel dose only when the normalized charge drop
actually equals its nominal window. The circuit campaign does not have it. -/
theorem ChargeWindow.nominal_kernel_dose {s t} (w : ChargeWindow s t) (k : ℝ)
    (steering : ∀ x ∈ uIcc s t, w.writeCurrent x = w.sensorCurrent x)
    (window : (k / 8) * w.sensorCharge s - (k / 8) * w.sensorCharge t =
      (1 / 10 : ℝ) - 1 / 40) :
    w.logGainStep k = 3 / 5 := by
  rw [w.kernel_dose_projection k steering]
  exact KernelR.error_dose_of_balance window

/-- The ideal design values, using 31.8 mV per log-gain unit. This is an
arithmetic consequence of a calibration, not a proof of that calibration. -/
theorem design_dose :
    ((1 / (318 / 10000) : ℝ) * (400 / 1000000000000000) /
      (30 / 1000000000000)) * (6 / 10 - 5 / 10) = 20 / 477 := by
  norm_num

theorem design_dose_below_read_budget : (20 / 477 : ℝ) < 1 / 20 := by norm_num

/-- A common additive offset cancels only if it is common to both realized
endpoints. This does not establish equal offsets for the transistor comparator. -/
theorem common_offset_cancels (upper lower offset : ℝ) :
    (upper + offset) - (lower + offset) = upper - lower := by ring

/-- Local per-window budgets compose through the actual log-gain sequence.
Every interval, including protected drift and inter-pulse leakage, must be
included or covered by its local budget. -/
theorem accumulated_error (z dose error : ℕ → ℝ) (n : ℕ)
    (stepBound : ∀ j < n, |z (j + 1) - z j - dose j| ≤ error j) :
    |z n - z 0 - ∑ j ∈ Finset.range n, dose j| ≤ ∑ j ∈ Finset.range n, error j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have prev := abs_le.mp (ih (fun j hj => stepBound j (Nat.lt_succ_of_lt hj)))
    have last := abs_le.mp (stepBound n (Nat.lt_succ_self n))
    simp only [Finset.sum_range_succ]
    exact abs_le.mpr ⟨by linarith [prev.1, last.1], by linarith [prev.2, last.2]⟩

end KernelR.Circuit
