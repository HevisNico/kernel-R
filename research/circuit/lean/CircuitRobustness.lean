import CircuitBridge

/-! Current and calibration budgets for the charge-to-dose bridge. These
are deterministic bounds on whole windows, not statistical confidence
intervals or bounds inferred from a finite set of simulations. -/

namespace KernelR.Circuit
open MeasureTheory Set

/-- An L1 current-transfer budget implies the signed residual budget.
Keeping the absolute value inside the integral prevents cancellation
from hiding large excursions of opposite signs. -/
theorem ChargeWindow.residual_of_current_error {s t} (w : ChargeWindow s t) {η : ℝ}
    (budget : (∫ x in s..t, |w.writeCurrent x - w.sensorCurrent x|) ≤ η) :
    |w.residual| ≤ η := by
  rw [ChargeWindow.residual, ← intervalIntegral.integral_sub w.write_integrable w.sensor_integrable]
  exact (intervalIntegral.abs_integral_le_integral_abs w.ordered).trans budget

/-- A uniform bound on the actual parasitic write current supplies a
retention budget proportional to the duration of the protected interval. -/
theorem ChargeWindow.protected_drift_of_current_bound {s t} (w : ChargeWindow s t)
    {k J : ℝ} (scale : 0 ≤ k)
    (currentBound : ∀ x ∈ Icc s t, |w.writeCurrent x| ≤ J) :
    |w.logGainStep k| ≤ k * (J * (t - s)) := by
  apply w.protected_drift scale
  have bound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := w.writeCurrent) (a := s) (b := t) (C := J) (by
      intro x hx
      rw [uIoc_of_le w.ordered] at hx
      simpa only [Real.norm_eq_abs] using currentBound x ⟨hx.1.le, hx.2⟩)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr w.ordered)] using bound

/-- Endpoint calibration errors add to the storage-derived log-gain step.
The true log-gain z need not be exactly affine in the storage coordinate. -/
theorem ChargeWindow.calibration_step_error {s t} (w : ChargeWindow s t)
    {z : ℝ → ℝ} {k reference εs εt : ℝ}
    (startFit : |z s - (reference - k * w.storageCharge s)| ≤ εs)
    (endFit : |z t - (reference - k * w.storageCharge t)| ≤ εt) :
    |z t - z s - w.logGainStep k| ≤ εs + εt := by
  obtain ⟨hs₁, hs₂⟩ := abs_le.mp startFit
  obtain ⟨ht₁, ht₂⟩ := abs_le.mp endFit
  simp only [ChargeWindow.logGainStep]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Compose current-transfer error with calibration error to control the
true log-gain increment, not just the capacitor proxy. -/
theorem ChargeWindow.actual_dose_error {s t} (w : ChargeWindow s t)
    {z : ℝ → ℝ} {k reference η εs εt : ℝ}
    (scale : 0 ≤ k) (budget : |w.residual| ≤ η)
    (startFit : |z s - (reference - k * w.storageCharge s)| ≤ εs)
    (endFit : |z t - (reference - k * w.storageCharge t)| ≤ εt) :
    |z t - z s - k * (w.sensorCharge s - w.sensorCharge t)| ≤ k * η + εs + εt := by
  have hc := abs_le.mp (w.calibration_step_error startFit endFit)
  have hd := abs_le.mp (w.dose_error scale budget)
  exact abs_le.mpr ⟨by linarith [hc.1, hd.1], by linarith [hc.2, hd.2]⟩

/-- Protected retention for the calibrated gain allows both residual
write charge and imperfect gain calibration. -/
theorem ChargeWindow.actual_protected_drift {s t} (w : ChargeWindow s t)
    {z : ℝ → ℝ} {k reference η εs εt : ℝ}
    (scale : 0 ≤ k) (budget : |∫ x in s..t, w.writeCurrent x| ≤ η)
    (startFit : |z s - (reference - k * w.storageCharge s)| ≤ εs)
    (endFit : |z t - (reference - k * w.storageCharge t)| ≤ εt) :
    |z t - z s| ≤ k * η + εs + εt := by
  have hc := abs_le.mp (w.calibration_step_error startFit endFit)
  have hd := abs_le.mp (w.protected_drift scale budget)
  exact abs_le.mpr ⟨by linarith [hc.1, hd.1], by linarith [hc.2, hd.2]⟩

/-- A log-gain budget controls the multiplicative gain error without
linearizing the exponential. -/
theorem gain_error_of_log_error {z reference ε : ℝ} (budget : |z - reference| ≤ ε) :
    |Real.exp z - Real.exp reference| ≤ Real.exp reference * (Real.exp ε - 1) := by
  obtain ⟨lower, upper⟩ := abs_le.mp budget
  have hi := Real.exp_le_exp.mpr (show z ≤ reference + ε by linarith)
  have lo := Real.exp_le_exp.mpr (show reference + (-ε) ≤ z by linarith)
  rw [Real.exp_add] at hi lo
  have convex : 2 ≤ Real.exp ε + Real.exp (-ε) := by
    linarith [Real.add_one_le_exp ε, Real.add_one_le_exp (-ε)]
  have scaled := mul_le_mul_of_nonneg_left convex (Real.exp_pos reference).le
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- On a read with frozen gains and the SAME admitted pulse shape, the
log-gain budget supplies an L1 current-error budget. Waveform mismatch,
gate timing and gain evolution during the read are separate obligations. -/
theorem current_budget_of_log_error {z reference ε t : ℝ} (pulse : ℝ → ℝ)
    (time : 0 ≤ t) (budget : |z - reference| ≤ ε) :
    (∫ u in 0..t, |Real.exp z * pulse u - Real.exp reference * pulse u|) ≤
      (Real.exp reference * (Real.exp ε - 1)) * (∫ u in 0..t, |pulse u|) := by
  have nonneg : 0 ≤ ∫ u in 0..t, |pulse u| :=
    intervalIntegral.integral_nonneg_of_forall time (fun u => abs_nonneg _)
  have split : (fun u => |Real.exp z * pulse u - Real.exp reference * pulse u|) =
      (fun u => |Real.exp z - Real.exp reference| * |pulse u|) := by
    funext u
    rw [← sub_mul, abs_mul]
  rw [split, intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_right (gain_error_of_log_error budget) nonneg

end KernelR.Circuit
