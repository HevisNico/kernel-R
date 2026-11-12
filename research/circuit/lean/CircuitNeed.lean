import CircuitRobustness
import Search.VariableNeedTolerance

/-! The circuit residual budget has a discrete consequence: a common need
for a scalar probe, even when the residual differs at every write. -/

namespace KernelR.Circuit
open RecursiveLearning.Native

/-- Sensor-window uncertainty, imperfect current transfer and state linkage
contribute separately to the per-write dose budget. The sensor bound sigma
is deterministic, not a noise standard deviation. -/
theorem needAlong_of_circuit_tolerances {level level₀ d₀ a ℓ k η σ e : ℝ} {m : ℕ}
    (start stop z : ℕ → ℝ) (windows : ∀ j, ChargeWindow (start j) (stop j))
    (scale : 0 ≤ k)
    (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀)
    (handoff : ∀ j, |z (j + 1) - z j - (windows j).logGainStep k| ≤ e)
    (stepPos : ∀ j, 0 ≤ z (j + 1) - z j)
    (sensorTol : ∀ j, |k * ((windows j).sensorCharge (start j) -
      (windows j).sensorCharge (stop j)) - d₀| ≤ σ)
    (residual : ∀ j, |(windows j).residual| ≤ η)
    (gain : |z 0 - needCentre level₀ d₀ m| ≤ a)
    (levelTol : |level - level₀| ≤ ℓ)
    (room : a + m * (k * η + σ + e) + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2) :
    NeedAlong level z m := by
  apply needAlong_of_step_tolerance z fire fire₀ stepPos gain ?_ levelTol room
  intro j
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp (handoff j)
  obtain ⟨hs₁, hs₂⟩ := abs_le.mp (sensorTol j)
  obtain ⟨hd₁, hd₂⟩ := abs_le.mp ((windows j).dose_error scale (residual j))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- If the calibrated log-gain states match the circuit window increments,
each sensor window has nominal dose d0 and each charge residual is at most
eta, then b = k * eta suffices in the original need-tolerance budget.
The state linkage must account for inter-window drift; it is not automatic. -/
theorem needAlong_of_circuit_residual {level level₀ d₀ a ℓ k η : ℝ} {m : ℕ}
    (start stop z : ℕ → ℝ) (windows : ∀ j, ChargeWindow (start j) (stop j))
    (scale : 0 ≤ k)
    (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀)
    (step : ∀ j, z (j + 1) - z j = (windows j).logGainStep k)
    (stepPos : ∀ j, 0 ≤ z (j + 1) - z j)
    (nominal : ∀ j, k * ((windows j).sensorCharge (start j) -
      (windows j).sensorCharge (stop j)) = d₀)
    (residual : ∀ j, |(windows j).residual| ≤ η)
    (gain : |z 0 - needCentre level₀ d₀ m| ≤ a)
    (levelTol : |level - level₀| ≤ ℓ)
    (room : a + m * (k * η) + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2) :
    NeedAlong level z m := by
  apply needAlong_of_step_tolerance z fire fire₀ stepPos gain ?_ levelTol room
  intro j
  rw [step j]
  simpa only [nominal j] using (windows j).dose_error scale (residual j)

/-- If the window-to-state map has additional log-gain error e (calibration,
inter-window drift, or both), that error must be added to b. -/
theorem needAlong_of_circuit_residual_and_handoff {level level₀ d₀ a ℓ k η e : ℝ} {m : ℕ}
    (start stop z : ℕ → ℝ) (windows : ∀ j, ChargeWindow (start j) (stop j))
    (scale : 0 ≤ k)
    (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀)
    (handoff : ∀ j, |z (j + 1) - z j - (windows j).logGainStep k| ≤ e)
    (stepPos : ∀ j, 0 ≤ z (j + 1) - z j)
    (nominal : ∀ j, k * ((windows j).sensorCharge (start j) -
      (windows j).sensorCharge (stop j)) = d₀)
    (residual : ∀ j, |(windows j).residual| ≤ η)
    (gain : |z 0 - needCentre level₀ d₀ m| ≤ a)
    (levelTol : |level - level₀| ≤ ℓ)
    (room : a + m * (k * η + e) + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2) :
    NeedAlong level z m := by
  apply needAlong_of_step_tolerance z fire fire₀ stepPos gain ?_ levelTol room
  intro j
  have hc := abs_le.mp (handoff j)
  have hd := (windows j).dose_error scale (residual j)
  rw [nominal j] at hd
  obtain ⟨hd₁, hd₂⟩ := abs_le.mp hd
  exact abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩

end KernelR.Circuit
