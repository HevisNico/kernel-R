import KernelR.HybridExecutionTools
import KernelR.HybridEnvelope

/-! Main READY comparisons with smooth upper and lower drives across actual traces. -/
namespace KernelR.Hybrid
open Set MeasureTheory


/-- Comparison with a smooth upper current. It is harmless to retain that
tail after the physical raw end, since this is only an upper bound. -/
theorem Flow.ready_drive_upper {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (hm : s.main i = .ready) (initial amplitude origin : ℝ)
    (hi : s.x i .q ≤ readyPulse initial amplitude origin s.time)
    (hd : ∀ t ∈ Ico s.time u.time,
      tailDrive s (f.path t) i t ≤ amplitude * a * Real.exp (-a * (t - origin))) :
    ∀ t ∈ Icc s.time u.time, f.path t i .q ≤ readyPulse initial amplitude origin t := by
  apply linear_comparison_of_right_derivatives (rate := 1 / 2)
    (lower := fun t => (1 / 2) * (1 / 10) + tailDrive s (f.path t) i t)
    (upper := fun t => (1 / 2) * (1 / 10) + amplitude * a * Real.exp (-a * (t - origin)))
    (f.continuous i .q)
    (fun t _ => (readyPulse_derivative initial amplitude origin t).continuousAt.continuousWithinAt)
    (fun t ht => (f.ready_right_derivative i hm t ht).congr_deriv (by ring))
    (fun t _ => (readyPulse_derivative initial amplitude origin t).hasDerivWithinAt.congr_deriv (by ring))
    (by simpa only [f.initial] using hi)
    (fun t ht => add_le_add (le_refl _) (hd t ht))

theorem Execution.ready_drive_upper {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .ready) (initial amplitude origin : ℝ)
    (hi : s.x i .q ≤ readyPulse initial amplitude origin s.time)
    (hd : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t ≤ amplitude * a * Real.exp (-a * (t - origin)))) :
    u.x i .q ≤ readyPulse initial amplitude origin u.time := by
  induction e with
  | nil => exact hi
  | cons move rest ih => cases move with
    | flow f =>
      apply ih hm.2 _ hd.2
      simpa only [f.final] using f.ready_drive_upper i hm.1 initial amplitude origin hi hd.1
        _ ⟨f.positive.le, le_rfl⟩
    | jump j =>
      exact ih hm (by simpa only [j.physical_continuous, j.time_unchanged] using hi) hd

theorem Flow.ready_drive_lower {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (hm : s.main i = .ready) (initial amplitude origin : ℝ)
    (hi : readyPulse initial amplitude origin s.time ≤ s.x i .q)
    (hd : ∀ t ∈ Ico s.time u.time,
      amplitude * a * Real.exp (-a * (t - origin)) ≤ tailDrive s (f.path t) i t) :
    ∀ t ∈ Icc s.time u.time, readyPulse initial amplitude origin t ≤ f.path t i .q := by
  apply linear_comparison_of_right_derivatives (rate := 1 / 2)
    (lower := fun t => (1 / 2) * (1 / 10) + amplitude * a * Real.exp (-a * (t - origin)))
    (upper := fun t => (1 / 2) * (1 / 10) + tailDrive s (f.path t) i t)
    (fun t _ => (readyPulse_derivative initial amplitude origin t).continuousAt.continuousWithinAt)
    (f.continuous i .q)
    (fun t _ => (readyPulse_derivative initial amplitude origin t).hasDerivWithinAt.congr_deriv (by ring))
    (fun t ht => (f.ready_right_derivative i hm t ht).congr_deriv (by ring))
    (by simpa only [f.initial] using hi)
    (fun t ht => add_le_add (le_refl _) (hd t ht))

theorem Execution.ready_drive_lower {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .ready) (initial amplitude origin : ℝ)
    (hi : readyPulse initial amplitude origin s.time ≤ s.x i .q)
    (hd : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      amplitude * a * Real.exp (-a * (t - origin)) ≤ tailDrive v (f.path t) i t)) :
    readyPulse initial amplitude origin u.time ≤ u.x i .q := by
  induction e with
  | nil => exact hi
  | cons move rest ih => cases move with
    | flow f =>
      apply ih hm.2 _ hd.2
      simpa only [f.final] using f.ready_drive_lower i hm.1 initial amplitude origin hi hd.1
        _ ⟨f.positive.le, le_rfl⟩
    | jump j => exact ih hm (by simpa only [j.physical_continuous,j.time_unchanged] using hi) hd

theorem Execution.raw_active_before {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ) (hr : s.raw i p = some origin)
    (ht : u.time < origin + 1) : e.AllFlows (fun {v _w} _ => v.raw i p = some origin) := by
  induction e with
  | nil => trivial
  | cons move rest ih => cases move with
    | flow f => exact ⟨hr,ih (by simpa only [f.raw_fixed] using hr) ht⟩
    | jump j => exact ih (j.raw_persists i p origin hr
        (by rw [← j.time_unchanged]; exact rest.time_monotone.trans_lt ht)) ht

end KernelR.Hybrid
