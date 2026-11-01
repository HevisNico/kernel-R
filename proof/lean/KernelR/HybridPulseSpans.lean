import KernelR.HybridPrefix
import KernelR.HybridReady

/-! Canonical sensor responses over actual finite spans, with the same raw
origin retained across other-cell and main-mode events. -/
namespace KernelR.Hybrid
open Set

theorem response_add (x y : ℝ) :
    response (x + y) = response x * Real.exp (-(1 / 2) * y) +
      Real.exp (-a * x) * response y := by
  unfold response
  rw [mul_add, mul_add, Real.exp_add, Real.exp_add]
  ring

theorem auxPulse_formula (initial amplitude start t : ℝ) :
    auxPulse initial amplitude start t = 1 / 40 +
      (initial - 1 / 40) * Real.exp (-(1 / 2) * (t - start)) + amplitude * response (t - start) := by
  dsimp [auxPulse, readyPulse]
  ring

theorem auxPulse_restart (initial amplitude start cut t : ℝ) :
    auxPulse (auxPulse initial amplitude start cut)
      (amplitude * Real.exp (-a * (cut - start))) cut t = auxPulse initial amplitude start t := by
  simp only [auxPulse_formula]
  rw [show t - start = (cut - start) + (t - cut) by ring, response_add, mul_add, Real.exp_add]
  ring

theorem attenuation_split (rate start cut t : ℝ) :
    Real.exp (-rate * (cut - start)) * Real.exp (-rate * (t - cut)) =
      Real.exp (-rate * (t - start)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- The exact READY sensor solution survives arbitrary legal jumps and flow
cuts before the actual raw endpoint. No prescribed auxiliary word is supplied. -/
theorem Execution.aux_ready_pulse_solution {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ) (hr : s.raw i p = some origin)
    (ht : u.time < origin + 1) (hm : e.AuxFlows i p .ready) :
    u.x i (.m p) = auxPulse (s.x i (.m p))
      ((θ i).inputGain p * Real.exp (-a * (s.time - origin))) s.time u.time := by
  induction e with
  | nil => simp [auxPulse_initial]
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      have hv : v.raw i p = some origin := by simpa only [f.raw_fixed] using hr
      have hrest := ih hv ht hm.2
      have hflow := f.aux_ready_single_pulse_solution i p origin hm.1 hr
        v.time ⟨f.positive.le, le_rfl⟩
      rw [f.final] at hflow
      have hamp : (θ i).inputGain p * Real.exp (-a * (v.time - origin)) =
          ((θ i).inputGain p * Real.exp (-a * (s.time - origin))) *
            Real.exp (-a * (v.time - s.time)) := by
        rw [mul_assoc, attenuation_split]
      rw [hrest, hflow, hamp, auxPulse_restart]
    | jump j =>
      have hv : v.raw i p = some origin := j.raw_persists i p origin hr
        (by rw [← j.time_unchanged]; exact rest.time_monotone.trans_lt ht)
      have hrest := ih hv ht hm
      simpa only [j.physical_continuous, j.time_unchanged] using hrest

end KernelR.Hybrid
