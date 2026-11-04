import KernelR.HybridResponseBounds

/-! Strict upward crossings of the uncut scalar pulse responses. The proof
uses their damped derivative equation and a strictly higher later value.
The derivative refers to the smooth scalar response, before any hybrid jump.
-/
namespace KernelR.Hybrid
open Set

private theorem derivative_pos_of_later_value {f d forcing : ℝ → ℝ}
    {rate decay contact deadline : ℝ}
    (hf : ∀ t, HasDerivAt f (d t) t)
    (hd : ∀ t, HasDerivAt d (-rate * d t - decay * forcing t) t)
    (hdecay : 0 ≤ decay) (hforcing : ∀ t, 0 ≤ forcing t)
    (later : contact < deadline) (above : f contact < f deadline) :
    0 < d contact := by
  by_contra not_positive
  have initial : d contact ≤ 0 := le_of_not_gt not_positive
  have scaledDerivative (t : ℝ) : HasDerivAt
      (fun x => Real.exp (rate * x) * d x)
      (-(decay * forcing t) * Real.exp (rate * t)) t := by
    have exponential := (((hasDerivAt_id t).const_mul rate).exp)
    exact (exponential.mul (hd t)).congr_deriv (by dsimp; ring)
  have scaledDecreasing : AntitoneOn (fun t => Real.exp (rate * t) * d t)
      (Ici contact) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici contact)
      (fun t _ => (scaledDerivative t).continuousAt.continuousWithinAt)
      (fun t _ => (scaledDerivative t).hasDerivWithinAt)
    intro t _
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hdecay (hforcing t)))
      (Real.exp_pos _).le
  have nonpositive {t : ℝ} (afterContact : contact ≤ t) : d t ≤ 0 := by
    have bound := (scaledDecreasing (mem_Ici.mpr le_rfl) (mem_Ici.mpr afterContact)
      afterContact).trans
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le initial)
    by_contra positive
    exact (not_lt_of_ge bound) (mul_pos (Real.exp_pos _) (lt_of_not_ge positive))
  have decreasing : AntitoneOn f (Icc contact deadline) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc contact deadline)
      (fun t _ => (hf t).continuousAt.continuousWithinAt)
      (fun t _ => (hf t).hasDerivWithinAt)
    intro t ht
    exact nonpositive (interior_subset ht : t ∈ Icc contact deadline).1
  exact (not_lt_of_ge (decreasing ⟨le_rfl, later.le⟩ ⟨later.le, le_rfl⟩ later.le)) above

/-- A main pulse response has positive slope at every point preceding a
strictly higher later value. Its exponentially decaying input is nonnegative. -/
theorem readyPulse_transversal_of_later_value {initial amplitude start contact deadline : ℝ}
    (ha : 0 ≤ amplitude) (later : contact < deadline)
    (above : readyPulse initial amplitude start contact <
      readyPulse initial amplitude start deadline) :
    0 < deriv (readyPulse initial amplitude start) contact := by
  let forcing := fun t => amplitude * a * Real.exp (-a * (t - start))
  let slope := fun t => (1 / 2 : ℝ) * (1 / 10 - readyPulse initial amplitude start t) +
    forcing t
  have hd (t : ℝ) : HasDerivAt slope (-(1 / 2) * slope t - a * forcing t) t := by
    have relaxation := ((readyPulse_derivative initial amplitude start t).const_sub
      (1 / 10)).const_mul (1 / 2)
    have input := ((((hasDerivAt_id t).sub_const start).const_mul (-a)).exp).const_mul
      (amplitude * a)
    exact (relaxation.add input).congr_deriv (by dsimp [slope, forcing]; ring)
  have positive := derivative_pos_of_later_value
    (fun t => readyPulse_derivative initial amplitude start t) hd
    (by linarith [a_coarse_bounds.1])
    (fun t => mul_nonneg (mul_nonneg ha (by linarith [a_coarse_bounds.1]))
      (Real.exp_pos _).le) later above
  simpa only [(readyPulse_derivative initial amplitude start contact).deriv] using positive

/-- The sensor response is a constant translate of a main pulse response,
so the same strict-slope argument applies. -/
theorem auxPulse_transversal_of_later_value {initial amplitude start contact deadline : ℝ}
    (ha : 0 ≤ amplitude) (later : contact < deadline)
    (above : auxPulse initial amplitude start contact <
      auxPulse initial amplitude start deadline) :
    0 < deriv (auxPulse initial amplitude start) contact := by
  have higher : readyPulse (initial + 1 / 10 - 1 / 40) amplitude start contact <
      readyPulse (initial + 1 / 10 - 1 / 40) amplitude start deadline := by
    simpa only [auxPulse, sub_lt_sub_iff_right, add_lt_add_iff_right] using above
  have positive := readyPulse_transversal_of_later_value ha later higher
  rw [(readyPulse_derivative (initial + 1 / 10 - 1 / 40) amplitude start contact).deriv]
    at positive
  rw [(auxPulse_derivative initial amplitude start contact).deriv]
  convert positive using 1
  dsimp [auxPulse]
  ring

#print axioms readyPulse_transversal_of_later_value
#print axioms auxPulse_transversal_of_later_value

end KernelR.Hybrid
