import CircuitInverter

/-! A witness that the hypotheses of `inhibited_silence` hold together, with a
positive leak and nonzero budgets. It shows that the theorem is not vacuous. It
is a choice of numbers in the scalar model, not a circuit and not a simulation. -/

namespace KernelR.Circuit
open MeasureTheory Set

/-- For a constant nonnegative current started from rest, the response lies
between `exp (-a * D) * c * t` and `c * t` on `[0, D]`. -/
theorem leakyResponse_const_bounds {a c D t : ℝ} (leak : 0 ≤ a) (current : 0 ≤ c)
    (ht : t ∈ Icc 0 D) :
    Real.exp (-a * D) * (c * t) ≤ leakyResponse a 0 (fun _ => c) t ∧
      leakyResponse a 0 (fun _ => c) t ≤ c * t := by
  have weight : ContinuousOn (fun u => Real.exp (-a * (t - u))) (uIcc 0 t) := by fun_prop
  have hc : IntervalIntegrable (fun _ : ℝ => c) volume 0 t := intervalIntegrable_const
  have hw := hc.continuousOn_mul weight
  have constant : (∫ _ in (0 : ℝ)..t, c) = c * t := by simp [mul_comm]
  have scaled : (∫ _ in (0 : ℝ)..t, Real.exp (-a * D) * c) = Real.exp (-a * D) * (c * t) := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  simp only [leakyResponse, mul_zero, zero_add]
  constructor
  · rw [← scaled]
    apply intervalIntegral.integral_mono_on ht.1 intervalIntegrable_const hw
    intro u hu
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith [hu.1, hu.2, ht.2])) current
  · rw [← constant]
    apply intervalIntegral.integral_mono_on ht.1 hw intervalIntegrable_const
    intro u hu
    have w : Real.exp (-a * (t - u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hu.2])
    simpa using mul_le_mul_of_nonneg_right w current

/-- `exp (-1/2) ≥ 1/2`, from `1 + x ≤ exp x`. -/
private theorem exp_neg_half_ge : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 10) * 5) := by
  have := Real.add_one_le_exp (-(1 / 10) * 5 : ℝ)
  linarith

/-- The witness: leak `a = 1/10`, slot `D = 5`, help `2` (nominal and actual),
inhibitory current `20` throughout, no wrong-sign current, threshold `3`,
inhibitory window `τ = 1`, `Q = 20`, and every budget `1/100`. All hypotheses
of `inhibited_silence` are discharged, so the state stays below threshold. -/
theorem inhibited_silence_witness :
    ∀ t ∈ Icc (0 : ℝ) 5,
      leakyResponse (1 / 10) 0 (fun u => (fun _ => (2 : ℝ)) u - (fun _ => (20 : ℝ)) u +
        (fun _ => (0 : ℝ)) u) t < 3 := by
  have leak : (0 : ℝ) ≤ 1 / 10 := by norm_num
  have upper (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 5) :
      leakyResponse (1 / 10) 0 (fun _ => (2 : ℝ)) t ≤ 2 * t :=
    (leakyResponse_const_bounds leak (by norm_num) ht).2
  apply inhibited_silence (reference := leakyResponse (1 / 10) 0 (fun _ => (2 : ℝ)))
    (help := fun _ => 2) (nominalHelp := fun _ => 2) (inhibitory := fun _ => 20)
    (wrongSign := fun _ => 0) (initial := 0) (referenceInitial := 0) (τ := 1)
    (level := 3) (ε₀ := 1 / 100) (ηH := 1 / 100) (ηm := 1 / 100) (δ := 1 / 100) (Q := 20)
    leak (by norm_num) intervalIntegrable_const intervalIntegrable_const
    intervalIntegrable_const intervalIntegrable_const
    (fun _ _ => rfl) (fun _ _ => rfl)
  · norm_num
  · intro t _
    simp
  · intro _ _
    norm_num
  · intro _ _
    norm_num
  · simp
  · simp
  · norm_num
  · intro t ht
    have := upper t ⟨ht.1, ht.2.trans (by norm_num)⟩
    linarith [ht.2]
  · intro t ht
    have := upper t ⟨by linarith [ht.1], ht.2⟩
    have half := exp_neg_half_ge
    nlinarith [ht.2]

/-- Without inhibition the same help reaches the threshold by the end of the slot:
at `t = 5` the reference is at least `5`, above `3` plus every budget. So the
silence in the witness is due to the inhibitory charge. -/
theorem help_alone_exceeds_level :
    3 + (1 / 100 + (1 / 100 + 1 / 100)) + 1 / 100 <
      leakyResponse (1 / 10) 0 (fun _ => (2 : ℝ)) 5 := by
  have lower := (leakyResponse_const_bounds (a := 1 / 10) (c := 2) (D := 5) (t := 5)
    (by norm_num) (by norm_num) ⟨by norm_num, le_rfl⟩).1
  have half := exp_neg_half_ge
  nlinarith

end KernelR.Circuit
