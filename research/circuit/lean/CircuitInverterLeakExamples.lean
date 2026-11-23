import CircuitInverterLeak
import CircuitInverterExamples

/-! A witness for `inhibited_silence_leaks`: the actual leak `a = 1/10` and the
reference leak `a' = 11/100` differ, `α = 1/100`, every other budget is `1/100`,
and `L = 50` bounds `t * (|r₀| + ∫₀ᵗ |H₀|)` on the slot. All hypotheses are
discharged together, so the theorem is not vacuous. Numbers in the scalar model
only, not circuit values. -/

namespace KernelR.Circuit
open MeasureTheory Set

private theorem exp_neg_three_fifths_ge : (2 / 5 : ℝ) ≤ Real.exp (-(11 / 100 + 1 / 100) * 5) := by
  have := Real.add_one_le_exp (-(11 / 100 + 1 / 100) * 5 : ℝ)
  linarith

private theorem exp_neg_eleven_twentieths_ge : (9 / 20 : ℝ) ≤ Real.exp (-(11 / 100) * 5) := by
  have := Real.add_one_le_exp (-(11 / 100) * 5 : ℝ)
  linarith

theorem inhibited_silence_leaks_witness :
    ∀ t ∈ Icc (0 : ℝ) 5,
      leakyResponse (1 / 10) 0 (fun u => (fun _ => (2 : ℝ)) u - (fun _ => (20 : ℝ)) u +
        (fun _ => (0 : ℝ)) u) t < 3 := by
  have leak' : (0 : ℝ) ≤ 11 / 100 := by norm_num
  have upper (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 5) :
      leakyResponse (11 / 100) 0 (fun _ => (2 : ℝ)) t ≤ 2 * t :=
    (leakyResponse_const_bounds leak' (by norm_num) ht).2
  apply inhibited_silence_leaks (reference := leakyResponse (11 / 100) 0 (fun _ => (2 : ℝ)))
    (help := fun _ => 2) (nominalHelp := fun _ => 2) (inhibitory := fun _ => 20)
    (wrongSign := fun _ => 0) (initial := 0) (referenceInitial := 0) (τ := 1)
    (level := 3) (ε₀ := 1 / 100) (ηH := 1 / 100) (ηm := 1 / 100) (δ := 1 / 100) (Q := 20)
    (α := 1 / 100) (L := 50) (a' := 11 / 100)
    (by norm_num) leak' (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    intervalIntegrable_const intervalIntegrable_const
    intervalIntegrable_const intervalIntegrable_const
    (fun _ _ => rfl) (fun _ _ => rfl)
  · intro t ht
    simp only [abs_zero, zero_add, abs_two]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    nlinarith [ht.1, ht.2]
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
  · norm_num
  · intro t ht
    have := upper t ⟨ht.1, ht.2.trans (by norm_num)⟩
    linarith [ht.2]
  · intro t ht
    have := upper t ⟨by linarith [ht.1], ht.2⟩
    have w := exp_neg_three_fifths_ge
    nlinarith [ht.2]

/-- With the reference leak, the help alone still reaches the threshold plus every
budget and `α * L` by the end of the slot, so the silence is due to the inhibition. -/
theorem help_alone_exceeds_level_leaks :
    3 + (1 / 100 + (1 / 100 + 1 / 100)) + 1 / 100 + 1 / 100 * 50 <
      leakyResponse (11 / 100) 0 (fun _ => (2 : ℝ)) 5 := by
  have lower := (leakyResponse_const_bounds (a := 11 / 100) (c := 2) (D := 5) (t := 5)
    (by norm_num) (by norm_num) ⟨by norm_num, le_rfl⟩).1
  have w := exp_neg_eleven_twentieths_ge
  nlinarith

end KernelR.Circuit
