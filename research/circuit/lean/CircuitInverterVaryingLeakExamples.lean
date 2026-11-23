import CircuitInverterVaryingLeak
import CircuitInverterExamples

/-! A witness for `inhibited_silence_varying`. The actual leak is `1/10`, the
reference leak `a' = 11/100`, `α = 1/100`; help `1/2`, inhibitory current `3`, no
wrong-sign current, from rest, on the slot `[0, 5]`. The actual trajectory is the
explicit `x t = -25 * (1 - exp (-t/10))`. Its integral form relative to `a'` is
derived from its differential law by `varying_leak_integral_form`, and every
hypothesis of the theorem is discharged, with the state bound `X = 13`.
It shows that the hypotheses are consistent; it is a choice of numbers, not a circuit. -/

namespace KernelR.Circuit
open MeasureTheory Set

/-- The explicit actual trajectory. -/
noncomputable def varyingTrajectory (t : ℝ) : ℝ := -25 * (1 - Real.exp (-(1 / 10) * t))

private theorem trajectory_continuous : Continuous varyingTrajectory := by
  unfold varyingTrajectory; fun_prop

private theorem trajectory_derivative (u : ℝ) :
    HasDerivAt varyingTrajectory (-(fun _ => (1 / 10 : ℝ)) u * varyingTrajectory u + (1 / 2 - 3)) u := by
  have e : HasDerivAt (fun t => Real.exp (-(1 / 10) * t)) (Real.exp (-(1 / 10) * u) * (-(1 / 10))) u := by
    simpa using ((hasDerivAt_id u).const_mul (-(1 / 10 : ℝ))).exp
  have h := (e.const_sub 1).const_mul (-25 : ℝ)
  convert h using 1
  · funext t; simp only [varyingTrajectory]
  · simp only [varyingTrajectory]; ring

private theorem trajectory_bounds (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 5) : |varyingTrajectory u| ≤ 13 := by
  have upper : Real.exp (-(1 / 10) * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hu.1])
  have lower : Real.exp (-(1 / 10) * 5) ≤ Real.exp (-(1 / 10) * u) :=
    Real.exp_le_exp.mpr (by nlinarith [hu.2])
  have half := Real.add_one_le_exp (-(1 / 10) * 5 : ℝ)
  rw [abs_le]
  constructor <;> simp only [varyingTrajectory] <;> nlinarith

private theorem trajectory_law (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 5) :
    varyingTrajectory t = leakyResponse (11 / 100) 0
      (fun u => ((fun _ => (1 / 2 : ℝ)) u - ((fun _ => (1 / 10 : ℝ)) u - 11 / 100) * varyingTrajectory u) -
        (fun _ => (3 : ℝ)) u + (fun _ => (0 : ℝ)) u) t := by
  have start : varyingTrajectory 0 = 0 := by simp [varyingTrajectory]
  have form := varying_leak_integral_form (a' := 11 / 100) (leak := fun _ => 1 / 10)
    (current := fun _ => 1 / 2 - 3) ht.1 trajectory_continuous.continuousOn
    (fun u _ => trajectory_derivative u)
    (Continuous.intervalIntegrable (by unfold varyingTrajectory; fun_prop) _ _)
  rw [form, start]
  congr 1
  funext u
  ring

private theorem exp_neg_eleven_twentieths_ge' : (9 / 20 : ℝ) ≤ Real.exp (-(11 / 100) * 5) := by
  have := Real.add_one_le_exp (-(11 / 100) * 5 : ℝ)
  linarith

theorem inhibited_silence_varying_witness :
    ∀ t ∈ Icc (0 : ℝ) 5, varyingTrajectory t < 3 := by
  have leak' : (0 : ℝ) ≤ 11 / 100 := by norm_num
  have upper (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 5) :
      leakyResponse (11 / 100) 0 (fun _ => (1 / 2 : ℝ)) t ≤ 1 / 2 * t :=
    (leakyResponse_const_bounds leak' (by norm_num) ht).2
  apply inhibited_silence_varying (reference := leakyResponse (11 / 100) 0 (fun _ => (1 / 2 : ℝ)))
    (leak := fun _ => 1 / 10) (help := fun _ => 1 / 2) (nominalHelp := fun _ => 1 / 2)
    (inhibitory := fun _ => 3) (wrongSign := fun _ => 0) (initial := 0) (referenceInitial := 0)
    (τ := 1) (level := 3) (ε₀ := 1 / 100) (ηH := 1 / 100) (ηm := 1 / 100) (δ := 1 / 100) (Q := 3)
    (α := 1 / 100) (X := 13) (a' := 11 / 100)
    leak' (by norm_num) intervalIntegrable_const intervalIntegrable_const intervalIntegrable_const
    intervalIntegrable_const
    (Continuous.intervalIntegrable (by unfold varyingTrajectory; fun_prop) _ _)
    (fun _ _ => by rw [abs_le]; constructor <;> norm_num) trajectory_bounds trajectory_law
    (fun _ _ => rfl)
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
    have w := exp_neg_eleven_twentieths_ge'
    nlinarith [ht.2]

end KernelR.Circuit
