import KernelR.Robust.Latency

/-! The actual exponential impulse response and the analytic reduction behind
the finite increment checks. The numerical transcendental enclosure remains a
separate premise, just as in the inherited interval-certificate interface. -/
namespace KernelR.Robust

noncomputable def response (a κ t : ℝ) : ℝ :=
  a / (a-κ) * (Real.exp (-κ*t) - Real.exp (-a*t))

noncomputable def responseSlope (a κ t : ℝ) : ℝ :=
  a / (a-κ) * (a * Real.exp (-a*t) - κ * Real.exp (-κ*t))

noncomputable def responseCurvature (a κ t : ℝ) : ℝ :=
  a / (a-κ) * (κ^2 * Real.exp (-κ*t) - a^2 * Real.exp (-a*t))

theorem response_derivative (a κ t : ℝ) :
    HasDerivAt (response a κ) (responseSlope a κ t) t := by
  unfold response responseSlope
  have hk := ((hasDerivAt_id t).const_mul (-κ)).exp
  have ha := ((hasDerivAt_id t).const_mul (-a)).exp
  convert (hk.sub ha).const_mul (a/(a-κ)) using 1 <;> dsimp <;> ring

theorem response_second_derivative (a κ t : ℝ) :
    HasDerivAt (responseSlope a κ) (responseCurvature a κ t) t := by
  unfold responseSlope responseCurvature
  have hk := (((hasDerivAt_id t).const_mul (-κ)).exp).const_mul κ
  have ha := (((hasDerivAt_id t).const_mul (-a)).exp).const_mul a
  convert (ha.sub hk).const_mul (a/(a-κ)) using 1 <;> dsimp <;> ring

theorem response_nonneg {a κ t : ℝ} (hk : 0 < κ) (ha : κ < a) (ht : 0 ≤ t) :
    0 ≤ response a κ t := by
  unfold response
  apply mul_nonneg (le_of_lt (div_pos (lt_trans hk ha) (sub_pos.mpr ha)))
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A single exponential inequality certifies concavity throughout the raw window. -/
theorem response_concave {a κ : ℝ} (hk : 0 < κ) (ha : κ < a)
    (curvature : κ^2 * Real.exp (a-κ) ≤ a^2) :
    ConcaveOn ℝ (Set.Icc 0 1) (response a κ) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
    (f' := responseSlope a κ) (f'' := responseCurvature a κ)
  · exact (continuous_iff_continuousAt.mpr
      (fun t => (response_derivative a κ t).continuousAt)).continuousOn
  · intro t ht
    exact (response_derivative a κ t).hasDerivWithinAt
  · intro t ht
    exact (response_second_derivative a κ t).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := interior_subset ht
    have hexp : Real.exp ((a-κ)*t) ≤ Real.exp (a-κ) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ht'.2]
    have hprod := (mul_le_mul_of_nonneg_left hexp (sq_nonneg κ)).trans curvature
    have hmul := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-a*t)).le
    have heq : Real.exp ((a-κ)*t) * Real.exp (-a*t) = Real.exp (-κ*t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, heq] at hmul
    unfold responseCurvature
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (div_pos (lt_trans hk ha) (sub_pos.mpr ha))) (sub_nonpos.mpr hmul)

end KernelR.Robust
