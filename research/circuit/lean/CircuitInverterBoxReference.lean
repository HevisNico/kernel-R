import CircuitInverter

/-! The box reference in closed form. The nominal help is a constant `c` on the
window `(h, h + ℓ]` and zero elsewhere; from rest, with a positive leak `a`, the
reference response is
`0` before `h`, `(c/a) (1 - e^{-a (t-h)})` in the window, and
`(c/a) (e^{-a (t-h-ℓ)} - e^{-a (t-h)})` after it.
Its largest value is `(c/a) (1 - e^{-a ℓ})`, reached at the end of the window. -/

namespace KernelR.Circuit
open MeasureTheory Set

/-- The nominal help: `c` on `(h, h + ℓ]`, zero elsewhere. -/
noncomputable def boxHelp (c h ℓ : ℝ) : ℝ → ℝ := fun u => if h < u ∧ u ≤ h + ℓ then c else 0

/-- The closed form of the box reference. -/
noncomputable def boxClosed (a c h ℓ t : ℝ) : ℝ :=
  if t ≤ h then 0
  else if t ≤ h + ℓ then c / a * (1 - Real.exp (-a * (t - h)))
  else c / a * (Real.exp (-a * (t - (h + ℓ))) - Real.exp (-a * (t - h)))

private theorem box_integrable (a c h ℓ t x y : ℝ) :
    IntervalIntegrable (fun u => Real.exp (-a * (t - u)) * boxHelp c h ℓ u) volume x y := by
  have bounded : IntervalIntegrable (boxHelp c h ℓ) volume x y := by
    have eq : boxHelp c h ℓ = (Ioc h (h + ℓ)).indicator (fun _ => c) := by
      funext u
      simp only [boxHelp, indicator, mem_Ioc]
    rw [eq]
    refine (intervalIntegrable_const (c := c)).mono_fun
      ((measurable_const.indicator measurableSet_Ioc).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (fun u => by simp only [indicator]; split_ifs <;> simp)
  exact bounded.continuousOn_mul (by fun_prop)

/-- The weighted constant current integrates to the difference of decay factors. -/
private theorem weighted_const_integral (a c t x y : ℝ) (leak : 0 < a) :
    (∫ u in x..y, Real.exp (-a * (t - u)) * c) =
      c / a * (Real.exp (-a * (t - y)) - Real.exp (-a * (t - x))) := by
  have deriv : ∀ u ∈ uIcc x y,
      HasDerivAt (fun u => c / a * Real.exp (-a * (t - u))) (Real.exp (-a * (t - u)) * c) u := by
    intro u _
    have e : HasDerivAt (fun u => Real.exp (-a * (t - u))) (Real.exp (-a * (t - u)) * a) u := by
      have inner : HasDerivAt (fun u => -a * (t - u)) a u := by
        simpa using ((hasDerivAt_id u).const_sub t).const_mul (-a)
      exact inner.exp
    convert e.const_mul (c / a) using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt deriv
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

private theorem zero_piece (a c h ℓ t x y : ℝ) (inside : ∀ u ∈ Ioc x y, ¬ (h < u ∧ u ≤ h + ℓ))
    (order : x ≤ y) :
    (∫ u in x..y, Real.exp (-a * (t - u)) * boxHelp c h ℓ u) = 0 := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))]
  · simp
  · refine Filter.Eventually.of_forall (fun u hu => ?_)
    rw [uIoc_of_le order] at hu
    simp [boxHelp, inside u hu]

private theorem const_piece (a c h ℓ t x y : ℝ) (inside : ∀ u ∈ Ioc x y, h < u ∧ u ≤ h + ℓ)
    (order : x ≤ y) (leak : 0 < a) :
    (∫ u in x..y, Real.exp (-a * (t - u)) * boxHelp c h ℓ u) =
      c / a * (Real.exp (-a * (t - y)) - Real.exp (-a * (t - x))) := by
  rw [intervalIntegral.integral_congr_ae (g := fun u => Real.exp (-a * (t - u)) * c)]
  · exact weighted_const_integral a c t x y leak
  · refine Filter.Eventually.of_forall (fun u hu => ?_)
    rw [uIoc_of_le order] at hu
    simp [boxHelp, inside u hu]

/-- The reference with the box help, from rest, has the closed form `boxClosed`. -/
theorem box_reference_eq {a c h ℓ t : ℝ} (leak : 0 < a) (start : 0 ≤ h) (width : 0 ≤ ℓ)
    (time : 0 ≤ t) :
    leakyResponse a 0 (boxHelp c h ℓ) t = boxClosed a c h ℓ t := by
  simp only [leakyResponse, mul_zero, zero_add, boxClosed]
  have I := box_integrable a c h ℓ t
  by_cases early : t ≤ h
  · simp only [early, ↓reduceIte]
    exact zero_piece a c h ℓ t 0 t (fun u hu => by intro h'; linarith [h'.1, hu.2]) time
  · simp only [early, ↓reduceIte]
    replace early := not_le.mp early
    rw [← intervalIntegral.integral_add_adjacent_intervals (I 0 h) (I h t),
      zero_piece a c h ℓ t 0 h (fun u hu => by intro h'; linarith [h'.1, hu.2]) start, zero_add]
    by_cases inWindow : t ≤ h + ℓ
    · simp only [inWindow, ↓reduceIte]
      rw [const_piece a c h ℓ t h t (fun u hu => ⟨hu.1, hu.2.trans inWindow⟩)
        early.le leak]
      simp
    · simp only [inWindow, ↓reduceIte]
      replace inWindow := not_le.mp inWindow
      rw [← intervalIntegral.integral_add_adjacent_intervals (I h (h + ℓ)) (I (h + ℓ) t),
        const_piece a c h ℓ t h (h + ℓ) (fun u hu => ⟨hu.1, hu.2⟩) (by linarith) leak,
        zero_piece a c h ℓ t (h + ℓ) t (fun u hu => by intro h'; linarith [h'.2, hu.1]) inWindow.le]
      ring

/-- The box reference never exceeds its value at the end of the window. -/
theorem box_closed_le_peak {a c h ℓ t : ℝ} (leak : 0 < a) (help : 0 ≤ c) (width : 0 ≤ ℓ) :
    boxClosed a c h ℓ t ≤ c / a * (1 - Real.exp (-a * ℓ)) := by
  have ca : 0 ≤ c / a := div_nonneg help leak.le
  have peak0 : 0 ≤ 1 - Real.exp (-a * ℓ) := by
    have := Real.exp_le_one_iff.mpr (show -a * ℓ ≤ 0 by nlinarith)
    linarith
  unfold boxClosed
  split_ifs with h1 h2
  · exact mul_nonneg ca peak0
  · apply mul_le_mul_of_nonneg_left _ ca
    have := Real.exp_le_exp.mpr (show -a * ℓ ≤ -a * (t - h) by nlinarith)
    linarith
  · apply mul_le_mul_of_nonneg_left _ ca
    replace h1 := not_le.mp h1
    replace h2 := not_le.mp h2
    have split : Real.exp (-a * (t - h)) =
        Real.exp (-a * (t - (h + ℓ))) * Real.exp (-a * ℓ) := by
      rw [← Real.exp_add]; congr 1; ring
    have le1 : Real.exp (-a * (t - (h + ℓ))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [split]
    nlinarith [Real.exp_pos (-a * (t - (h + ℓ))), Real.exp_pos (-a * ℓ)]

/-- Before the window the box reference is zero. -/
theorem box_closed_before {a c h ℓ t : ℝ} (early : t ≤ h) : boxClosed a c h ℓ t = 0 := by
  simp [boxClosed, early]

/-- The box help, as a current: its L1 norm on any prefix is at most `c * ℓ`,
which bounds `t * ∫₀ᵗ |H₀|` by `D * c * ℓ` (the `L` of the two-leak theorems). -/
theorem box_help_abs_integral_le {c h ℓ t : ℝ} (help : 0 ≤ c) (width : 0 ≤ ℓ) (start : 0 ≤ h)
    (time : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, |boxHelp c h ℓ u|) ≤ c * ℓ := by
  have eqAbs : (fun u => |boxHelp c h ℓ u|) = boxHelp c h ℓ := by
    funext u; unfold boxHelp; split_ifs <;> simp [abs_of_nonneg help]
  have weight := box_reference_eq (a := 1) (c := c) (h := h) (ℓ := ℓ) (t := t) one_pos start width time
  rw [eqAbs]
  have indicatorForm : boxHelp c h ℓ = (Ioc h (h + ℓ)).indicator (fun _ => c) := by
    funext u; simp only [boxHelp, indicator, mem_Ioc]
  rw [indicatorForm, intervalIntegral.integral_of_le time, integral_indicator measurableSet_Ioc]
  rw [Measure.restrict_restrict measurableSet_Ioc, setIntegral_const, smul_eq_mul]
  have measure : (volume (Ioc h (h + ℓ) ∩ Ioc 0 t)).toReal ≤ ℓ := by
    calc (volume (Ioc h (h + ℓ) ∩ Ioc 0 t)).toReal ≤ (volume (Ioc h (h + ℓ))).toReal := by
          apply ENNReal.toReal_mono (by simp)
          exact measure_mono inter_subset_left
      _ = ℓ := by simp [Real.volume_Ioc, width]
  have hreal : volume.real (Ioc h (h + ℓ) ∩ Ioc 0 t) = (volume (Ioc h (h + ℓ) ∩ Ioc 0 t)).toReal := rfl
  rw [hreal]
  nlinarith

end KernelR.Circuit
