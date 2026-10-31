import KernelR.HybridFlow
import KernelR.Recovery

/-! READY responses derived from integral executions and scalar ODE uniqueness.
The pulse lemma retains residual charge and an already-active raw tail. -/
namespace KernelR.Hybrid
open MeasureTheory Set Filter
open scoped Topology

theorem linear_unique_of_right_derivatives {y z forcing : ℝ → ℝ} {s u rate : ℝ}
    (hyc : ContinuousOn y (Icc s u)) (hzc : ContinuousOn z (Icc s u))
    (hy : ∀ x ∈ Ico s u, HasDerivWithinAt y (-rate * y x + forcing x) (Ici x) x)
    (hz : ∀ x ∈ Ico s u, HasDerivWithinAt z (-rate * z x + forcing x) (Ici x) x)
    (hinit : y s = z s) : ∀ t ∈ Icc s u, y t = z t := by
  let F : ℝ → ℝ := fun t => (y t - z t) * Real.exp (rate * (t - s))
  have hc : ContinuousOn F (Icc s u) := (hyc.sub hzc).mul (by fun_prop)
  have hd : ∀ x ∈ Ico s u, HasDerivWithinAt F 0 (Ici x) x := by
    intro x hx
    have he := ((((hasDerivAt_id x).sub_const s).const_mul rate).exp).hasDerivWithinAt (s := Ici x)
    exact (((hy x hx).sub (hz x hx)).mul he).congr_deriv (by dsimp; ring)
  intro t ht
  have h := constant_of_has_deriv_right_zero hc hd t ht
  have hp : (y t - z t) * Real.exp (rate * (t - s)) = 0 := by simpa [F, hinit] using h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (Real.exp_ne_zero _))

theorem response_derivative (t : ℝ) :
    HasDerivAt response (a * Real.exp (-a * t) - (1 / 2) * response t) t := by
  have hne : a - 1 / 2 ≠ 0 := by
    have h := KernelR.log_four_bounds.1
    dsimp [a]; linarith
  have hmul := div_mul_cancel₀ a hne
  have h := ((((hasDerivAt_id t).const_mul (-(1 / 2 : ℝ))).exp).sub
    (((hasDerivAt_id t).const_mul (-a)).exp)).const_mul (a / (a - 1 / 2))
  convert h using 1
  · rfl
  · dsimp [response]
    linear_combination -Real.exp (-a * t) * hmul

noncomputable def readyPulse (initial amplitude start t : ℝ) : ℝ :=
  1 / 10 + (initial - 1 / 10) * Real.exp (-(1 / 2) * (t - start)) +
    amplitude * response (t - start)

theorem readyPulse_initial (initial amplitude start : ℝ) :
    readyPulse initial amplitude start start = initial := by
  simp [readyPulse, response]

theorem readyPulse_derivative (initial amplitude start t : ℝ) :
    HasDerivAt (readyPulse initial amplitude start)
      ((1 / 2) * (1 / 10 - readyPulse initial amplitude start t) +
        amplitude * a * Real.exp (-a * (t - start))) t := by
  have h₁ := ((((hasDerivAt_id t).sub_const start).const_mul (-(1 / 2 : ℝ))).exp).const_mul
    (initial - 1 / 10)
  have h₂ := ((response_derivative (t - start)).comp t ((hasDerivAt_id t).sub_const start)).const_mul amplitude
  convert (h₁.const_add (1 / 10)).add h₂ using 1
  · rfl
  · dsimp [readyPulse]; ring

/-- One actual active input, frozen by absence of ERROR on that port. The
origin may precede this flow; no raw tail is discarded at a main reopening. -/
theorem Flow.ready_single_pulse_solution {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (p : Port) (origin : ℝ) (hm : s.main i = .ready)
    (hraw : s.raw i p = some origin) (hothers : ∀ j, j ≠ p → s.raw i j = none)
    (haux : s.aux i p ≠ .error) :
    ∀ t ∈ Icc s.time u.time, f.path t i .q =
      readyPulse (s.x i .q)
        (Real.exp (s.x i (.z p)) * Real.exp (-a * (s.time - origin))) s.time t := by
  let amplitude := Real.exp (s.x i (.z p)) * Real.exp (-a * (s.time - origin))
  let forcing : ℝ → ℝ := fun t => (1 / 2) * (1 / 10) +
    amplitude * a * Real.exp (-a * (t - s.time))
  let y : ℝ → ℝ := fun t => f.path t i .q
  let z : ℝ → ℝ := readyPulse (s.x i .q) amplitude s.time
  have hfield (v : ℝ) (hv : v ∈ Ico s.time u.time) :
      field θ s (f.path v) v i .q = -(1 / 2) * y v + forcing v := by
    have hz := f.gain_constant_without_error i p haux v ⟨hv.1, hv.2.le⟩
    have hr := f.raw_support i p origin hraw
    have hp : origin ≤ v ∧ v < origin + 1 := ⟨hr.1.trans hv.1, hv.2.trans_le hr.2⟩
    have hdrive : drive s (f.path v) i v = Real.exp (s.x i (.z p)) * a * Real.exp (-a * (v - origin)) := by
      unfold drive
      rw [Finset.sum_eq_single p]
      · simp [current, hraw, pulse, hp, hz, mul_assoc]
      · intro j _ hj; simp [current, hothers j hj]
      · simp
    have he : Real.exp (-a * (v - origin)) =
        Real.exp (-a * (s.time - origin)) * Real.exp (-a * (v - s.time)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [field, hm, hdrive, he]
    dsimp [y, forcing, amplitude]
    ring
  have hcont : ContinuousOn (fun v => -(1 / 2) * y v + forcing v) (Icc s.time u.time) :=
    ((f.continuous i .q).const_mul (-(1 / 2))).add (by dsimp [forcing]; fun_prop)
  have hi : ∀ t ∈ Icc s.time u.time,
      y t = y s.time + ∫ v in s.time..t, -(1 / 2) * y v + forcing v := by
    intro t ht
    have he := f.integral_eq t ht i .q
    have hchange : (∫ v in s.time..t, field θ s (f.path v) v i .q) =
        ∫ v in s.time..t, -(1 / 2) * y v + forcing v := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro v hv
      exact hfield v ⟨hv.1.le, hv.2.trans_le ht.2⟩
    rw [hchange] at he
    simpa only [y, f.initial] using he
  apply linear_unique_of_right_derivatives (y := y) (z := z) (forcing := forcing) (rate := 1 / 2)
    (f.continuous i .q)
    (fun t _ => (readyPulse_derivative (s.x i .q) amplitude s.time t).continuousAt.continuousWithinAt)
    (fun x hx => right_derivative_of_integral (y := y) hcont hi hx)
  · intro x hx
    exact (readyPulse_derivative (s.x i .q) amplitude s.time x).hasDerivWithinAt.congr_deriv
      (by dsimp [z, forcing]; ring)
  · simp [y, z, f.initial, readyPulse_initial]

noncomputable def auxPulse (initial amplitude start t : ℝ) : ℝ :=
  readyPulse (initial + 1 / 10 - 1 / 40) amplitude start t - 1 / 10 + 1 / 40

theorem auxPulse_initial (initial amplitude start : ℝ) :
    auxPulse initial amplitude start start = initial := by
  rw [auxPulse, readyPulse_initial]; ring

theorem auxPulse_derivative (initial amplitude start t : ℝ) :
    HasDerivAt (auxPulse initial amplitude start)
      ((1 / 2) * (1 / 40 - auxPulse initial amplitude start t) +
        amplitude * a * Real.exp (-a * (t - start))) t := by
  exact (((readyPulse_derivative (initial + 1 / 10 - 1 / 40) amplitude start t).sub_const
    (1 / 10)).add_const (1 / 40)).congr_deriv (by dsimp [auxPulse]; ring)

theorem Flow.aux_ready_single_pulse_solution {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (p : Port) (origin : ℝ) (hm : s.aux i p = .ready)
    (hraw : s.raw i p = some origin) :
    ∀ t ∈ Icc s.time u.time, f.path t i (.m p) =
      auxPulse (s.x i (.m p)) ((θ i).inputGain p * Real.exp (-a * (s.time - origin))) s.time t := by
  let amplitude := (θ i).inputGain p * Real.exp (-a * (s.time - origin))
  let forcing : ℝ → ℝ := fun t => (1 / 2) * (1 / 40) +
    amplitude * a * Real.exp (-a * (t - s.time))
  let y : ℝ → ℝ := fun t => f.path t i (.m p)
  let z : ℝ → ℝ := auxPulse (s.x i (.m p)) amplitude s.time
  have hfield (v : ℝ) (hv : v ∈ Ico s.time u.time) :
      field θ s (f.path v) v i (.m p) = -(1 / 2) * y v + forcing v := by
    have hr := f.raw_support i p origin hraw
    have hp : origin ≤ v ∧ v < origin + 1 := ⟨hr.1.trans hv.1, hv.2.trans_le hr.2⟩
    have he : Real.exp (-a * (v - origin)) =
        Real.exp (-a * (s.time - origin)) * Real.exp (-a * (v - s.time)) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [field, hm, ite_true, current, hraw, pulse, ite_eq_left hp]
    rw [he]
    dsimp [y, forcing, amplitude]
    ring
  have hcont : ContinuousOn (fun v => -(1 / 2) * y v + forcing v) (Icc s.time u.time) :=
    ((f.continuous i (.m p)).const_mul (-(1 / 2))).add (by dsimp [forcing]; fun_prop)
  have hi : ∀ t ∈ Icc s.time u.time,
      y t = y s.time + ∫ v in s.time..t, -(1 / 2) * y v + forcing v := by
    intro t ht
    have he := f.integral_eq t ht i (.m p)
    have hchange : (∫ v in s.time..t, field θ s (f.path v) v i (.m p)) =
        ∫ v in s.time..t, -(1 / 2) * y v + forcing v := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro v hv
      exact hfield v ⟨hv.1.le, hv.2.trans_le ht.2⟩
    rw [hchange] at he
    simpa only [y, f.initial] using he
  apply linear_unique_of_right_derivatives (y := y) (z := z) (forcing := forcing) (rate := 1 / 2)
    (f.continuous i (.m p))
    (fun t _ => (auxPulse_derivative (s.x i (.m p)) amplitude s.time t).continuousAt.continuousWithinAt)
    (fun x hx => right_derivative_of_integral (y := y) hcont hi hx)
  · intro x hx
    exact (auxPulse_derivative (s.x i (.m p)) amplitude s.time x).hasDerivWithinAt.congr_deriv
      (by dsimp [z, forcing]; ring)
  · simp [y, z, f.initial, auxPulse_initial]

/-- The analytic head response has the actual first threshold contact of this
READY flow. No recorded firing date or root enclosure is assumed. -/
theorem Flow.ready_first_contact {n θ route s u after} (f : @Flow n θ s u)
    (exit : Jump route u after) (i : Fin n) (p : Port) (origin : ℝ)
    (hm : s.main i = .ready) (ha : after.main i = .fast)
    (hraw : s.raw i p = some origin) (hothers : ∀ j, j ≠ p → s.raw i j = none)
    (haux : s.aux i p ≠ .error) :
    let model := readyPulse (s.x i .q)
      (Real.exp (s.x i (.z p)) * Real.exp (-a * (s.time - origin))) s.time
    model u.time = 1 ∧ ∀ t ∈ Ico s.time u.time, model t < 1 := by
  dsimp only
  have hq := exit.fast_entry_guard i (by rw [f.main_fixed, hm]; decide) ha
  rw [exit.physical_continuous] at hq
  have hsol := f.ready_single_pulse_solution i p origin hm hraw hothers haux
  constructor
  · rw [← hsol u.time ⟨f.positive.le, le_rfl⟩, f.final, hq]
  · intro t ht
    rw [← hsol t ⟨ht.1, ht.2.le⟩]
    have h := (f.guards t ht).1 i
    simpa only [hm] using h

theorem Flow.aux_ready_first_contact {n θ route s u after} (f : @Flow n θ s u)
    (exit : Jump route u after) (i : Fin n) (p : Port) (origin : ℝ)
    (hm : s.aux i p = .ready) (ha : after.aux i p = .mark)
    (hraw : s.raw i p = some origin) :
    let model := auxPulse (s.x i (.m p))
      ((θ i).inputGain p * Real.exp (-a * (s.time - origin))) s.time
    model u.time = 1 ∧ ∀ t ∈ Ico s.time u.time, model t < 1 := by
  dsimp only
  have hq := exit.mark_entry_guard i p (by rw [f.aux_fixed, hm]; decide) ha
  rw [exit.physical_continuous] at hq
  have hsol := f.aux_ready_single_pulse_solution i p origin hm hraw
  constructor
  · rw [← hsol u.time ⟨f.positive.le, le_rfl⟩, f.final, hq]
  · intro t ht
    rw [← hsol t ⟨ht.1, ht.2.le⟩]
    have h := (f.guards t ht).2 i p
    simpa only [hm] using h

end KernelR.Hybrid
