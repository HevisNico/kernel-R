import KernelR.HybridReady
import KernelR.HybridWork

/-! READY comparison for actual variable-gain, multi-port flows. Canonical raw
tails are retained at their original dates, including at the right endpoint. -/
namespace KernelR.Hybrid
open MeasureTheory Set

/-- Scalar comparison using right derivatives, so endpoints and flow cuts need
not have two-sided derivatives. -/
theorem linear_comparison_of_right_derivatives {y z lower upper : ℝ → ℝ}
    {s u rate : ℝ} (hyc : ContinuousOn y (Icc s u)) (hzc : ContinuousOn z (Icc s u))
    (hy : ∀ x ∈ Ico s u, HasDerivWithinAt y (-rate * y x + lower x) (Ici x) x)
    (hz : ∀ x ∈ Ico s u, HasDerivWithinAt z (-rate * z x + upper x) (Ici x) x)
    (hinit : y s ≤ z s) (hforcing : ∀ x ∈ Ico s u, lower x ≤ upper x) :
    ∀ t ∈ Icc s u, y t ≤ z t := by
  let F : ℝ → ℝ := fun t => (y t - z t) * Real.exp (rate * (t - s))
  let F' : ℝ → ℝ := fun t => (lower t - upper t) * Real.exp (rate * (t - s))
  have hc : ContinuousOn F (Icc s u) := (hyc.sub hzc).mul (by fun_prop)
  have hd : ∀ x ∈ Ico s u, HasDerivWithinAt F (F' x) (Ici x) x := by
    intro x hx
    have he := ((((hasDerivAt_id x).sub_const s).const_mul rate).exp).hasDerivWithinAt (s := Ici x)
    exact (((hy x hx).sub (hz x hx)).mul he).congr_deriv (by dsimp [F']; ring)
  have hF : ∀ t ∈ Icc s u, F t ≤ 0 := by
    apply image_le_of_deriv_right_le_deriv_boundary hc hd
    · simpa [F] using sub_nonpos.mpr hinit
    · exact continuousOn_const
    · intro x _; exact hasDerivWithinAt_const x _ 0
    · intro x hx
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hforcing x hx)) (Real.exp_pos _).le
  intro t ht
  have h := (mul_le_mul_iff_left₀ (Real.exp_pos (rate * (t - s)))).mp
    (show (y t - z t) * Real.exp (rate * (t - s)) ≤ 0 * Real.exp (rate * (t - s)) by simpa using hF t ht)
  exact sub_nonpos.mp h

/-- The smooth left extension is used only on a flow whose raw-support
conditions certify the actual current throughout its half-open interval. -/
noncomputable def rawTail {n} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) : ℝ :=
  match s.raw i p with
  | none => 0
  | some origin => a * Real.exp (-a * (t - origin))

theorem rawTail_nonnegative {n} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    0 ≤ rawTail s i p t := by
  unfold rawTail
  split
  · exact le_rfl
  · exact mul_nonneg (by linarith [a_coarse_bounds.1]) (Real.exp_pos _).le

theorem rawTail_continuous {n} (s : Snapshot n) (i : Fin n) (p : Port) :
    Continuous (rawTail s i p) := by
  unfold rawTail
  split <;> fun_prop

theorem Flow.current_eq_rawTail {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (t : ℝ) (ht : t ∈ Ico s.time u.time) : current s i p t = rawTail s i p t := by
  cases hr : s.raw i p with
  | none => simp [current, rawTail, hr]
  | some origin =>
    have h := f.raw_support i p origin hr
    simp [current, rawTail, hr, pulse, h.1.trans ht.1, ht.2.trans_le h.2]

noncomputable def tailDrive {n} (s : Snapshot n) (x : Values n) (i : Fin n) (t : ℝ) : ℝ :=
  ∑ p : Port, Real.exp (x i (.z p)) * rawTail s i p t

theorem Flow.drive_eq_tailDrive {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (t : ℝ) (ht : t ∈ Ico s.time u.time) :
    drive s (f.path t) i t = tailDrive s (f.path t) i t := by
  unfold drive tailDrive
  apply Finset.sum_congr rfl
  intro p _
  rw [f.current_eq_rawTail i p t ht]

theorem Flow.tailDrive_continuous {n θ s u} (f : @Flow n θ s u) (i : Fin n) :
    ContinuousOn (fun t => tailDrive s (f.path t) i t) (Icc s.time u.time) := by
  apply continuousOn_finsetSum
  intro p _
  exact (Real.continuous_exp.comp_continuousOn (f.continuous i (.z p))).mul
    (rawTail_continuous s i p).continuousOn

theorem Flow.ready_right_derivative {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hm : s.main i = .ready) (t : ℝ) (ht : t ∈ Ico s.time u.time) :
    HasDerivWithinAt (fun v => f.path v i .q)
      ((1 / 2) * (1 / 10 - f.path t i .q) + tailDrive s (f.path t) i t) (Ici t) t := by
  let g := fun v => (1 / 2 : ℝ) * (1 / 10 - f.path v i .q) + tailDrive s (f.path v) i v
  have hc : ContinuousOn g (Icc s.time u.time) :=
    ((continuousOn_const.sub (f.continuous i .q)).const_mul (1 / 2)).add (f.tailDrive_continuous i)
  apply right_derivative_of_integral hc _ ht
  intro v hv
  have he := f.integral_eq v hv i .q
  have hchange : (∫ w in s.time..v, field θ s (f.path w) w i .q) = ∫ w in s.time..v, g w := by
    apply intervalIntegral.integral_congr_Ioo_of_le hv.1
    intro w hw
    simp only [field, hm, g, f.drive_eq_tailDrive i w ⟨hw.1.le, hw.2.trans_le hv.2⟩]
  rw [hchange] at he
  simpa only [f.initial] using he

/-- Sum of all active tails, attenuated from their real origins to this flow's
start. The gains supplied here are comparison values, not frozen physical gains. -/
noncomputable def rawAmplitude {n} (s : Snapshot n) (i : Fin n) (gain : Port → ℝ) : ℝ :=
  ∑ p : Port, match s.raw i p with
    | none => 0
    | some origin => gain p * Real.exp (-a * (s.time - origin))

theorem rawAmplitude_drive {n} (s : Snapshot n) (i : Fin n) (gain : Port → ℝ) (t : ℝ) :
    rawAmplitude s i gain * a * Real.exp (-a * (t - s.time)) =
      ∑ p : Port, gain p * rawTail s i p t := by
  unfold rawAmplitude
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  cases hr : s.raw i p with
  | none => simp [rawTail, hr]
  | some origin =>
    simp only [rawTail, hr]
    have he : Real.exp (-a * (s.time - origin)) * Real.exp (-a * (t - s.time)) =
        Real.exp (-a * (t - origin)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = gain p * a * (Real.exp (-a * (s.time - origin)) * Real.exp (-a * (t - s.time))) := by ring
      _ = _ := by rw [he]; ring

/-- No absence-of-ERROR premise: the gains may vary throughout the raw pulse,
and all three ports may be active. Only actual path bounds are used. -/
theorem Flow.ready_gain_envelope {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (hm : s.main i = .ready) (lower upper : Port → ℝ)
    (hgain : ∀ t ∈ Icc s.time u.time, ∀ p,
      lower p ≤ Real.exp (f.path t i (.z p)) ∧ Real.exp (f.path t i (.z p)) ≤ upper p) :
    ∀ t ∈ Icc s.time u.time,
      readyPulse (s.x i .q) (rawAmplitude s i lower) s.time t ≤ f.path t i .q ∧
      f.path t i .q ≤ readyPulse (s.x i .q) (rawAmplitude s i upper) s.time t := by
  have hmodel (gain : Port → ℝ) (x : ℝ) :
      HasDerivWithinAt (readyPulse (s.x i .q) (rawAmplitude s i gain) s.time)
        (-(1 / 2) * readyPulse (s.x i .q) (rawAmplitude s i gain) s.time x +
          ((1 / 2) * (1 / 10) + ∑ p : Port, gain p * rawTail s i p x)) (Ici x) x := by
    exact (readyPulse_derivative (s.x i .q) (rawAmplitude s i gain) s.time x).hasDerivWithinAt.congr_deriv
      (by rw [← rawAmplitude_drive]; ring)
  have hactual (x : ℝ) (hx : x ∈ Ico s.time u.time) :
      HasDerivWithinAt (fun v => f.path v i .q)
        (-(1 / 2) * f.path x i .q + ((1 / 2) * (1 / 10) + tailDrive s (f.path x) i x)) (Ici x) x :=
    (f.ready_right_derivative i hm x hx).congr_deriv (by ring)
  have hcont (gain : Port → ℝ) :
      ContinuousOn (readyPulse (s.x i .q) (rawAmplitude s i gain) s.time) (Icc s.time u.time) :=
    fun t _ => (readyPulse_derivative _ _ _ t).continuousAt.continuousWithinAt
  have hlo := linear_comparison_of_right_derivatives (hcont lower) (f.continuous i .q)
    (fun x _ => hmodel lower x) hactual (by simp [readyPulse_initial, f.initial]) (by
      intro x hx
      apply add_le_add_right
      unfold tailDrive
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right (hgain x ⟨hx.1, hx.2.le⟩ p).1 (rawTail_nonnegative s i p x))
  have hup := linear_comparison_of_right_derivatives (f.continuous i .q) (hcont upper)
    hactual (fun x _ => hmodel upper x) (by simp [readyPulse_initial, f.initial]) (by
      intro x hx
      apply add_le_add_right
      unfold tailDrive
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right (hgain x ⟨hx.1, hx.2.le⟩ p).2 (rawTail_nonnegative s i p x))
  exact fun t ht => ⟨hlo t ht, hup t ht⟩

/-- Reachable cap bounds and actual gain monotonicity supply the comparison
gains; variable-gain overlap is retained rather than assumed absent. -/
theorem Flow.ready_physical_envelope {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (hm : s.main i = .ready)
    (hcap : ∀ p, s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    ∀ t ∈ Icc s.time u.time,
      readyPulse (s.x i .q) (rawAmplitude s i (fun p => Real.exp (s.x i (.z p)))) s.time t ≤
        f.path t i .q ∧
      f.path t i .q ≤ readyPulse (s.x i .q) (rawAmplitude s i (θ i).cap) s.time t := by
  apply f.ready_gain_envelope i hm
  intro t ht p
  refine ⟨Real.exp_le_exp.mpr (f.gain_nondecreasing hb i p t ht), ?_⟩
  calc
    _ ≤ Real.exp (Real.log ((θ i).cap p)) := Real.exp_le_exp.mpr (f.gain_cap_on i p (hcap p) t ht)
    _ = _ := Real.exp_log (hb.cap_positive i p)

end KernelR.Hybrid
