import KernelR.HybridWeakFlow
import KernelR.HybridEnvelope
import KernelR.HybridContactTransversality

/-! Weak upper READY guards permit tangencies, but cannot postpone a contact
whose actual pre-jump vector field is strictly positive. -/
namespace KernelR.Hybrid
open MeasureTheory Set Filter
open scoped Topology

/-- Raw support makes each current equal its smooth tail on a weak flow. -/
theorem WeakFlow.current_eq_rawTail {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (p : Port) (t : ℝ) (ht : t ∈ Ico s.time u.time) :
    current s i p t = rawTail s i p t := by
  cases hr : s.raw i p with
  | none => simp [current, rawTail, hr]
  | some origin =>
    have h := f.raw_support i p origin hr
    simp [current, rawTail, hr, pulse, h.1.trans ht.1, ht.2.trans_le h.2]

theorem WeakFlow.drive_eq_tailDrive {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (t : ℝ) (ht : t ∈ Ico s.time u.time) :
    drive s (f.path t) i t = tailDrive s (f.path t) i t := by
  unfold drive tailDrive
  apply Finset.sum_congr rfl
  intro p _
  rw [f.current_eq_rawTail i p t ht]

theorem WeakFlow.tailDrive_continuous {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) :
    ContinuousOn (fun t => tailDrive s (f.path t) i t) (Icc s.time u.time) := by
  apply continuousOn_finsetSum
  intro p _
  exact (Real.continuous_exp.comp_continuousOn (f.continuous i (.z p))).mul
    (rawTail_continuous s i p).continuousOn

/-- This derivative uses only the integral ODE and support, not strict guards. -/
theorem WeakFlow.ready_right_derivative {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (hm : s.main i = .ready) (t : ℝ)
    (ht : t ∈ Ico s.time u.time) :
    HasDerivWithinAt (fun v => f.path v i .q)
      ((1 / 2) * (1 / 10 - f.path t i .q) + tailDrive s (f.path t) i t) (Ici t) t := by
  let g := fun v => (1 / 2 : ℝ) * (1 / 10 - f.path v i .q) + tailDrive s (f.path v) i v
  have hc : ContinuousOn g (Icc s.time u.time) :=
    ((continuousOn_const.sub (f.continuous i .q)).const_mul (1 / 2)).add
      (f.tailDrive_continuous i)
  apply right_derivative_of_integral hc _ ht
  intro v hv
  have he := f.integral_eq v hv i .q
  have hchange : (∫ w in s.time..v, field θ s (f.path w) w i .q) = ∫ w in s.time..v, g w := by
    apply intervalIntegral.integral_congr_Ioo_of_le hv.1
    intro w hw
    simp only [field, hm, g, f.drive_eq_tailDrive i w ⟨hw.1.le, hw.2.trans_le hv.2⟩]
  rw [hchange] at he
  simpa only [f.initial] using he

/-- The same guard-independent argument applies to an auxiliary READY cell. -/
theorem WeakFlow.aux_ready_right_derivative {n θ s u} (f : @WeakFlow n θ s u)
    (i : Fin n) (p : Port) (hm : s.aux i p = .ready) (t : ℝ)
    (ht : t ∈ Ico s.time u.time) :
    HasDerivWithinAt (fun v => f.path v i (.m p))
      ((1 / 2) * (1 / 40 - f.path t i (.m p)) +
        (θ i).inputGain p * rawTail s i p t) (Ici t) t := by
  let g := fun v => (1 / 2 : ℝ) * (1 / 40 - f.path v i (.m p)) +
    (θ i).inputGain p * rawTail s i p v
  have hc : ContinuousOn g (Icc s.time u.time) :=
    ((continuousOn_const.sub (f.continuous i (.m p))).const_mul (1 / 2)).add
      ((rawTail_continuous s i p).continuousOn.const_mul _)
  apply right_derivative_of_integral hc _ ht
  intro v hv
  have he := f.integral_eq v hv i (.m p)
  have hchange : (∫ w in s.time..v, field θ s (f.path w) w i (.m p)) =
      ∫ w in s.time..v, g w := by
    apply intervalIntegral.integral_congr_Ioo_of_le hv.1
    intro w hw
    simp only [field, hm, ite_true, g,
      f.current_eq_rawTail i p w ⟨hw.1.le, hw.2.trans_le hv.2⟩]
  rw [hchange] at he
  simpa only [f.initial] using he

/-- A right derivative at an initial upper contact cannot be positive. -/
theorem right_derivative_nonpos_of_initial_upper_guard {y : ℝ → ℝ} {d s u : ℝ}
    (hu : s < u) (hd : HasDerivWithinAt y d (Ici s) s)
    (hupper : ∀ t ∈ Ico s u, y t ≤ y s) : d ≤ 0 := by
  have hlim : Tendsto (slope y s) (𝓝[>] s) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s)).mp
      hd.Ioi_of_Ici
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT hu] with t ht
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hupper t ⟨ht.1.le, ht.2⟩))
    (sub_nonneg.mpr ht.1.le)

/-- A positive weak flow cannot bypass any enabled transverse jump. Tangential
READY contacts remain permitted; all non-READY events retain strict urgency. -/
theorem WeakFlow.no_initial_transverse_jump {n θ route s u}
    (f : @WeakFlow n θ s u) (v : Snapshot n) (j : Jump route s v) :
    ¬ j.ContactTransversal θ := by
  have hg : WeakBeforeGuards s s.x := by
    simpa only [f.initial] using f.guards s.time ⟨le_rfl, f.positive⟩
  cases j with
  | fire i hm hq =>
    intro hpos
    have hd := f.ready_right_derivative i hm s.time ⟨le_rfl, f.positive⟩
    have hn := right_derivative_nonpos_of_initial_upper_guard f.positive hd (by
      intro t ht
      have h := (f.guards t ht).1 i
      simpa only [hm, f.initial, hq] using h)
    have he := f.drive_eq_tailDrive i s.time ⟨le_rfl, f.positive⟩
    simp only [f.initial] at hn he
    simp only [Jump.ContactTransversal, field, hm] at hpos
    linarith
  | mark i p hm hq =>
    intro hpos
    have hd := f.aux_ready_right_derivative i p hm s.time ⟨le_rfl, f.positive⟩
    have hn := right_derivative_nonpos_of_initial_upper_guard f.positive hd (by
      intro t ht
      have h := (f.guards t ht).2 i p
      simpa only [hm, f.initial, hq] using h)
    have he := f.current_eq_rawTail i p s.time ⟨le_rfl, f.positive⟩
    simp only [f.initial] at hn
    simp only [Jump.ContactTransversal, field, hm, ite_true] at hpos
    rw [← he] at hn
    linarith
  | fastEnd i hm hq =>
    have h := hg.1 i
    simp only [hm] at h
    linarith
  | reopen i hm hq =>
    have h := hg.1 i
    simp only [hm] at h
    linarith
  | silent i p hm hq =>
    have h := hg.2 i p
    simp only [hm] at h
    linarith
  | error i p hm hq =>
    have h := hg.2 i p
    simp only [hm] at h
    linarith
  | auxReady i p hm hq =>
    have h := hg.2 i p
    simp only [hm] at h
    linarith
  | arrive d before after hqueue hdue hfree =>
    have hd : d ∈ s.pending := by simp [hqueue]
    have h := f.pending_urgent d hd
    linarith [f.positive]
  | rawEnd i p origin hraw hdue =>
    have h := (f.raw_support i p origin hraw).2
    linarith [f.positive]

end KernelR.Hybrid
