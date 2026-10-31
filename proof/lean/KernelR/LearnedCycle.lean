import KernelR.HybridFrozen
import KernelR.LearnedCycleBounds

/-! Derived event clocks for a stable learned pulse. The phase ordering is
proved uniformly from the physical box and first crossings; it is not a supplied
case word. Assembly of the full reacting execution remains a separate step. -/
namespace KernelR.Hybrid
open Set

structure LearnedClock (theta : Parameters) (port : Port) (gain sensor : ℝ) where
  fire : ℝ
  auxiliary : ℝ
  fire_lower : 1/2 < fire
  fire_upper : fire ≤ 9/10
  fire_value : learnedHead gain fire = 1
  fire_before : ∀ t ∈ Ico 0 fire, learnedHead gain t < 1
  auxiliary_lower : 1/100 < auxiliary
  auxiliary_upper : auxiliary ≤ 1/20
  auxiliary_value : auxPulse sensor (theta.inputGain port) 0 auxiliary = 1
  auxiliary_before : ∀ t ∈ Ico 0 auxiliary, auxPulse sensor (theta.inputGain port) 0 t < 1

theorem learned_clock_exists {n theta epsilon} (hb : @PhysicalBox n theta epsilon)
    (i : Fin n) (port : Port) {gain sensor : ℝ}
    (hg : 9/5 ≤ gain ∧ gain ≤ 19/10) (hs : |sensor-1/40| ≤ 1/100000) :
    Nonempty (LearnedClock (theta i) port gain sensor) := by
  obtain ⟨f, _, hfu, hfv, hff⟩ := learned_latency_exists hg
  obtain ⟨tau, htl, htu, htv, htf⟩ := auxiliary_latency_exists hs (hb.input_gain_bounds i port)
  exact ⟨⟨f, tau, learned_latency_after_half hg hff, hfu, hfv, hff.2.2,
    htl, htu, htv, htf.2.2⟩⟩

noncomputable def LearnedClock.markEnd {theta port gain sensor}
    (clock : LearnedClock theta port gain sensor) : ℝ :=
  clock.auxiliary + Real.log (5/4) / theta.lm port

noncomputable def LearnedClock.errorStart {theta port gain sensor}
    (clock : LearnedClock theta port gain sensor) : ℝ :=
  clock.markEnd + Real.log 8 / theta.ls port

noncomputable def LearnedClock.auxiliaryEnd {theta port gain sensor}
    (clock : LearnedClock theta port gain sensor) : ℝ :=
  clock.errorStart + a / theta.le port

noncomputable def LearnedClock.reopen {theta port gain sensor}
    (clock : LearnedClock theta port gain sensor) (recovery : ℝ) : ℝ :=
  clock.fire + 1 + Real.log (5/2) / recovery

structure CycleChronology {theta port gain sensor}
    (clock : LearnedClock theta port gain sensor) (recovery : ℝ) : Prop where
  auxiliary_positive : 0 < clock.auxiliary
  mark_span : clock.auxiliary < clock.markEnd
  silent_span : clock.markEnd < clock.errorStart
  error_span : clock.errorStart < clock.auxiliaryEnd
  mark_before_fire : clock.markEnd < clock.fire
  fire_before_raw_end : clock.fire < 1
  fire_before_error : clock.fire < clock.errorStart
  raw_end_before_auxiliary_end : 1 < clock.auxiliaryEnd
  auxiliary_end_before_fast_end : clock.auxiliaryEnd < clock.fire+1
  fast_end_before_reopen : clock.fire+1 < clock.reopen recovery
  reopen_before_gap : clock.reopen recovery < 15/2

theorem LearnedClock.chronology {n theta epsilon} (hb : @PhysicalBox n theta epsilon)
    (i : Fin n) (port : Port) {gain sensor recovery : ℝ}
    (clock : LearnedClock (theta i) port gain sensor)
    (hr : 17/100 ≤ recovery ∧ recovery ≤ 1/5) : CycleChronology clock recovery := by
  have hm := hb.mark_duration_bounds i port
  have hs := hb.silent_duration_bounds i port
  have he := hb.error_duration_bounds i port
  have hfl := clock.fire_lower
  have hfu := clock.fire_upper
  have htl := clock.auxiliary_lower
  have htu := clock.auxiliary_upper
  have hrl : clock.fire+1 < clock.reopen recovery := by
    have hpos : 0 < Real.log (5/2) / recovery :=
      div_pos (Real.log_pos (by norm_num)) (by linarith)
    dsimp [reopen]; linarith
  constructor
  · linarith
  · dsimp [markEnd]; linarith [hm.1]
  · dsimp [errorStart]; linarith [hs.1]
  · dsimp [auxiliaryEnd]; linarith [he.1]
  · dsimp [markEnd]; linarith [hm.2]
  · linarith
  · dsimp [errorStart, markEnd]; linarith [hm.1, hs.1]
  · dsimp [auxiliaryEnd, errorStart, markEnd]; linarith [hm.1, hs.1, he.1]
  · dsimp [auxiliaryEnd, errorStart, markEnd]; linarith [hm.2, hs.2, he.2]
  · exact hrl
  · exact learned_return_before_gap hr hfu

/-- Exact decay endpoints and strict pre-guard inequalities, for actual real
rates. These give the protected-mode guard proofs for the cycle segments. -/
theorem decay_section_endpoint {initial final rate : ℝ} (hi : 0 < initial)
    (hf : 0 < final) (hr : 0 < rate) :
    initial * Real.exp (-rate*(Real.log (initial/final)/rate)) = final := by
  have hn : rate ≠ 0 := ne_of_gt hr
  rw [show -rate*(Real.log (initial/final)/rate) = -Real.log (initial/final) by field_simp,
    Real.exp_neg, Real.exp_log (div_pos hi hf)]
  field_simp

theorem decay_section_before {initial final rate t : ℝ} (hi : 0 < initial)
    (hf : 0 < final) (hr : 0 < rate) (ht : t < Real.log (initial/final)/rate) :
    final < initial * Real.exp (-rate*t) := by
  have hh := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr
    (show -rate*(Real.log (initial/final)/rate) < -rate*t by nlinarith)) hi
  rw [decay_section_endpoint hi hf hr] at hh
  exact hh

end KernelR.Hybrid
