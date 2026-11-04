import KernelR.HybridCellOrbitGerm
import KernelR.HybridCrossingExecution
import KernelR.HybridUrgentMoves

/-! A genuine full-cell grazing orbit, deliberately outside PhysicalBox and the
protocol. At q=1 its slope is zero and its right continuation lies below one. -/
namespace KernelR.Hybrid.GrazingFixture
open Set Filter
open scoped Topology

noncomputable def gain : ℝ := (9 / 20) / a

theorem a_positive : 0 < a := by linarith [a_coarse_bounds.1]

theorem gain_positive : 0 < gain := div_pos (by norm_num) a_positive

noncomputable def parameters : Fin 1 → Parameters := fun _ => {
  cap := fun _ => 1
  lm := fun _ => 1
  ls := fun _ => 1
  le := fun _ => 1
  inputGain := fun _ => 0
}

noncomputable def snapshot : Snapshot 1 := {
  time := 0
  x := fun _ c => match c with
    | .q => 1
    | .m _ => 1 / 40
    | .z p => if p = 0 then Real.log gain else 0
    | .b => 1 / 10
    | .energy => 100
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ p => if p = 0 then some 0 else none
  pending := []
}

noncomputable def orbit : CellOrbitGerm parameters snapshot 0 := by
  refine {
    duration := 1 / 2
    positive := by norm_num
    path := cellOrbitValues parameters snapshot
    initial := congrFun (cellOrbitValues_initial (θ := parameters) snapshot) 0
    derivative := ?_
  }
  intro t ht c
  have raw (p : Port) : current snapshot 0 p t = cellTailCurrent snapshot 0 p t := by
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t < 1 := by have := ht.2; change t < 0 + 1 / 2 at this; linarith
    fin_cases p <;> simp [current, snapshot, pulse, cellTailCurrent, ht0, ht1]
  have he (p : Port) : errorAct parameters snapshot (cellOrbitValues parameters snapshot t) 0 p = 0 := by
    simp [errorAct, snapshot]
  have hm (p : Port) : markAct parameters snapshot (cellOrbitValues parameters snapshot t) 0 p = 0 := by
    simp [markAct, snapshot]
  have hz (p : Port) : cellOrbitValues parameters snapshot t 0 (.z p) = snapshot.x 0 (.z p) := rfl
  have hd : drive snapshot (cellOrbitValues parameters snapshot t) 0 t =
      ∑ p : Port, Real.exp (snapshot.x 0 (.z p)) * cellTailCurrent snapshot 0 p t := by
    simp only [drive, hz, raw]
  apply (cellOrbitValues_derivative snapshot 0 c t).congr_deriv
  symm
  have hmain : snapshot.main 0 = .ready := rfl
  have haux (p : Port) : snapshot.aux 0 p = .ready := rfl
  cases c with
  | q => simp only [field, cellOrbitRhs, hmain, hd]
  | m p => simp only [field, cellOrbitRhs, raw]
  | z p => exact he p
  | b => simp [field, cellOrbitRhs, hm]
  | energy =>
    simp only [field, cellOrbitRhs, work, he, hm, cellSmoothWork, hmain, haux, hd,
      Finset.sum_const_zero, add_zero, ite_true]
    simp only [raw, cellOrbitValues]

theorem amplitude : cellMainAmplitude snapshot 0 = gain := by
  have ha : a ≠ 0 := ne_of_gt a_positive
  simp [cellMainAmplitude, snapshot, current, pulse, Fin.sum_univ_succ,
    Real.exp_log gain_positive, ha]

 theorem orbit_q (t : ℝ) : orbit.path t 0 .q = readyPulse 1 gain 0 t := by
  change readyPulse 1 (cellMainAmplitude snapshot 0) 0 t = _
  rw [amplitude]

theorem pulse_derivative (t : ℝ) :
    HasDerivAt (readyPulse 1 gain 0)
      ((9 / 20) * a / (a - 1 / 2) * (Real.exp (-a * t) - Real.exp (-(1 / 2) * t))) t := by
  have ha : a ≠ 0 := ne_of_gt a_positive
  have hd : a - 1 / 2 ≠ 0 := by linarith [a_coarse_bounds.1]
  apply (readyPulse_derivative 1 gain 0 t).congr_deriv
  dsimp [readyPulse, response, gain]
  have h2 : -1 + a * 2 ≠ 0 := by linarith [a_coarse_bounds.1]
  field_simp [ha, hd]
  ring_nf
  have hmul : (-1 + a * 2) * (-1 + a * 2)⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination (180 * (Real.exp (t * (-1 / 2)) - Real.exp (-(t * a)))) * hmul

theorem pulse_strictAnti : StrictAntiOn (readyPulse 1 gain 0) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · change ContinuousOn (fun t => readyPulse 1 gain 0 t) (Ici 0)
    dsimp [readyPulse, response]
    fun_prop
  · intro t ht
    rw [interior_Ici, mem_Ioi] at ht
    rw [(pulse_derivative t).deriv]
    have hp : 0 < (9 / 20 : ℝ) * a / (a - 1 / 2) :=
      div_pos (mul_pos (by norm_num) a_positive) (by linarith [a_coarse_bounds.1])
    have he : Real.exp (-a * t) < Real.exp (-(1 / 2) * t) := by
      apply Real.exp_lt_exp.mpr
      nlinarith [a_coarse_bounds.1]
    exact mul_neg_of_pos_of_neg hp (sub_neg.mpr he)

theorem orbit_zero_derivative : HasDerivAt (fun t => orbit.path t 0 .q) 0 0 := by
  have hfun : (fun t => orbit.path t 0 .q) = readyPulse 1 gain 0 := funext orbit_q
  rw [hfun]
  simpa using pulse_derivative 0

/-- This is an actual orbit, not an assumed trajectory. In particular zero
slope at a READY threshold does not imply an ascending crossing. -/
theorem genuine_grazing_contact :
    ∃ germ : CellOrbitGerm parameters snapshot 0,
      snapshot.x 0 .q = 1 ∧ field parameters snapshot snapshot.x snapshot.time 0 .q = 0 ∧
      ∀ t : ℝ, 0 < t → germ.path t 0 .q < 1 := by
  refine ⟨orbit, rfl, ?_, ?_⟩
  · have hfield : drive snapshot snapshot.x 0 0 = gain * a := by
      simp [drive, snapshot, current, pulse, Fin.sum_univ_succ,
        Real.exp_log gain_positive]
    rw [show snapshot.time = 0 from rfl]
    change (1 / 2 : ℝ) * (1 / 10 - 1) + drive snapshot snapshot.x 0 0 = 0
    rw [hfield]
    dsimp [gain]
    field_simp [ne_of_gt a_positive]
    ring
  · intro t ht
    rw [orbit_q]
    have h := pulse_strictAnti (show (0 : ℝ) ∈ Ici 0 from (by simp)) ht.le ht
    simpa only [readyPulse_initial] using h

/-- The constructed full-cell orbit does not cross the threshold to its right. -/
theorem orbit_no_ascending_crossing :
    ¬ ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 < orbit.path t 0 .q := by
  intro above
  obtain ⟨t, ht, htime⟩ := (above.and self_mem_nhdsWithin).exists
  have below : orbit.path t 0 .q < 1 := by
    rw [orbit_q]
    have h := pulse_strictAnti (show (0 : ℝ) ∈ Ici 0 from (by simp)) htime.le htime
    simpa only [readyPulse_initial] using h
  linarith

noncomputable def endpoint : Snapshot 1 := readyInputEnd parameters snapshot 0 0 (1 / 4)

theorem readyInput_q (t : ℝ) : readyInputValues parameters snapshot 0 0 t 0 .q =
    readyPulse 1 gain 0 t := by
  simp [readyInputValues, readyInputMainAmplitude, snapshot, Real.exp_log gain_positive]

private theorem input_field (t : ℝ) (ht : 0 ≤ t ∧ t < 1) (j : Fin 1) (c : Coord) :
    field parameters snapshot (readyInputValues parameters snapshot 0 0 t) t j c =
      readyInputRhs parameters snapshot 0 0 t j c := by
  apply readyInput_field snapshot 0 0 (by intros; rfl) (by intros; rfl) rfl _ t (by simpa only [snapshot, zero_add] using ht) j c
  intro k p h
  have hk : k = 0 := Fin.eq_zero k
  rcases h with h | h
  · exact (h hk).elim
  · simp [snapshot, h]

/-- A real positive weak flow starts at the grazing threshold and descends.
The guards permit equality only at the initial time. -/
noncomputable def grazingWeakFlow : WeakFlow parameters snapshot endpoint where
  positive := by norm_num [snapshot, endpoint, readyInputEnd]
  path := readyInputValues parameters snapshot 0 0
  initial := readyInputValues_initial snapshot 0 0
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := by
    intro j c
    exact (continuous_iff_continuousAt.mpr (fun t =>
      (readyInputValues_derivative (θ := parameters) snapshot 0 0 t j c).continuousAt)).continuousOn
  integrable := by
    intro j c
    have hc : ContinuousOn (fun t => field parameters snapshot
        (readyInputValues parameters snapshot 0 0 t) t j c) (Icc snapshot.time endpoint.time) := by
      apply (readyInputRhs_continuous (θ := parameters) snapshot 0 0 j c).continuousOn.congr
      intro t ht
      exact input_field t ⟨ht.1, by have := ht.2; change t ≤ (1 / 4 : ℝ) at this; linarith⟩ j c
    exact hc.intervalIntegrable_of_Icc (by norm_num [snapshot, endpoint, readyInputEnd])
  mark_integrable := by
    intro j p
    simp only [markAct, snapshot, reduceCtorEq, false_and, ite_false]
    exact intervalIntegrable_const
  integral_eq := by
    intro t ht j c
    have rhs := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => readyInputValues_derivative (θ := parameters) snapshot 0 0 v j c)
      ((readyInputRhs_continuous (θ := parameters) snapshot 0 0 j c).intervalIntegrable snapshot.time t)
    rw [readyInputValues_initial] at rhs
    have heq : (∫ v in snapshot.time..t,
        field parameters snapshot (readyInputValues parameters snapshot 0 0 v) v j c) =
        ∫ v in snapshot.time..t, readyInputRhs parameters snapshot 0 0 v j c := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le ht.1] at hv
      apply input_field v ⟨hv.1, ?_⟩ j c
      have ht4 : t ≤ (1 / 4 : ℝ) := ht.2
      linarith [hv.2]
    rw [heq]
    linarith
  guards := by
    intro t ht
    constructor
    · intro j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      change readyInputValues parameters snapshot 0 0 t 0 .q ≤ 1
      rw [readyInput_q]
      by_cases zero : t = 0
      · subst t; simp only [readyPulse_initial, le_refl]
      · have htime : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm zero)
        have h := pulse_strictAnti (show (0 : ℝ) ∈ Ici 0 from (by simp)) htime.le htime
        exact le_of_lt (by simpa only [readyPulse_initial] using h)
    · intro j p
      change readyInputValues parameters snapshot 0 0 t j (.m p) ≤ 1
      norm_num [readyInputValues, readyInputAuxAmplitude, parameters, snapshot, auxPulse, readyPulse]
  raw_support := by
    intro j p origin hraw
    by_cases hp : p = 0
    · subst p
      have horigin : origin = 0 := by simpa [snapshot] using hraw.symm
      subst origin
      norm_num [snapshot, endpoint, readyInputEnd]
    · simp [snapshot, hp] at hraw
  pending_urgent := by intro d hd; exact (List.not_mem_nil hd).elim

/-- This crossing execution contains a positive flow and no FIRE. -/
noncomputable def grazingCrossingExecution :
    CrossingExecution parameters (fun _ _ => []) snapshot endpoint := {
  execution := .cons (.flow grazingWeakFlow) (.nil _)
  crossings := trivial
}

/-- Native first-contact urgency excludes every positive native flow from
this same initial state, because FIRE is already enabled at q=1. -/
theorem no_native_flow (v : Snapshot 1) : IsEmpty (Flow parameters snapshot v) := by
  constructor
  intro flow
  let jump : Jump (fun _ _ => []) snapshot _ := Jump.fire snapshot 0 rfl rfl
  exact (flow.no_initial_jump _).false jump

end KernelR.Hybrid.GrazingFixture
