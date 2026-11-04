import KernelR.HybridWeakFlow
import KernelR.HybridFlowUniqueness

/-! A weak READY upper guard can be made strict by an exact homogeneous
perturbation. READY charges do not enter actuation or work, so gains, recovery
and energy are unchanged. Applying the same perturbation to two paths reduces
their comparison to the existing integral-flow uniqueness theorem. -/
namespace KernelR.Hybrid
open Set MeasureTheory

noncomputable def weakShiftAmount (ε origin t : ℝ) : ℝ :=
  ε * Real.exp (-(1 / 2 : ℝ) * (t - origin))

noncomputable def weakShiftCorrection {n} (s : Snapshot n) (ε origin t : ℝ)
    (i : Fin n) : Coord → ℝ
  | .q => if s.main i = .ready then weakShiftAmount ε origin t else 0
  | .m p => if s.aux i p = .ready then weakShiftAmount ε origin t else 0
  | _ => 0

noncomputable def weakShiftValues {n} (s : Snapshot n) (ε origin t : ℝ)
    (x : Values n) : Values n := fun i c => x i c - weakShiftCorrection s ε origin t i c

noncomputable def weakShiftSnapshot {n} (s : Snapshot n) (ε origin : ℝ) : Snapshot n :=
  {s with x := weakShiftValues s ε origin s.time s.x}

theorem weakShiftCorrection_continuous {n} (s : Snapshot n) (ε origin : ℝ)
    (i : Fin n) (c : Coord) : Continuous (fun t => weakShiftCorrection s ε origin t i c) := by
  cases c with
  | q =>
    by_cases mode : s.main i = .ready <;> simp only [weakShiftCorrection, mode, ite_true, ite_false]
    · unfold weakShiftAmount; fun_prop
    · fun_prop
  | m p =>
    by_cases mode : s.aux i p = .ready <;> simp only [weakShiftCorrection, mode, ite_true, ite_false]
    · unfold weakShiftAmount; fun_prop
    · fun_prop
  | z p => exact continuous_const
  | b => exact continuous_const
  | energy => exact continuous_const

theorem weakShiftCorrection_derivative {n} (s : Snapshot n) (ε origin t : ℝ)
    (i : Fin n) (c : Coord) :
    HasDerivAt (fun v => weakShiftCorrection s ε origin v i c)
      (-(1 / 2 : ℝ) * weakShiftCorrection s ε origin t i c) t := by
  have hd : HasDerivAt (weakShiftAmount ε origin)
      (-(1 / 2 : ℝ) * weakShiftAmount ε origin t) t := by
    convert (((hasDerivAt_id t).sub_const origin).const_mul (-(1 / 2 : ℝ))).exp.const_mul ε using 1
    · rfl
    · dsimp [weakShiftAmount]; ring
  cases c <;> simp only [weakShiftCorrection] <;> first
    | (split_ifs <;> first | exact hd | simpa using (hasDerivAt_const t (0 : ℝ)))
    | simpa using (hasDerivAt_const t (0 : ℝ))

theorem weakShiftCorrection_integral {n} (s : Snapshot n) (ε origin t : ℝ)
    (i : Fin n) (c : Coord) :
    (∫ v in origin..t, (1 / 2 : ℝ) * weakShiftCorrection s ε origin v i c) =
      weakShiftCorrection s ε origin origin i c - weakShiftCorrection s ε origin t i c := by
  have hd (v : ℝ) : HasDerivAt (fun w => -weakShiftCorrection s ε origin w i c)
      ((1 / 2 : ℝ) * weakShiftCorrection s ε origin v i c) v := by
    convert (weakShiftCorrection_derivative s ε origin v i c).neg using 1
    ring
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
    (((weakShiftCorrection_continuous s ε origin i c).const_mul (1 / 2 : ℝ)).intervalIntegrable origin t)
  linarith

@[simp] theorem weakShift_drive {n} (s : Snapshot n) (ε origin t : ℝ) (x : Values n)
    (i : Fin n) :
    drive (weakShiftSnapshot s ε origin) (weakShiftValues s ε origin t x) i t = drive s x i t := by
  simp [drive, weakShiftSnapshot, weakShiftValues, weakShiftCorrection, current]

@[simp] theorem weakShift_current {n} (s : Snapshot n) (ε origin t : ℝ)
    (i : Fin n) (p : Port) : current (weakShiftSnapshot s ε origin) i p t = current s i p t := rfl

@[simp] theorem weakShift_errorAct {n θ} (s : Snapshot n) (ε origin t : ℝ) (x : Values n)
    (i : Fin n) (p : Port) :
    errorAct θ (weakShiftSnapshot s ε origin) (weakShiftValues s ε origin t x) i p =
      errorAct θ s x i p := by
  by_cases mode : s.aux i p = .error
  · simp [errorAct, weakShiftSnapshot, weakShiftValues, weakShiftCorrection, mode]
  · simp [errorAct, weakShiftSnapshot, mode]

@[simp] theorem weakShift_markAct {n θ} (s : Snapshot n) (ε origin t : ℝ) (x : Values n)
    (i : Fin n) (p : Port) :
    markAct θ (weakShiftSnapshot s ε origin) (weakShiftValues s ε origin t x) i p =
      markAct θ s x i p := by
  by_cases mode : s.aux i p = .mark
  · simp [markAct, weakShiftSnapshot, weakShiftValues, weakShiftCorrection, mode]
  · simp [markAct, weakShiftSnapshot, mode]

@[simp] theorem weakShift_work {n θ} (s : Snapshot n) (ε origin t : ℝ) (x : Values n)
    (i : Fin n) :
    work θ (weakShiftSnapshot s ε origin) (weakShiftValues s ε origin t x) i t = work θ s x i t := by
  have aux : ∀ p, (if s.aux i p = .ready then (θ i).inputGain p * current s i p t
      else auxDrain (θ i) (s.aux i p) p (weakShiftValues s ε origin t x i (.m p))) =
      (if s.aux i p = .ready then (θ i).inputGain p * current s i p t
      else auxDrain (θ i) (s.aux i p) p (x i (.m p))) := by
    intro p
    cases mode : s.aux i p <;> simp [weakShiftValues, weakShiftCorrection, mode]
  simp only [work, show (weakShiftSnapshot s ε origin).main = s.main from rfl,
    show (weakShiftSnapshot s ε origin).aux = s.aux from rfl,
    weakShift_current, weakShift_drive, weakShift_errorAct, weakShift_markAct]
  simp_rw [aux]
  cases mode : s.main i <;> simp [weakShiftValues, weakShiftCorrection, mode]

theorem weakShift_field {n θ} (s : Snapshot n) (ε origin t : ℝ) (x : Values n)
    (i : Fin n) (c : Coord) :
    field θ (weakShiftSnapshot s ε origin) (weakShiftValues s ε origin t x) t i c =
      field θ s x t i c + (1 / 2 : ℝ) * weakShiftCorrection s ε origin t i c := by
  cases c with
  | q =>
    cases mode : s.main i <;>
      simp [field, weakShiftSnapshot, weakShiftValues, weakShiftCorrection, mode, drive, current]
    ring
  | m p =>
    cases mode : s.aux i p <;>
      simp [field, weakShiftSnapshot, weakShiftValues, weakShiftCorrection, mode, current]
    ring
  | z p => simp only [field, weakShift_errorAct, weakShiftCorrection, mul_zero, add_zero]
  | b => simp only [field, weakShift_markAct, weakShiftCorrection, mul_zero, add_zero]
  | energy => simp [field, weakShift_work, weakShiftValues, weakShiftCorrection]

noncomputable def WeakFlow.strictify {n θ s u} (f : @WeakFlow n θ s u) (ε : ℝ) (hε : 0 < ε) :
    Flow θ (weakShiftSnapshot s ε s.time) (weakShiftSnapshot u ε s.time) where
  positive := f.positive
  path := fun t => weakShiftValues s ε s.time t (f.path t)
  initial := by simp [weakShiftSnapshot, f.initial]
  final := by
    change weakShiftValues s ε s.time u.time (f.path u.time) =
      weakShiftValues u ε s.time u.time u.x
    rw [f.final]
    funext i c
    cases c <;> simp [weakShiftValues, weakShiftCorrection, f.main_fixed, f.aux_fixed]
  main_fixed := f.main_fixed
  aux_fixed := f.aux_fixed
  raw_fixed := f.raw_fixed
  queue_fixed := f.queue_fixed
  continuous := fun i c => (f.continuous i c).sub
    (weakShiftCorrection_continuous s ε s.time i c).continuousOn
  integrable := by
    intro i c
    simp_rw [weakShift_field]
    exact (f.integrable i c).add
      (((weakShiftCorrection_continuous s ε s.time i c).const_mul (1 / 2 : ℝ)).intervalIntegrable _ _)
  mark_integrable := by
    intro i p
    simp_rw [weakShift_markAct]
    exact f.mark_integrable i p
  integral_eq := by
    intro t ht i c
    change t ∈ Icc s.time u.time at ht
    change weakShiftValues s ε s.time t (f.path t) i c =
      weakShiftValues s ε s.time s.time s.x i c +
        ∫ v in s.time..t,
          field θ (weakShiftSnapshot s ε s.time) (weakShiftValues s ε s.time v (f.path v)) v i c
    simp_rw [weakShift_field]
    rw [intervalIntegral.integral_add
      ((f.integrable i c).mono_set (by
        rw [uIcc_of_le ht.1, uIcc_of_le f.positive.le]
        exact Icc_subset_Icc le_rfl ht.2))
      (((weakShiftCorrection_continuous s ε s.time i c).const_mul (1 / 2 : ℝ)).intervalIntegrable _ _),
      weakShiftCorrection_integral]
    dsimp only [weakShiftValues]
    rw [f.integral_eq t ht i c]
    ring
  guards := by
    intro t ht
    have positive : 0 < weakShiftAmount ε s.time t := mul_pos hε (Real.exp_pos _)
    constructor
    · intro i
      have guard := (f.guards t ht).1 i
      cases mode : s.main i <;>
        simp_all [weakShiftSnapshot, weakShiftValues, weakShiftCorrection]
      linarith
    · intro i p
      have guard := (f.guards t ht).2 i p
      cases mode : s.aux i p <;>
        simp_all [weakShiftSnapshot, weakShiftValues, weakShiftCorrection]
      linarith
  raw_support := f.raw_support
  pending_urgent := f.pending_urgent

theorem weakShiftSnapshot_physical {n θ} {s : Snapshot n} (hs : PhysicalInvariant θ s)
    {ε : ℝ} (hε : 0 ≤ ε) (origin : ℝ) : PhysicalInvariant θ (weakShiftSnapshot s ε origin) := by
  have nonneg : 0 ≤ weakShiftAmount ε origin s.time := mul_nonneg hε (Real.exp_pos _).le
  constructor
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using (hs.region i).1
    · have hq := (hs.region i).2.1
      cases mode : s.main i <;> simp [weakShiftSnapshot, weakShiftValues, weakShiftCorrection, mode]
      all_goals linarith
    · intro p
      have hm := (hs.region i).2.2 p
      cases mode : s.aux i p <;>
        simp_all [weakShiftSnapshot, weakShiftValues, weakShiftCorrection, auxUpper]
      linarith
  · intro i p
    simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using hs.gain_cap i p
  · intro i
    simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using hs.recovery_cap i
  · intro i
    simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using hs.reserve i

/-- The exact perturbation also transfers physical bounds back to the weak
flow. READY endpoint bounds follow from its weak guards and continuity. -/
theorem WeakFlow.physical_invariant {n θ ε s u} (f : @WeakFlow n θ s u)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s) : PhysicalInvariant θ u := by
  let strict := f.strictify 1 (by norm_num)
  let trace : Execution θ (fun _ _ => []) (weakShiftSnapshot s 1 s.time)
      (weakShiftSnapshot u 1 s.time) := .cons (.flow strict) (.nil _)
  have shifted := trace.physical_invariant hb
    (weakShiftSnapshot_physical hs (by norm_num) s.time)
  constructor
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using (shifted.region i).1
    · cases mode : s.main i with
      | ready =>
        have bound : ∀ t ∈ Icc s.time u.time, f.path t i .q ≤ 1 := by
          apply continuous_bound_from_Ico f.positive (f.continuous i .q)
          intro t ht
          simpa only [WeakBeforeGuards, mode] using (f.guards t ht).1 i
        simpa only [f.final] using bound u.time ⟨f.positive.le, le_rfl⟩
      | fast | slow =>
        simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection, f.main_fixed, mode]
          using (shifted.region i).2.1
    · intro p
      cases mode : s.aux i p with
      | ready =>
        have bound : ∀ t ∈ Icc s.time u.time, f.path t i (.m p) ≤ 1 := by
          apply continuous_bound_from_Ico f.positive (f.continuous i (.m p))
          intro t ht
          simpa only [WeakBeforeGuards, mode] using (f.guards t ht).2 i p
        simpa [f.final, f.aux_fixed, mode, auxUpper] using bound u.time ⟨f.positive.le, le_rfl⟩
      | mark | silent | error =>
        simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection, f.aux_fixed, mode]
          using (shifted.region i).2.2 p
  · intro i p
    simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using shifted.gain_cap i p
  · intro i
    simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using shifted.recovery_cap i
  · intro i
    simpa [weakShiftSnapshot, weakShiftValues, weakShiftCorrection] using shifted.reserve i

/-- Weak integral flows agree exactly; strictification cancels pointwise. -/
theorem WeakFlow.path_unique {n θ ε s u v} (f : @WeakFlow n θ s u) (g : WeakFlow θ s v)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) : f.path t = g.path t := by
  have equal := (f.strictify 1 (by norm_num)).path_unique (g.strictify 1 (by norm_num)) hb
    (weakShiftSnapshot_physical hs (by norm_num) s.time) hf hg
  funext i c
  have coord := congrFun (congrFun equal i) c
  dsimp only [WeakFlow.strictify, weakShiftValues] at coord
  linarith

theorem Flow.path_unique_weak {n θ ε s u v} (f : @Flow n θ s u) (g : WeakFlow θ s v)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s) {t : ℝ}
    (hf : t ∈ Icc s.time u.time) (hg : t ∈ Icc s.time v.time) : f.path t = g.path t :=
  f.toWeak.path_unique g hb hs hf hg

#print axioms WeakFlow.path_unique
#print axioms Flow.path_unique_weak

end KernelR.Hybrid
