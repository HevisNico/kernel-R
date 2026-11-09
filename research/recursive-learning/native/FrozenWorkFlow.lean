import KernelR.HybridCellOrbitGerm

/-! An explicit frozen-memory orbit is a physical flow when the learning
gates remain closed and the supplied interval respects the guards and queue. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid MeasureTheory Set

@[fun_prop] private theorem frozen_values_continuous {n θ} (s : Snapshot n) (i : Fin n) (c : Coord) :
    Continuous (fun t => cellOrbitValues θ s t i c) := by
  cases c with
  | energy =>
    exact (by unfold relax; fun_prop : Continuous (relax 10 100 (s.x i .energy) s.time)).sub
      (linearConvolution_continuous (cellSmoothWork_continuous s i) 10 s.time)
  | q => exact cellBaseValues_continuous (θ := θ) s i .q
  | m p => exact cellBaseValues_continuous (θ := θ) s i (.m p)
  | z p => exact continuous_const
  | b => exact continuous_const

private theorem frozen_rhs_continuous {n θ} (s : Snapshot n) (i : Fin n) (c : Coord) :
    Continuous (fun t => cellOrbitRhs θ s t i c) := by
  cases c with
  | q =>
    cases hm : s.main i <;> simp only [cellOrbitRhs, hm, cellTailCurrent]
    all_goals fun_prop (disch := first | exact frozen_values_continuous _ _ _)
  | m p =>
    by_cases hm : s.aux i p = .ready
    · simp only [cellOrbitRhs, hm, ite_true, cellTailCurrent]
      fun_prop (disch := exact frozen_values_continuous _ _ _)
    · cases mode : s.aux i p <;> simp_all only [cellOrbitRhs, reduceCtorEq, ite_false, auxDrain, neg_zero]
      all_goals fun_prop (disch := exact frozen_values_continuous _ _ _)
  | z _ => exact continuous_const
  | b => exact continuous_const
  | energy =>
    simp only [cellOrbitRhs]
    fun_prop (disch := first | exact frozen_values_continuous _ _ _ | exact cellSmoothWork_continuous _ _)

private theorem frozen_raw_tail {n} {s : Snapshot n} {T t : ℝ}
    (support : ∀ i p origin, s.raw i p = some origin → origin ≤ s.time ∧ T ≤ origin + 1)
    (ht : t ∈ Ico s.time T) (i : Fin n) (p : Port) :
    current s i p t = cellTailCurrent s i p t := by
  cases raw : s.raw i p with
  | none => simp [current, cellTailCurrent, raw]
  | some origin =>
    have range := support i p origin raw
    have now : origin ≤ t ∧ t < origin + 1 := ⟨range.1.trans ht.1, ht.2.trans_le range.2⟩
    have start : origin ≤ s.time ∧ s.time < origin + 1 := ⟨range.1, ht.1.trans_lt now.2⟩
    simp only [current, cellTailCurrent, raw, pulse, ite_eq_left now, ite_eq_left start]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring

private theorem frozen_field {n θ} (s : Snapshot n) (t : ℝ) (i : Fin n)
    (raw : ∀ p, current s i p t = cellTailCurrent s i p t)
    (error : ∀ p, s.main i ≠ .ready ∨ s.aux i p ≠ .error ∨ Real.log ((θ i).cap p) ≤ s.x i (.z p))
    (mark : ∀ p, s.main i = .ready ∨ s.aux i p ≠ .mark ∨ 11 / 10 ≤ s.x i .b)
    (c : Coord) :
    field θ s (cellOrbitValues θ s t) t i c = cellOrbitRhs θ s t i c := by
  have ez (p : Port) : errorAct θ s (cellOrbitValues θ s t) i p = 0 := by
    rcases error p with h | h | h
    · simp [errorAct, h]
    · simp [errorAct, h]
    · simp [errorAct, cellOrbitValues, cellBaseValues, not_lt_of_ge h]
  have mb (p : Port) : markAct θ s (cellOrbitValues θ s t) i p = 0 := by
    rcases mark p with h | h | h
    · simp [markAct, h]
    · simp [markAct, h]
    · simp [markAct, cellOrbitValues, cellBaseValues, not_lt_of_ge h]
  have drv : drive s (cellOrbitValues θ s t) i t =
      ∑ p, Real.exp (s.x i (.z p)) * cellTailCurrent s i p t := by
    simp only [drive, cellOrbitValues, cellBaseValues, raw]
  cases c with
  | q => cases hm : s.main i <;> simp [field, cellOrbitRhs, hm, drv, cellOrbitValues, cellBaseValues]
  | m p => simp [field, cellOrbitRhs, raw]
  | z p => exact ez p
  | b => simp [field, cellOrbitRhs, mb]
  | energy =>
    have same : work θ s (cellOrbitValues θ s t) i t = cellSmoothWork θ s i t := by
      simp only [work, ez, mb, Finset.sum_const_zero, add_zero, cellSmoothWork, drv, raw, cellOrbitValues]
      rfl
    simp [field, cellOrbitRhs, same]

noncomputable def frozenWorkEnd {n} (θ : Fin n → Parameters) (s : Snapshot n) (T : ℝ) : Snapshot n :=
  {s with time := T, x := cellOrbitValues θ s T}

/-- Promote the existing frozen cell orbit to a native flow on any guarded
interval before raw expiry. This covers both saturated MARK and saturated ERROR. -/
noncomputable def frozenWorkFlow {n θ} (s : Snapshot n) {T : ℝ} (positive : s.time < T)
    (error : ∀ i p, s.main i ≠ .ready ∨ s.aux i p ≠ .error ∨ Real.log ((θ i).cap p) ≤ s.x i (.z p))
    (mark : ∀ i p, s.main i = .ready ∨ s.aux i p ≠ .mark ∨ 11 / 10 ≤ s.x i .b)
    (support : ∀ i p origin, s.raw i p = some origin → origin ≤ s.time ∧ T ≤ origin + 1)
    (guards : ∀ t ∈ Ico s.time T, BeforeGuards s (cellOrbitValues θ s t))
    (pending : ∀ d ∈ s.pending, T ≤ d.due) :
    Flow θ s (frozenWorkEnd θ s T) where
  positive := positive
  path := cellOrbitValues θ s
  initial := cellOrbitValues_initial s
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := fun i c => (frozen_values_continuous s i c).continuousOn
  integrable := by
    intro i c
    apply ((frozen_rhs_continuous s i c).intervalIntegrable s.time T).congr_uIoo
    intro t ht
    rw [uIoo_of_lt positive] at ht
    exact (frozen_field s t i (frozen_raw_tail support ⟨ht.1.le, ht.2⟩ i) (error i) (mark i) c).symm
  mark_integrable := by
    intro i p
    have zero t : markAct θ s (cellOrbitValues θ s t) i p = 0 := by
      rcases mark i p with h | h | h
      · simp [markAct, h]
      · simp [markAct, h]
      · simp [markAct, cellOrbitValues, cellBaseValues, not_lt_of_ge h]
    simp_rw [zero]
    exact intervalIntegrable_const
  integral_eq := by
    intro t ht i c
    have equal := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => cellOrbitValues_derivative (θ := θ) s i c v)
      ((frozen_rhs_continuous s i c).intervalIntegrable s.time t)
    rw [cellOrbitValues_initial] at equal
    have integral : (∫ v in s.time..t, field θ s (cellOrbitValues θ s v) v i c) =
        ∫ v in s.time..t, cellOrbitRhs θ s v i c := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro v hv
      exact frozen_field s v i (frozen_raw_tail support ⟨hv.1.le, hv.2.trans_le ht.2⟩ i)
        (error i) (mark i) c
    rw [integral]
    linarith
  guards := guards
  raw_support := support
  pending_urgent := pending

end RecursiveLearning.Native
