import KernelR.HybridCadenceSilent
/-! The three novel-port weak stages at period four, with real carry bounds. -/
namespace KernelR.Hybrid

noncomputable def cadenceWeakInputCap (k : Fin 3) : ℝ := if k = 0 then 1 / 10 else if k = 1 then 3 / 20 else 1 / 5
noncomputable def cadenceWeakDriveCap (k : Fin 3) : ℝ := if k = 0 then 1 / 3 else if k = 1 then 3 / 5 else 7 / 6
noncomputable def cadenceWeakOutputCap (k : Fin 3) : ℝ := if k = 0 then 3 / 20 else if k = 1 then 1 / 5 else 3 / 10

theorem cadenceWeak_raw_gain_upper (k : Fin 3) {z : ℝ}
    (hz : z ≤ Real.log (3 / 10) + (3 / 5) * (k.val : ℝ) + 1 / 100000 + 11 / 125) :
    Real.exp z ≤ cadenceWeakDriveCap k := by
  fin_cases k
  · have he : Real.exp (9 / 100 : ℝ) ≤ 10 / 9 := by
      have h := Real.exp_bound (x := (9 / 100 : ℝ)) (n := 2) (by norm_num) (by norm_num)
      norm_num [Finset.sum_range_succ] at h
      linarith [(abs_sub_le_iff.mp h).1]
    have h := Real.exp_le_exp.mpr (show z ≤ Real.log (3 / 10) + 9 / 100 by norm_num at hz; linarith)
    rw [Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 3 / 10)] at h
    norm_num [cadenceWeakDriveCap]
    linarith
  · have h := Real.exp_le_exp.mpr (show z ≤ Real.log (3 / 10) + Real.log 2 by
      norm_num at hz
      linarith [Real.log_two_gt_d9])
    rw [Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 3 / 10),
      Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    norm_num [cadenceWeakDriveCap]
    linarith
  · have h := low_gain_tail_upper (z := z) (by norm_num at hz; linarith)
    simpa [cadenceWeakDriveCap] using h

theorem cadenceWeak_below_fast_nominal (k : Fin 3) {z : ℝ}
    (hz : z ≤ Real.log (3 / 10) + (3 / 5) * (k.val : ℝ) + 1 / 100000) :
    z ≤ Real.log (6 / 5) + 1 / 1000 := by
  have hlog : Real.log (6 / 5 : ℝ) = Real.log (3 / 10) + Real.log 4 := by
    rw [← Real.log_mul (by norm_num : (3 / 10 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    norm_num
  have hk : (k.val : ℝ) ≤ 2 := by exact_mod_cast (show k.val ≤ 2 by omega)
  rw [hlog]
  linarith [KernelR.log_four_bounds.1]

/-- Three instantiated physical silent cases retain their successively larger
charge caps, instead of reusing the period-eight resting section. -/
theorem Execution.cadence_weak_stage {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (k : Fin 3)
    (hs : CadenceReadyCoordinates s i (cadenceWeakInputCap k))
    (hz : s.x i (.z p) ≤ Real.log (3 / 10) + (3 / 5) * (k.val : ℝ) + 1 / 100000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 4 ≤ u.time) :
    Nonempty (CadenceSilentPulse e i p (cadenceWeakOutputCap k)) := by
  apply e.cadence_silent_pulse hb hf hv i p (cadenceWeakInputCap k) (cadenceWeakDriveCap k)
    (cadenceWeakOutputCap k) hs
  · fin_cases k <;> norm_num [cadenceWeakInputCap]
  · fin_cases k <;> norm_num [cadenceWeakDriveCap]
  · fin_cases k <;> norm_num [cadenceWeakInputCap,cadenceWeakDriveCap]
  · fin_cases k <;> norm_num [cadenceWeakInputCap,cadenceWeakDriveCap,cadenceWeakOutputCap]
  · exact cadenceWeak_below_fast_nominal k hz
  · intro z hz'
    exact cadenceWeak_raw_gain_upper k (by linarith)
  · exact hr
  · exact ho
  · exact hno
  · exact ht

end KernelR.Hybrid
