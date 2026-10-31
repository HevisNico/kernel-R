import KernelR.HybridLowRecovery
import KernelR.HybridMarkBudget

/-! The actual low-recovery SLOW state protects the next complete sensor cycle. -/
namespace KernelR.Hybrid
open Set

/-- An upper bound on the actual recovery integral rules out a first SLOW
exit throughout the sensor window. No MARK exposure or dose is assumed. -/
theorem Execution.slow_sensor_window {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.main i = .slow) (hq : 7 / 50 ≤ s.x i .q)
    (hb : e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time,
      f.path t i .b ≤ 18001 / 100000)) :
    e.AllStates (fun v => v.time ≤ s.time + 419 / 300 → v.main i = .slow) := by
  rcases e.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact e.allStates_mono (fun v hv _ => hv) h
  · have hbound := hb
    rw [he,Execution.allFlows_append] at hbound
    have hI := segment.accumulatedRecovery_of_upper i (18001 / 100000) hbound.1
    have hguard := exit.slow_departure_guard i hv hw
    have hsol := segment.slow_solution i (segment.allStates_main_flows i .slow hstates)
    rw [hguard] at hsol
    have hlate : s.time + 419 / 300 < w.time := by
      by_contra hn
      have ht : v.time ≤ s.time + 419 / 300 := by
        rw [← exit.time_unchanged]; exact le_of_not_gt hn
      have hImax : segment.accumulatedRecovery i ≤ (18001 / 100000 : ℝ) * (419 / 300) := by
        have hd : v.time - s.time ≤ (419 / 300 : ℝ) := by linarith
        exact hI.trans (mul_le_mul_of_nonneg_left hd (by norm_num))
      have heLower := Real.add_one_le_exp (-segment.accumulatedRecovery i)
      have hePos := Real.exp_pos (-segment.accumulatedRecovery i)
      have hproduct := mul_le_mul_of_nonneg_right hq hePos.le
      nlinarith
    have hsegment : segment.AllStates (fun v => v.time ≤ s.time + 419 / 300 → v.main i = .slow) :=
      segment.allStates_mono (fun v hv _ => hv) hstates
    have hrest : rest.AllStates (fun v => v.time ≤ s.time + 419 / 300 → v.main i = .slow) :=
      rest.allStates_mono (fun v hv ht => False.elim (by have h := hv.1; linarith))
        rest.allStates_time_bounds
    rw [he,Execution.allStates_append]
    exact ⟨hsegment,segment.allStates_final hsegment,hrest⟩

/-- The unconditional one-input budget supplies the recovery bound before
establishing that the MARK gates are open. -/
theorem SensorCycle.protected_window {n θ ε route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hb : PhysicalBox θ ε) (hv : RawValid s) (hs : MarkEntry s i)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    e.AllStates (fun v => v.time ≤ s.time + 419 / 300 → v.main i = .slow) ∧
    e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b ≤ 18001 / 100000) := by
  have hbudget := e.recovery_one_input_budget cycle hb hv hr ho hno
    (fun q _ => ⟨(hs.auxiliary q).1,(hs.auxiliary q).2.2⟩)
  have hend : u.x i .b ≤ 18001 / 100000 := by linarith [hs.recovery.2]
  have hupper := e.recovery_upper_of_end hb i (18001 / 100000) hend
  exact ⟨e.slow_sensor_window i hs.slow hs.charge.1 hupper.2,hupper.2⟩

end KernelR.Hybrid
