import KernelR.HybridPreparedCalendar
/-! Positive READY residual charge is retained in the first physical latency. -/
namespace KernelR.Hybrid
open Set

/-- A READY trace that never emits cannot leave READY, since every physical
READY departure contributes an actual fire event. -/
theorem Execution.ready_states_of_no_emissions {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.main i = .ready) (he : e.emissionTimes i = []) :
    e.AllStates (fun v => v.main i = .ready) := by
  rcases e.first_state_change (fun v => v.main i) .ready
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,hr,hstates,hv,hw⟩
  · exact h
  · have hm : v.time ∈ e.emissionTimes i := by
      rw [hr,Execution.emissionTimes_append,Execution.emissionTimes_cons]
      simp [Move.ledger,exit.ready_main_departure_emission i hv hw]
    rw [he] at hm
    contradiction

/-- Nonnegative raw drive cannot push a READY charge below the exact rest
value when it starts at or above that value. -/
theorem Execution.ready_charge_ge_rest {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .ready) (hq : 1 / 10 ≤ s.x i .q) : 1 / 10 ≤ u.x i .q := by
  have hd : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      (0 : ℝ) * a * Real.exp (-a * (t - s.time)) ≤ tailDrive v (f.path t) i t) := by
    apply e.allFlows_of
    intro v w f t ht
    simp only [zero_mul]
    unfold tailDrive
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (Real.exp_pos _).le (rawTail_nonnegative v i p t))
  have hlo := e.ready_drive_lower i hm (s.x i .q) 0 s.time (by rw [readyPulse_initial]) hd
  simp only [readyPulse,zero_mul,add_zero] at hlo
  have hc : 0 ≤ (s.x i .q - 1 / 10) * Real.exp (-(1 / 2) * (u.time - s.time)) :=
    mul_nonneg (sub_nonneg.mpr hq) (Real.exp_pos _).le
  linarith

/-- The first learned output after silent learning may be advanced by its
positive residual. It is never delayed beyond the same-gain rest reference. -/
theorem LearnedPulse.latency_le_rest {n θ ε route s u i} {e : @Execution n θ route s u}
    (pulse : LearnedPulse e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (p : Port) (hs : PreparedSection s i) (hq : 1 / 10 ≤ s.x i .q)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) :
    pulse.trigger.beforeFire.time - s.time ≤ restLatency (Real.exp (s.x i (.z p))) := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p (hs.auxiliary p).1 hr (hs.auxiliary p).2 (by linarith)
  have hroot := pulse.trigger.firing_equation cycle hr ho hno
  have hshift : readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) 0
      (pulse.trigger.beforeFire.time - s.time) = 1 := by
    simpa only [readyPulse,sub_zero] using hroot
  have hlo : s.time + 3 / 10 < pulse.trigger.beforeFire.time := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.early
  have hhi : pulse.trigger.beforeFire.time < s.time + 9 / 10 := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.deadline
  have hsref := restLatency_spec hg
  exact first_firing_le_rest_reference hq hg.1
    ⟨by linarith,by linarith⟩ ⟨by linarith [hsref.1],by linarith [hsref.2.1]⟩ hshift hsref.2.2

end KernelR.Hybrid
