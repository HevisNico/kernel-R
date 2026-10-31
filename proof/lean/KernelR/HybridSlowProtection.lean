import KernelR.HybridSingleOutput

/-! Minimum physical protection durations and zero learned-input ERROR dose. -/
namespace KernelR.Hybrid
open Set MeasureTheory

theorem Flow.recovery_cap_on {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hs : s.x i .b ≤ 11 / 10) : ∀ t ∈ Icc s.time u.time, f.path t i .b ≤ 11 / 10 := by
  intro t ht
  rcases ht.1.eq_or_lt with heq | hlt
  · simpa only [← heq,f.initial] using hs
  · exact (f.prefix hlt ht.2).recovery_cap i hs

theorem Flow.accumulatedRecovery_upper {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hs : s.x i .b ≤ 11 / 10) : f.accumulatedRecovery i ≤ (11 / 10) * (u.time - s.time) := by
  have h : (∫ t in s.time..u.time, f.path t i .b) ≤ ∫ _t in s.time..u.time, (11 / 10 : ℝ) :=
    intervalIntegral.integral_mono_on f.positive.le
      ((f.continuous i .b).intervalIntegrable_of_Icc f.positive.le) intervalIntegrable_const
      (f.recovery_cap_on i hs)
  simpa only [Flow.accumulatedRecovery,intervalIntegral.integral_const,smul_eq_mul,mul_comm] using h

theorem Execution.accumulatedRecovery_upper {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.x i .b ≤ 11 / 10) : e.accumulatedRecovery i ≤ (11 / 10) * (u.time - s.time) := by
  induction e with
  | nil => simp [accumulatedRecovery]
  | @cons s v u move rest ih => cases move with
    | flow f =>
      have hf := f.accumulatedRecovery_upper i hs
      have hrest := ih (f.recovery_cap i hs)
      simp only [accumulatedRecovery]
      linarith
    | jump j => simpa only [accumulatedRecovery,j.time_unchanged] using ih (by simpa only [j.physical_continuous] using hs)

theorem Execution.slow_minimum_duration {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .slow) (hs : s.x i .q = 1 / 4) (hu : u.x i .q = 1 / 10)
    (hb : s.x i .b ≤ 11 / 10) : 4 / 5 < u.time - s.time := by
  have he := e.slow_solution i hm
  rw [hs,hu] at he
  have hex : Real.exp (-e.accumulatedRecovery i) = (2 / 5 : ℝ) := by linarith
  have href : Real.exp (-Real.log (5 / 2)) = (2 / 5 : ℝ) := by
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]; norm_num
  have hi := neg_injective (Real.exp_injective (hex.trans href.symm))
  have hbnd := e.accumulatedRecovery_upper i hb
  rw [hi] at hbnd
  linarith [KernelR.log_recovery_bounds.1]

theorem Execution.allStates_time_bounds {n θ route s u} (e : @Execution n θ route s u) :
    e.AllStates (fun v => s.time ≤ v.time ∧ v.time ≤ u.time) := by
  induction e with
  | nil => exact ⟨le_rfl,le_rfl⟩
  | @cons s v u move rest ih =>
    refine ⟨⟨le_rfl,move.time_monotone.trans rest.time_monotone⟩,?_⟩
    exact rest.allStates_mono (fun w hw => ⟨move.time_monotone.trans hw.1,hw.2⟩) ih

theorem Execution.allStates_recovery_cap {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.x i .b ≤ 11 / 10) : e.AllStates (fun v => v.x i .b ≤ 11 / 10) := by
  induction e with
  | nil => exact hs
  | cons move rest ih =>
    refine ⟨hs,ih ?_⟩
    cases move with
    | flow f => exact f.recovery_cap i hs
    | jump j => simpa only [j.physical_continuous] using hs

theorem Execution.slow_protected_until {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.main i = .slow) (hq : s.x i .q = 1 / 4) (hb : s.x i .b ≤ 11 / 10) :
    e.AllStates (fun v => v.time ≤ s.time + 4 / 5 → v.main i ≠ .ready) := by
  rcases e.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact e.allStates_mono (fun v hv _ => by rw [hv]; decide) h
  · have hg := exit.slow_departure_guard i hv hw
    have hd := segment.slow_minimum_duration i (segment.allStates_main_flows i .slow hstates) hq hg hb
    have hwtime : s.time + 4 / 5 < w.time := by rw [exit.time_unchanged]; linarith
    have hsegment : segment.AllStates (fun v => v.time ≤ s.time + 4 / 5 → v.main i ≠ .ready) := segment.allStates_mono
      (fun v hv (_ : v.time ≤ s.time + 4 / 5) => by rw [hv]; decide) hstates
    have hrest : rest.AllStates (fun v => v.time ≤ s.time + 4 / 5 → v.main i ≠ .ready) := rest.allStates_mono
      (fun v hv (ht : v.time ≤ s.time + 4 / 5) => False.elim (by have h := hv.1; linarith))
      rest.allStates_time_bounds
    rw [he,Execution.allStates_append]
    exact ⟨hsegment,segment.allStates_final hsegment,hrest⟩

theorem Execution.fast_protected_until {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.main i = .fast) (hq : s.x i .q = 1) (hb : s.x i .b ≤ 11 / 10) :
    e.AllStates (fun v => v.time ≤ s.time + 9 / 5 → v.main i ≠ .ready) := by
  rcases e.first_state_change (fun v => v.main i) .fast
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact e.allStates_mono (fun v hv _ => by rw [hv]; decide) h
  · have hg := exit.fast_departure_guard i hv hw
    have hd := segment.fast_duration i (segment.allStates_main_flows i .fast hstates) hq hg.1
    have hwtime : w.time = s.time + 1 := by rw [exit.time_unchanged]; linarith
    have hqslow : w.x i .q = 1 / 4 := by rw [exit.physical_continuous,hg.1]
    have hbslow : w.x i .b ≤ 11 / 10 := by rw [exit.physical_continuous]; exact segment.recovery_cap i hb
    have hslow := rest.slow_protected_until i hg.2 hqslow hbslow
    have hrest : rest.AllStates (fun v => v.time ≤ s.time + 9 / 5 → v.main i ≠ .ready) := rest.allStates_mono (fun v hv (ht : v.time ≤ s.time + 9 / 5) =>
      hv (by rw [hwtime]; linarith)) hslow
    have hsegment : segment.AllStates (fun v => v.time ≤ s.time + 9 / 5 → v.main i ≠ .ready) := segment.allStates_mono
      (fun v hv (_ : v.time ≤ s.time + 9 / 5) => by rw [hv]; decide) hstates
    rw [he,Execution.allStates_append]
    exact ⟨hsegment,segment.allStates_final hsegment,hrest⟩

/-- The minimum protected duration is already enough to cover the whole
sensor ERROR window; no nominal SLOW return time is assumed. -/
theorem MainTrigger.sensor_window_protected {n θ route s u i} {e : @Execution n θ route s u}
    (tr : MainTrigger e i) (hb : s.x i .b ≤ 11 / 10) :
    e.AllStates (fun v => s.time + 99 / 100 ≤ v.time → v.time ≤ s.time + 419 / 300 → v.main i ≠ .ready) := by
  have hcap : tr.afterFire.x i .b ≤ 11 / 10 := by
    rw [tr.entry.physical_continuous]; exact tr.span.recovery_cap i hb
  have hprotected := tr.rest.fast_protected_until i tr.fast_after tr.charge hcap
  have hrest : tr.rest.AllStates (fun v => s.time + 99 / 100 ≤ v.time → v.time ≤ s.time + 419 / 300 → v.main i ≠ .ready) := tr.rest.allStates_mono (fun v hv _ (ht : v.time ≤ s.time + 419 / 300) =>
    hv (by linarith [tr.early])) hprotected
  have hdeadline : tr.beforeFire.time < s.time + 9 / 10 := by
    simpa only [tr.entry.time_unchanged] using tr.deadline
  have hspan : tr.span.AllStates (fun v => s.time + 99 / 100 ≤ v.time → v.time ≤ s.time + 419 / 300 → v.main i ≠ .ready) := tr.span.allStates_mono
    (fun v hv (ht : s.time + 99 / 100 ≤ v.time) _ => False.elim (by have h := hv.2; linarith))
    tr.span.allStates_time_bounds
  rw [tr.reconstruct,Execution.allStates_append]
  exact ⟨hspan,tr.span.allStates_final hspan,hrest⟩

theorem Execution.gain_constant_protected_states {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (hs : e.AllStates (fun v => v.main i ≠ .ready)) :
    u.x i (.z p) = s.x i (.z p) := by
  induction e with
  | nil => rfl
  | cons move rest ih => cases move with
    | flow f =>
      have hf := f.gain_constant_when_protected i p hs.1 _ ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hf
      exact (ih hs.2).trans hf
    | jump j => simpa only [j.physical_continuous] using ih hs.2

theorem SensorCycle.error_protected_by_trigger {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (tr : MainTrigger e i) (hb : s.x i .b ≤ 11 / 10) :
    cycle.phases.errorPhase.span.AllStates (fun v => v.main i ≠ .ready) := by
  let er := cycle.phases.errorPhase
  have hmain := (cycle.error_states (tr.sensor_window_protected hb)).1
  have hupper : er.beforeExit.time < s.time + 419 / 300 := by
    rw [← er.exit.time_unchanged]; exact cycle.ready_deadline
  refine er.span.allStates_mono ?_ (er.span.allStates_and hmain er.span.allStates_time_bounds)
  intro v h
  exact h.1 (by have ht := h.2.1; linarith [cycle.error_starts_late])
    (by have ht := h.2.2; linarith)

theorem SensorCycle.error_zero_of_protected {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hv₀ : RawValid s)
    (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p)
    (hm : cycle.phases.errorPhase.span.AllStates (fun v => v.main i ≠ .ready)) :
    e.ledger.error i p = 0 ∧ u.x i (.z p) = s.x i (.z p) := by
  let er := cycle.phases.errorPhase
  have herr := er.span.gain_constant_protected_states i p hm
  have hafter : er.afterExit.x i (.z p) = s.x i (.z p) := by
    rw [er.exit.physical_continuous,herr,cycle.error_initial_gain]
  have hvalid := e.allStates_raw_valid hv₀
  have hallowed := e.raw_allowed_states i p s.time (Or.inr hr) hno
  have hv := er.rest.allStates_initial (cycle.error_states hvalid).2
  have ha := er.rest.allStates_initial (cycle.error_states hallowed).2
  have hraw : er.afterExit.raw i p = none := by
    rcases ha with h | h
    · exact h
    · exact False.elim (not_lt_of_ge (hv i p s.time h).2 cycle.ready_after_raw)
  have hquiet := er.rest.aux_ready_without_input i p cycle.phases.ready_mode
    (by simpa only [protectedFloor] using er.after_charge.le) hraw (cycle.error_rest_no_arrival p hno)
  have hgain := (er.rest.gain_constant_aux i p .ready (by decide)
    (er.rest.allStates_aux_flows i p .ready hquiet)).1
  have hu := hgain.trans hafter
  refine ⟨?_,hu⟩
  have hb := e.gain_balance i p
  linarith

theorem SensorCycle.total_error_zero_of_trigger {n θ route born s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p) (tr : MainTrigger e i)
    (past : Execution θ route born s) (hborn : BirthState born)
    (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p) :
    e.ledger.error i p = 0 ∧ u.x i (.z p) = s.x i (.z p) := by
  have hb : s.x i .b ≤ 11 / 10 := past.recovery_cap i (by linarith [(hborn.2.2 i).2.2.1.2])
  exact cycle.error_zero_of_protected (past.raw_valid hborn.raw_valid) hr hno
    (cycle.error_protected_by_trigger tr hb)

end KernelR.Hybrid
