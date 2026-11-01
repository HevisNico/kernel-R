import KernelR.HybridMarkRecoveryIntegral

namespace KernelR.Hybrid
open Set

/-- A short SLOW window needs neither a low birth recovery nor protection
through ERROR. The cap suffices for the first 1/20 time unit. -/
theorem Execution.slow_short_mark_window {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n)
    (hs : s.main i = .slow) (hq : 11 / 100 ≤ s.x i .q)
    (hb : s.x i .b ≤ 11 / 10) :
    e.AllStates (fun v => v.time ≤ s.time + 1 / 20 → v.main i = .slow) := by
  rcases e.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact e.allStates_mono (fun v hv _ => hv) h
  · have hI := segment.accumulatedRecovery_upper i hb
    have hsol := segment.slow_solution i (segment.allStates_main_flows i .slow hstates)
    have hguard := exit.slow_departure_guard i hv hw
    have hlate : s.time + 1 / 20 < w.time := by
      by_contra hn
      have htime : v.time ≤ s.time + 1 / 20 := by
        rw [← exit.time_unchanged]
        exact le_of_not_gt hn
      have hImax : segment.accumulatedRecovery i ≤ (11 / 200 : ℝ) := by nlinarith
      have hexp := Real.add_one_le_exp (-segment.accumulatedRecovery i)
      have hproduct := mul_le_mul_of_nonneg_right hq (Real.exp_pos (-segment.accumulatedRecovery i)).le
      rw [hguard] at hsol
      nlinarith
    have hseg : segment.AllStates (fun v => v.time ≤ s.time + 1 / 20 → v.main i = .slow) :=
      segment.allStates_mono (fun v hv _ => hv) hstates
    have hrest : rest.AllStates (fun v => v.time ≤ s.time + 1 / 20 → v.main i = .slow) :=
      rest.allStates_mono (fun v hv ht => False.elim (by have h := hv.1; linarith))
        rest.allStates_time_bounds
    rw [he,Execution.allStates_append]
    exact ⟨hseg,segment.allStates_final hseg,hrest⟩

structure ShortMarkPulse {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) where
  cycle : SensorCycle e i p
  slow_window : e.AllStates (fun v => v.time ≤ s.time + 1 / 20 → v.main i = .slow)
  mark_dose : e.ledger.mark i p = 1 / 10
  mark_other : ∀ q, q ≠ p → e.ledger.mark i q = 0
  recovery_gain : u.x i .b = s.x i .b + 1 / 10
  mark_integral : cycle.phases.markPhase.span.accumulatedRecovery i =
    (cycle.trigger.afterMark.x i .b + 1 / 2) *
      Cadence.markDuration ((θ i).lm p) - 1 / (10 * (θ i).lm p)

theorem Execution.aux_modes_as_all_flows {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port) (mode : AuxMode)
    (h : e.AuxFlows i p mode) : e.AllFlows (fun {v _w} _ => v.aux i p = mode) := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ⟨h.1,ih h.2⟩
    | jump j => exact ih h

/-- The main is protected only through MARK. ERROR and the later READY return
remain available to the combined cadence case. -/
theorem Execution.short_mark_pulse_of_invariant {n θ ε route s u}
    (e : @Execution n θ route s u) (hb : PhysicalBox θ ε)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (i : Fin n) (p : Port)
    (hs : s.main i = .slow) (hq : 11 / 100 ≤ s.x i .q)
    (hbrecovery : s.x i .b ≤ 3 / 10)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 419 / 300 ≤ u.time) :
    Nonempty (ShortMarkPulse e i p) := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hf.region i p (ha p).1 hr (ha p).2 ht
  have hwindow := e.slow_short_mark_window i hs hq (by linarith)
  have hbudget := e.recovery_one_input_budget cycle hb hv hr ho hno
    (fun q _ => ⟨(ha q).1,(ha q).2.2⟩)
  have hupper := e.recovery_upper_of_end hb i (s.x i .b + 1 / 10) hbudget
  let mk := cycle.phases.markPhase
  have hmain : mk.span.AllStates (fun v => v.main i ≠ .ready) := by
    have hstates := cycle.mark_states hwindow
    have hend : mk.beforeExit.time < s.time + 1 / 20 := by
      rw [← mk.exit.time_unchanged]
      exact cycle.mark_ends_early hb
    refine mk.span.allStates_mono ?_ (mk.span.allStates_and hstates mk.span.allStates_time_bounds)
    intro v h
    have hmode := h.1 (by have ht := h.2.2; linarith)
    rw [hmode]; decide
  have hcap : mk.span.AllFlows (fun {v w} f =>
      ∀ t ∈ Icc v.time w.time, f.path t i .b < 11 / 10) := by
    refine mk.span.allFlows_mono ?_ (cycle.mark_flows hupper.2)
    intro v w f hh t ht
    linarith [hh t ht]
  have hquiet : ∀ q, q ≠ p → e.AllStates (fun v => v.aux i q = .ready) := by
    intro q hq
    exact e.aux_ready_without_input_band i q (ha q).1 (ha q).2.2 (ho q hq) (hno q)
  have hclosed : e.OtherMarkClosed i p := by
    apply e.allFlows_forall (fun q {v _w} _ => q ≠ p → v.aux i q ≠ .mark)
    intro q
    by_cases hq : q = p
    · subst q
      exact e.allFlows_mono (fun f _ h => False.elim (h rfl)) e.allFlows_time_bounds
    · have hflows := e.allStates_aux_flows i q .ready (hquiet q hq)
      exact e.allFlows_mono (fun f hh _ => by rw [hh]; decide)
        (e.aux_modes_as_all_flows i q .ready hflows)
  have hmark := cycle.mark_recovery_integral_of_invariant hb hf hmain hcap (cycle.mark_flows hclosed)
  have hd : e.ledger.mark i p = 1 / 10 :=
    (cycle.mark_ledger_eq_phase hv hr (hno p)).trans hmark.1
  have hother : ∀ q, q ≠ p → e.ledger.mark i q = 0 := by
    intro q hq
    exact e.mark_zero_aux i q .ready (by decide)
      (e.allStates_aux_flows i q .ready (hquiet q hq))
  have hbgain : u.x i .b = s.x i .b + 1 / 10 := by
    rw [e.recovery_balance i,e.recovery_sum_marks i,
      Finset.sum_eq_single p (fun q _ hq => hother q hq) (by simp),hd]
  exact ⟨⟨cycle,hwindow,hd,hother,hbgain,hmark.2.2⟩⟩

end KernelR.Hybrid
