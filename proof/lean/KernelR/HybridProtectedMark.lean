import KernelR.HybridProtectedWindow

/-! Full protected MARK and zero ERROR doses derived from the actual sensor cycle. -/
namespace KernelR.Hybrid
open Set

theorem SensorCycle.error_zero_of_protected {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hv : RawValid s)
    (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p)
    (hm : cycle.phases.errorPhase.span.AllStates (fun v => v.main i ≠ .ready)) :
    e.ledger.error i p = 0 ∧ u.x i (.z p) = s.x i (.z p) := by
  let er := cycle.phases.errorPhase
  have herr := er.span.gain_constant_protected_states i p hm
  have hafter : er.afterExit.x i (.z p) = s.x i (.z p) := by
    rw [er.exit.physical_continuous,herr,cycle.error_initial_gain]
  have hquiet := cycle.error_rest_ready hv hr hno
  have hgain := (er.rest.gain_constant_aux i p .ready (by decide)
    (er.rest.allStates_aux_flows i p .ready hquiet)).1
  have hu := hgain.trans hafter
  exact ⟨by have h := e.gain_balance i p; linarith,hu⟩

theorem SensorCycle.full_protected_mark {n θ ε route born s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (past : Execution θ route born s) (hborn : BirthState born)
    (hb : PhysicalBox θ ε) (hs : MarkEntry s i)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    e.ledger.mark i p = 1 / 10 ∧ e.ledger.error i p = 0 ∧ u.x i (.z p) = s.x i (.z p) := by
  let st := cycle.trigger
  let mk := cycle.phases.markPhase
  let er := cycle.phases.errorPhase
  have hv := past.raw_valid hborn.raw_valid
  have hw := cycle.protected_window hb hv hs hr ho hno
  have hm : mk.span.AllStates (fun v => v.main i ≠ .ready) := by
    have hstates := cycle.mark_states hw.1
    have hend : mk.beforeExit.time < s.time + 1 / 20 := by
      rw [← mk.exit.time_unchanged]; exact cycle.mark_ends_early hb
    refine mk.span.allStates_mono ?_ (mk.span.allStates_and hstates mk.span.allStates_time_bounds)
    intro v h
    have hmode := h.1 (by have ht := h.2.2; linarith)
    rw [hmode]; decide
  have hc : mk.span.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b < 11 / 10) := by
    refine mk.span.allFlows_mono ?_ (cycle.mark_flows hw.2)
    intro v w f hf t ht
    linarith [hf t ht]
  let pastMark := past.append (st.span.append (.cons (.jump st.entry) (.nil _)))
  have hexposed := mk.span.mark_exposed_of_upper pastMark hborn hb i p mk.flows hm hc
  have hfull := mk.span.full_mark_of_open_endpoints i p hexposed st.charge
    (by simpa only [protectedFloor] using mk.charge)
  have herror : er.span.AllStates (fun v => v.main i ≠ .ready) := by
    have hstates := (cycle.error_states hw.1).1
    have hend : er.beforeExit.time < s.time + 419 / 300 := by
      rw [← er.exit.time_unchanged]; exact cycle.ready_deadline
    refine er.span.allStates_mono ?_ (er.span.allStates_and hstates er.span.allStates_time_bounds)
    intro v h
    have hmode := h.1 (by have ht := h.2.2; linarith)
    rw [hmode]; decide
  exact ⟨(cycle.mark_ledger_eq_phase hv hr (hno p)).trans hfull,
    cycle.error_zero_of_protected hv hr (hno p) herror⟩

end KernelR.Hybrid
