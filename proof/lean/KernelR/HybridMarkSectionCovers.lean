import KernelR.HybridDoseCountingTools
import KernelR.HybridSectionStates
import KernelR.HybridProtectedMark
import KernelR.HybridSlowMarkWindow

/-! Actual one-input MARK covers. The counted section is reconstructed from
the sensor's real entry and departure jumps. Outside that section the cover is
inactive because the auxiliary is READY, SILENT or ERROR, never because an
endpoint ledger happened to vanish. -/
namespace KernelR.Hybrid
open Set

theorem SensorCycle.mark_cover_of_exposed {n θ route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (hv : RawValid s) (hr : s.raw i p = some s.time)
    (hno : NoArrivalAt e i p)
    (exposed : cycle.phases.markPhase.span.MarkExposed i p) :
    ∃ cover : MarkSectionCover i p e, cover.count = 1 := by
  let st := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  let er := cycle.phases.errorPhase
  let tailCover := er.rest.markCover_of_inactive i p
    (er.rest.mark_inactive_of_auxFlows i p .ready (by decide)
      (er.rest.allStates_aux_flows i p .ready (cycle.error_rest_ready hv hr hno)))
  let errorSpanCover := er.span.markCover_of_inactive i p
    (er.span.mark_inactive_of_auxFlows i p .error (by decide) er.flows)
  let errorCover : MarkSectionCover i p si.rest := by
    rw [er.reconstruct]
    exact errorSpanCover.append (.inactive (.jump er.exit) er.rest trivial tailCover)
  let silentSpanCover := si.span.markCover_of_inactive i p
    (si.span.mark_inactive_of_auxFlows i p .silent (by decide) si.flows)
  let silentCover : MarkSectionCover i p mk.rest := by
    rw [si.reconstruct]
    exact silentSpanCover.append (.inactive (.jump si.exit) si.rest trivial errorCover)
  have phase : mk.span.AllStates (fun v => v.aux i p = .mark) :=
    mk.span.aux_states_of_protected_flows i p .mark (by decide)
      st.mark_after mk.mode_before mk.flows
  let fullCover : MarkSectionCover i p (.cons (.jump st.entry) st.rest) := by
    rw [mk.reconstruct]
    exact .fullPhase st.entry mk.span mk.exit mk.rest
      (by rw [st.ready_before]; decide) st.mark_after mk.mode_before
      (by rw [mk.mode_after]; decide) phase exposed silentCover
  let prefixCover := st.span.markCover_of_inactive i p
    (st.span.mark_inactive_of_auxFlows i p .ready (by decide) st.flows)
  let cover : MarkSectionCover i p e := by
    rw [st.reconstruct]
    exact prefixCover.append fullCover
  refine ⟨cover, ?_⟩
  have dose : e.ledger.mark i p = 1 / 10 :=
    (cycle.mark_ledger_eq_phase hv hr hno).trans
      (mk.span.full_mark_of_open_endpoints i p exposed st.charge
        (by simpa only [protectedFloor] using mk.charge))
  have equality := cover.ledger_eq
  rw [dose] at equality
  have count : (cover.count : ℝ) = 1 := by linarith
  exact_mod_cast count

/-- Exposure is derived from the physical one-input window and reserve/cap
bounds. It is not a new premise attached to the protected protocol. -/
theorem SensorCycle.protected_mark_exposed {n θ ε route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s)
    (hv : RawValid s) (hs : MarkEntry s i)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    cycle.phases.markPhase.span.MarkExposed i p := by
  let st := cycle.trigger
  let mk := cycle.phases.markPhase
  have window := cycle.protected_window hb hv hs hr ho hno
  have main : mk.span.AllStates (fun v => v.main i ≠ .ready) := by
    have states := cycle.mark_states window.1
    have terminal : mk.beforeExit.time < s.time + 1 / 20 := by
      rw [← mk.exit.time_unchanged]
      exact cycle.mark_ends_early hb
    refine mk.span.allStates_mono ?_ (mk.span.allStates_and states mk.span.allStates_time_bounds)
    intro v h
    have mode := h.1 (by have ht := h.2.2; linarith)
    rw [mode]
    decide
  have cap : mk.span.AllFlows (fun {v w} f =>
      ∀ t ∈ Icc v.time w.time, f.path t i .b < 11 / 10) := by
    refine mk.span.allFlows_mono ?_ (cycle.mark_flows window.2)
    intro v w f bound t ht
    linarith [bound t ht]
  let past := st.span.append (.cons (.jump st.entry) (.nil _))
  exact mk.span.mark_exposed_of_invariant hb (past.physical_invariant hb hf)
    i p mk.flows main cap

/-- The physical protected-input hypotheses construct the whole sensor-cycle
cover, with exactly one complete protected MARK. -/
theorem SensorCycle.protected_mark_cover {n θ ε route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s)
    (hv : RawValid s) (hs : MarkEntry s i)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    ∃ cover : MarkSectionCover i p e, cover.count = 1 :=
  cycle.mark_cover_of_exposed hv hr (hno p)
    (cycle.protected_mark_exposed hb hf hv hs hr ho hno)

/-- The cadence cases only need protection through MARK. Their later READY
return may expose ERROR; it does not alter this full MARK cover. -/
theorem ShortMarkPulse.mark_section_cover {n θ ε route s u i p}
    {e : @Execution n θ route s u} (pulse : ShortMarkPulse e i p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s)
    (hv : RawValid s) (hr : s.raw i p = some s.time)
    (hno : NoArrivalAt e i p)
    (headroom : s.x i .b + 1 / 10 < 11 / 10) :
    ∃ cover : MarkSectionCover i p e, cover.count = 1 := by
  let cycle := pulse.cycle
  let st := cycle.trigger
  let mk := cycle.phases.markPhase
  have upper := e.recovery_upper_of_end hb i (s.x i .b + 1 / 10)
    (by rw [pulse.recovery_gain])
  have main : mk.span.AllStates (fun v => v.main i ≠ .ready) := by
    have states := cycle.mark_states pulse.slow_window
    have terminal : mk.beforeExit.time < s.time + 1 / 20 := by
      rw [← mk.exit.time_unchanged]
      exact cycle.mark_ends_early hb
    refine mk.span.allStates_mono ?_ (mk.span.allStates_and states mk.span.allStates_time_bounds)
    intro v h
    have mode := h.1 (by have ht := h.2.2; linarith)
    rw [mode]
    decide
  have cap : mk.span.AllFlows (fun {v w} f =>
      ∀ t ∈ Icc v.time w.time, f.path t i .b < 11 / 10) := by
    refine mk.span.allFlows_mono ?_ (cycle.mark_flows upper.2)
    intro v w f bound t ht
    exact (bound t ht).trans_lt headroom
  let past := st.span.append (.cons (.jump st.entry) (.nil _))
  have exposed := mk.span.mark_exposed_of_invariant hb (past.physical_invariant hb hf)
    i p mk.flows main cap
  exact cycle.mark_cover_of_exposed hv hr hno exposed

#print axioms SensorCycle.protected_mark_cover
#print axioms ShortMarkPulse.mark_section_cover

end KernelR.Hybrid
