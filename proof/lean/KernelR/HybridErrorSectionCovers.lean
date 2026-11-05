import KernelR.HybridDoseCountingTools
import KernelR.HybridSectionStates
import KernelR.HybridCadenceMixedPulse

/-! Actual complete ERROR covers extracted from sensor cycles. The cover is
constructed from the recorded trigger, MARK/SILENT spans, ERROR entry and
exit, and the structurally inactive READY tail. No ledger equality is used
to supply the existence of a cover. -/
namespace KernelR.Hybrid

/-- The physical exposure proof used by the dose identity, retained as an
explicit certificate on the actual ERROR span. -/
theorem SensorCycle.error_exposed_of_ready_error {n θ ε route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s)
    (hm : cycle.phases.errorPhase.span.AllStates (fun v => v.main i = .ready))
    (hh : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p)) :
    cycle.phases.errorPhase.span.ErrorExposed i p := by
  let tr := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  let er := cycle.phases.errorPhase
  let pastMark := tr.span.append (.cons (.jump tr.entry) (.nil _))
  let pastSilent := pastMark.append (mk.span.append (.cons (.jump mk.exit) (.nil _)))
  let pastError := pastSilent.append (si.span.append (.cons (.jump si.exit) (.nil _)))
  have hmain := er.span.allStates_main_flows i .ready hm
  have hh' : si.afterExit.x i (.z p) + 8 * (si.afterExit.x i (.m p) - 1 / 40) <
      Real.log ((θ i).cap p) := by
    rw [cycle.error_initial_gain, si.after_charge]
    norm_num only [protectedFloor]
    linarith
  exact er.span.error_exposed_of_invariant hb (pastError.physical_invariant hb hf)
    i p er.flows hmain hh'

/-- A sensor cycle whose actual ERROR span is fully exposed has a cover of
the entire execution, including the inactive moves before and after ERROR. -/
theorem SensorCycle.error_cover_of_exposed {n θ route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (exposed : cycle.phases.errorPhase.span.ErrorExposed i p)
    (rest_ready : cycle.phases.errorPhase.rest.AllStates (fun v => v.aux i p = .ready)) :
    Nonempty (ErrorSectionCover i p e) := by
  let tr := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  let er := cycle.phases.errorPhase
  have phase := er.span.aux_states_of_protected_flows i p .error (by decide)
    si.mode_after er.mode_before er.flows
  let tail := er.rest.errorCover_of_inactive i p
    (er.rest.error_inactive_of_auxFlows i p .ready (by decide)
      (er.rest.allStates_aux_flows i p .ready rest_ready))
  have errorPart : ErrorSectionCover i p (.cons (.jump si.exit) si.rest) := by
    rw [er.reconstruct]
    exact .fullPhase si.exit er.span er.exit er.rest
      (by rw [si.mode_before]; decide) si.mode_after er.mode_before
      (by rw [er.mode_after]; decide) phase exposed tail
  have silentPart : ErrorSectionCover i p mk.rest := by
    rw [si.reconstruct]
    exact (si.span.errorCover_of_inactive i p
      (si.span.error_inactive_of_auxFlows i p .silent (by decide) si.flows)).append errorPart
  have markPart : ErrorSectionCover i p tr.rest := by
    rw [mk.reconstruct]
    exact (mk.span.errorCover_of_inactive i p
      (mk.span.error_inactive_of_auxFlows i p .mark (by decide) mk.flows)).append
        (.inactive (.jump mk.exit) mk.rest trivial silentPart)
  rw [tr.reconstruct]
  exact ⟨(tr.span.errorCover_of_inactive i p
    (tr.span.error_inactive_of_auxFlows i p .ready (by decide) tr.flows)).append
      (.inactive (.jump tr.entry) tr.rest trivial markPart)⟩

/-- The actual cycle has one complete ERROR section under precisely the
physical hypotheses of `total_error_of_ready_error`. The count is obtained
only after constructing its actual-trace cover. -/
theorem SensorCycle.error_cover_of_ready_error {n θ ε route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hm : cycle.phases.errorPhase.span.AllStates (fun v => v.main i = .ready))
    (hh : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p))
    (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p) :
    ∃ cover : ErrorSectionCover i p e, cover.count = 1 := by
  obtain ⟨cover⟩ := cycle.error_cover_of_exposed
    (cycle.error_exposed_of_ready_error hb hf hm hh) (cycle.error_rest_ready hv hr hno)
  refine ⟨cover, ?_⟩
  have hc := cover.ledger_eq
  have hd := (cycle.total_error_of_ready_error hb hf hv hm hh hr hno).1
  have count_real : (cover.count : ℝ) = 1 := by linarith
  exact_mod_cast count_real

theorem SensorCycle.error_cover_of_invariant {n θ ε route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hm : e.AllStates (fun v => v.main i = .ready))
    (hh : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p))
    (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p) :
    ∃ cover : ErrorSectionCover i p e, cover.count = 1 :=
  cycle.error_cover_of_ready_error hb hf hv (cycle.error_states hm).1 hh hr hno

/-- A protected ERROR phase contributes no counted section. Every flow is
inactive for its actual auxiliary or main mode, including the READY tail. -/
theorem SensorCycle.error_inactive_of_protected_error {n θ route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (hv : RawValid s) (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p)
    (hm : cycle.phases.errorPhase.span.AllStates (fun v => v.main i ≠ .ready)) :
    e.AllFlows (fun {v w} (_ : Flow θ v w) =>
      v.aux i p ≠ .error ∨ v.main i ≠ .ready) := by
  let tr := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  let er := cycle.phases.errorPhase
  have htr := tr.span.error_inactive_of_auxFlows i p .ready (by decide) tr.flows
  have hmk := mk.span.error_inactive_of_auxFlows i p .mark (by decide) mk.flows
  have hsi := si.span.error_inactive_of_auxFlows i p .silent (by decide) si.flows
  have her := er.span.error_inactive_of_protected i p hm
  have htail := er.rest.error_inactive_of_auxFlows i p .ready (by decide)
    (er.rest.allStates_aux_flows i p .ready (cycle.error_rest_ready hv hr hno))
  rw [tr.reconstruct, Execution.allFlows_append]
  refine ⟨htr, ?_⟩
  change tr.rest.AllFlows _
  rw [mk.reconstruct, Execution.allFlows_append]
  refine ⟨hmk, ?_⟩
  change mk.rest.AllFlows _
  rw [si.reconstruct, Execution.allFlows_append]
  refine ⟨hsi, ?_⟩
  change si.rest.AllFlows _
  rw [er.reconstruct, Execution.allFlows_append]
  exact ⟨her, htail⟩

theorem SensorCycle.error_cover_of_protected {n θ route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (hv : RawValid s) (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p)
    (hm : cycle.phases.errorPhase.span.AllStates (fun v => v.main i ≠ .ready)) :
    ∃ cover : ErrorSectionCover i p e, cover.count = 0 := by
  let inactive := cycle.error_inactive_of_protected_error hv hr hno hm
  exact ⟨e.errorCover_of_inactive i p inactive,
    e.errorCover_of_inactive_count i p inactive⟩

theorem SensorCycle.error_cover_of_trigger {n θ route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (trigger : MainTrigger e i) (hv : RawValid s)
    (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p)
    (hcap : s.x i .b ≤ 11 / 10) :
    ∃ cover : ErrorSectionCover i p e, cover.count = 0 :=
  cycle.error_cover_of_protected hv hr hno (cycle.error_protected_by_trigger trigger hcap)

#print axioms SensorCycle.error_cover_of_ready_error
#print axioms SensorCycle.error_cover_of_invariant
#print axioms SensorCycle.error_cover_of_protected

end KernelR.Hybrid
