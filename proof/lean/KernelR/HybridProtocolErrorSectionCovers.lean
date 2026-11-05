import KernelR.HybridErrorSectionCovers
import KernelR.HybridWeakInputCycleExistence
import KernelR.HybridCadenceMixedFullResponse

/-! Actual section covers for the weak and mixed physical learning responses.
Their factories retain the main-mode chronology used to establish exposure;
the covers are constructed before the exact natural counts are deduced. -/
namespace KernelR.Hybrid

theorem SilentPulse.error_section_cover {n θ ε route s u i p}
    {e : @Execution n θ route s u} (pulse : SilentPulse e i p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (headroom : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p))
    (raw : s.raw i p = some s.time) (noArrival : NoArrivalAt e i p) :
    ∃ cover : ErrorSectionCover i p e, cover.count = 1 :=
  pulse.cycle.error_cover_of_invariant hb hf hv pulse.ready_states headroom raw noArrival

theorem SilentPulse.mark_section_cover {n θ route s u i p}
    {e : @Execution n θ route s u} (pulse : SilentPulse e i p) (q : Port) :
    ∃ cover : MarkSectionCover i q e, cover.count = 0 := by
  let inactive := e.mark_inactive_of_ready i q (e.allStates_main_flows i .ready pulse.ready_states)
  exact ⟨e.markCover_of_inactive i q inactive, e.markCover_of_inactive_count i q inactive⟩

theorem WeakInputCycle.error_section_cover {n θ ε route s i p}
    (cycle : @WeakInputCycle n θ route s i p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (headroom : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p))
    (raw : s.raw i p = some s.time) :
    ∃ cover : ErrorSectionCover i p cycle.execution, cover.count = 1 :=
  cycle.pulse.error_section_cover hb hf hv headroom raw (by simp [NoArrivalAt, cycle.deliveries])

theorem CadenceMixedFullResponse.error_section_cover {θ ε s p}
    (response : CadenceMixedFullResponse θ s p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (headroom : s.x 0 (.z p) + 3 / 5 < Real.log ((θ 0).cap p))
    (raw : s.raw 0 p = some s.time) :
    ∃ cover : ErrorSectionCover 0 p response.execution, cover.count = 1 :=
  response.pulse.mark_case.cycle.error_cover_of_ready_error hb hf hv
    response.pulse.error_ready headroom raw (by simp [NoArrivalAt, response.deliveries])

#print axioms SilentPulse.error_section_cover
#print axioms SilentPulse.mark_section_cover
#print axioms WeakInputCycle.error_section_cover
#print axioms CadenceMixedFullResponse.error_section_cover

end KernelR.Hybrid
