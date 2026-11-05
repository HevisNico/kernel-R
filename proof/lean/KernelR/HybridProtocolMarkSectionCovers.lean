import KernelR.HybridMarkSectionCovers
import KernelR.HybridProtectedInputShortCycle
import KernelR.HybridCadenceMarkOnlyExistence
import KernelR.HybridCadenceMixedFullResponse

/-! The three concrete learning responses used by finite-chain preparation
and cadence each admit one actual complete protected MARK section. These
wrappers take the physical inputs already used by their response factories;
they do not assume a cover or an actuation-dose equality. -/
namespace KernelR.Hybrid

theorem ProtectedInputShortCycle.mark_section_cover {θ ε route s p}
    (c : ProtectedInputShortCycle θ route s p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s)
    (hv : RawValid s) (hs : MarkEntry s 0) :
    ∃ cover : MarkSectionCover 0 p c.execution, cover.count = 1 := by
  obtain ⟨cycle⟩ := c.execution.sensor_cycle hb hf.region 0 p
    (c.auxiliary_initial p).1 c.raw_active_initial (c.auxiliary_initial p).2
    (by rw [c.date]; linarith)
  exact cycle.protected_mark_cover hb hf hv hs c.raw_active_initial c.raw_other_initial
    (by intro q; simp [NoArrivalAt, c.deliveries])

theorem ProtectedInputShortCycle.other_mark_section_cover {θ route s p}
    (c : ProtectedInputShortCycle θ route s p) (q : Port) (different : q ≠ p) :
    ∃ cover : MarkSectionCover 0 q c.execution, cover.count = 0 := by
  have states := c.execution.aux_ready_without_input_band 0 q
    (c.auxiliary_initial q).1 (c.auxiliary_initial q).2.2
    (c.raw_other_initial q different) (by simp [NoArrivalAt, c.deliveries])
  let inactive := c.execution.mark_inactive_of_auxFlows 0 q .ready (by decide)
    (c.execution.allStates_aux_flows 0 q .ready states)
  exact ⟨c.execution.markCover_of_inactive 0 q inactive,
    c.execution.markCover_of_inactive_count 0 q inactive⟩

theorem ProtectedInputShortCycle.mark_section_covers {θ ε route s p}
    (c : ProtectedInputShortCycle θ route s p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s)
    (hv : RawValid s) (hs : MarkEntry s 0) :
    ∃ covers : ∀ q, MarkSectionCover 0 q c.execution,
      ∀ q, (covers q).count = if q = p then 1 else 0 := by
  classical
  have each : ∀ q, ∃ cover : MarkSectionCover 0 q c.execution,
      cover.count = if q = p then 1 else 0 := by
    intro q
    by_cases same : q = p
    · subst q
      simpa using c.mark_section_cover hb hf hv hs
    · simpa [same] using c.other_mark_section_cover q same
  exact ⟨fun q => Classical.choose (each q), fun q => Classical.choose_spec (each q)⟩

theorem CadenceMarkOnlyResponse.mark_section_cover {θ ε route s p}
    (c : CadenceMarkOnlyResponse θ route s p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s)
    (hv : RawValid s) (hr : s.raw 0 p = some s.time) :
    ∃ cover : MarkSectionCover 0 p c.execution, cover.count = 1 := by
  apply c.pulse.mark_case.mark_section_cover hb hf hv hr
    (by simp [NoArrivalAt, c.deliveries])
  rw [← c.recovery_gain]
  linarith [c.recovery_band.2]

theorem CadenceMixedFullResponse.mark_section_cover {θ ε s p}
    (c : CadenceMixedFullResponse θ s p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s)
    (hv : RawValid s) (hr : s.raw 0 p = some s.time) :
    ∃ cover : MarkSectionCover 0 p c.execution, cover.count = 1 := by
  apply c.pulse.mark_case.mark_section_cover hb hf hv hr
    (by simp [NoArrivalAt, c.deliveries])
  rw [← c.recovery_gain]
  linarith [c.recovery_band.2]

#print axioms ProtectedInputShortCycle.mark_section_cover
#print axioms ProtectedInputShortCycle.mark_section_covers
#print axioms CadenceMarkOnlyResponse.mark_section_cover
#print axioms CadenceMixedFullResponse.mark_section_cover

end KernelR.Hybrid
