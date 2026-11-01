import KernelR.HybridCadenceCPhase
import KernelR.HybridCadenceForwardGeometry
import KernelR.HybridCadenceRelayPhase
import KernelR.HybridCadenceReturnGeometry
import KernelR.HybridCadenceWireCalendar
/-! Derive B's cadence response and its own output calendar from C's actual outputs. -/
namespace KernelR.Hybrid

noncomputable def CadenceCCalendar.forwardLatencies {θ route s u} {e : @Execution 3 θ route s u}
    {pre : CadencePrelude e} {cphase : CadenceCPhase pre} (ccal : CadenceCCalendar cphase) :
    CadenceForwardLatencies :=
  ⟨ccal.firstLow,restLatency (Real.exp (s.x 2 (.z 0) + 9 / 5)),ccal.firstHigh,
    highRestLatency (Real.exp (s.x 2 (.z 0) + 12 / 5))⟩

theorem CadenceCCalendar.forwardBounds {θ route s u} {e : @Execution 3 θ route s u}
    {pre : CadencePrelude e} {cphase : CadenceCPhase pre} (ccal : CadenceCCalendar cphase) :
    CadenceForwardLatencyBounds ccal.forwardLatencies :=
  ⟨ccal.firstLow_lower,ccal.firstLow_upper,ccal.firstLow_le_rest,ccal.restLow_lower,
    ccal.restLow_upper,ccal.firstHigh_sharp,ccal.firstHigh_le_rest,ccal.highRest_sharp⟩

structure CadenceBPhase {θ forward backward s u}
    {e : @Execution 3 θ (cadenceRouter forward backward) s u}
    {pre : CadencePrelude e} {cphase : CadenceCPhase pre} (ccal : CadenceCCalendar cphase) where
  preB : CadenceSparsePrefix e 1 2 (cadenceForwardSparse ccal.forwardLatencies forward)
    (cadenceForwardBDate ccal.forwardLatencies forward 2)
    ((cadenceForwardBDate ccal.forwardLatencies forward 3 ::
      cadenceForwardBDate ccal.forwardLatencies forward 4 ::
      cadenceForwardBDate ccal.forwardLatencies forward 5 ::
      cadenceForwardBDate ccal.forwardLatencies forward 6 ::
      cadenceForwardHighTail ccal.forwardLatencies forward).map (fun t => ⟨1,2,t⟩))
  relay : CadenceRelayPhase preB
  calendar : CadenceRelayCalendar relay

noncomputable def CadenceBPhase.returnLatencies {θ forward backward s u}
    {e : @Execution 3 θ (cadenceRouter forward backward) s u}
    {pre : CadencePrelude e} {cphase : CadenceCPhase pre} {ccal : CadenceCCalendar cphase}
    (phase : CadenceBPhase ccal) : CadenceReturnLatencies :=
  ⟨ccal.firstLow,restLatency (Real.exp (s.x 2 (.z 0) + 9 / 5)),ccal.firstHigh,
    highRestLatency (Real.exp (s.x 2 (.z 0) + 12 / 5)),
    restLatency (Real.exp (s.x 1 (.z 2))),phase.calendar.firstResidual,
    highRestLatency (Real.exp (s.x 1 (.z 2) + 3 / 5))⟩

theorem CadenceBPhase.returnBounds {θ forward backward s u}
    {e : @Execution 3 θ (cadenceRouter forward backward) s u}
    {pre : CadencePrelude e} {cphase : CadenceCPhase pre} {ccal : CadenceCCalendar cphase}
    (phase : CadenceBPhase ccal) : CadenceReturnLatencyBounds phase.returnLatencies :=
  ⟨ccal.firstLow_le_rest,ccal.restLow_lower,ccal.restLow_upper,ccal.firstHigh_sharp,
    ccal.firstHigh_le_rest,ccal.highRest_sharp,phase.calendar.restLow_lower,
    phase.calendar.restLow_upper,phase.calendar.firstResidual_sharp_lower,
    phase.calendar.firstResidual_le_rest,phase.calendar.restHigh_sharp_upper⟩

theorem CadenceBPhase.b_emission_calendar_explicit {θ forward backward s u}
    {e : @Execution 3 θ (cadenceRouter forward backward) s u}
    {pre : CadencePrelude e} {cphase : CadenceCPhase pre} {ccal : CadenceCCalendar cphase}
    (phase : CadenceBPhase ccal) :
    e.emissionTimes 1 = cadenceBOutputCalendar phase.returnLatencies forward := by
  simpa [cadenceBOutputCalendar,CadenceBPhase.returnLatencies,CadenceCCalendar.forwardLatencies,
    cadenceForwardSparse,cadenceForwardHighTail,cadenceForwardBDate,cadenceForwardCDate,
    cadenceBInputDate,cadenceCOutputDate,List.ofFn_succ] using phase.calendar.emissions

theorem CadenceBPhase.b_emission_calendar {θ forward backward s u}
    {e : @Execution 3 θ (cadenceRouter forward backward) s u}
    {pre : CadencePrelude e} {cphase : CadenceCPhase pre} {ccal : CadenceCCalendar cphase}
    (phase : CadenceBPhase ccal) :
    e.emissionTimes 1 = List.ofFn (fun j : Fin 18 => cadenceBOutputDate phase.returnLatencies forward j.val) := by
  rw [phase.b_emission_calendar_explicit]
  simp [cadenceBOutputCalendar,cadenceBOutputDate,cadenceBOutputSourceIndex,cadenceBOutputLatency,List.ofFn_succ]

theorem CadenceBPhase.emission_count {θ forward backward s u}
    {e : @Execution 3 θ (cadenceRouter forward backward) s u}
    {pre : CadencePrelude e} {cphase : CadenceCPhase pre} {ccal : CadenceCCalendar cphase}
    (phase : CadenceBPhase ccal) : (e.emissionTimes 1).length = 18 := by
  simpa [cadenceForwardSparse,cadenceForwardHighTail] using phase.relay.emissions

/-- The incoming calendar is obtained from the execution's actual C emissions.
B's two sparse pulses and all transient/dense pulse cases are then derived. -/
theorem CadenceCCalendar.b_phase {θ ε forward backward s u}
    {e : @Execution 3 θ (cadenceRouter forward backward) s u}
    {pre : CadencePrelude e} {cphase : CadenceCPhase pre} (ccal : CadenceCCalendar cphase)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : PreparedSection s 1) (hq : s.x 1 .q = 1 / 10) (hr : ∀ p, s.raw 1 p = none)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 1 (.z 2) ∧
      s.x 1 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hqueue : s.pending.filter (fun d => d.cell = 1) = [])
    (hu : u.time = 7899 / 10) (hpf : PendingFuture u)
    (hforward : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (CadenceBPhase ccal) := by
  let v := ccal.forwardLatencies
  have geometry := cadenceForward_geometry ccal.forwardBounds hforward
  have hcout : e.emissionTimes 2 = cadenceForwardCCalendar v := by
    simpa [cadenceForwardCCalendar,cadenceForwardCDate,v,CadenceCCalendar.forwardLatencies,List.ofFn_succ]
      using ccal.emissions
  have hwire := e.cadence_forward_calendar forward backward (cadenceForwardCCalendar v)
    hcout geometry.emissions_order geometry.gate hu hpf hqueue hforward
  have hcalendar : e.cellDeliveries 1 = (cadenceForwardBCalendar v forward).map (fun t => ⟨1,2,t⟩) := by
    rw [hwire]
    simp [cadenceForwardCCalendar,cadenceForwardBCalendar,cadenceForwardBDate,
      cadenceForwardCDate,cadenceForwardContact,Contact.token,List.ofFn_succ]
  have hcalendar' : e.cellDeliveries 1 =
      (cadenceForwardSparse v forward).map (fun t => ⟨1,2,t⟩) ++
        ⟨1,2,cadenceForwardBDate v forward 2⟩ ::
        ((cadenceForwardBDate v forward 3 :: cadenceForwardBDate v forward 4 ::
          cadenceForwardBDate v forward 5 :: cadenceForwardBDate v forward 6 ::
          cadenceForwardHighTail v forward).map (fun t => ⟨1,2,t⟩)) := by
    rw [hcalendar,geometry.decomposition]
    simp only [List.map_append,List.map_cons]
    rfl
  obtain ⟨preB⟩ := e.cadence_sparse_prefix hb hf hv 1 2 (cadenceForwardSparse v forward)
    (cadenceForwardBDate v forward 2)
    ((cadenceForwardBDate v forward 3 :: cadenceForwardBDate v forward 4 ::
      cadenceForwardBDate v forward 5 :: cadenceForwardBDate v forward 6 ::
      cadenceForwardHighTail v forward).map (fun t => ⟨1,2,t⟩))
    hs hq hz hr hcalendar' geometry.sparse_spacing
  have hgap1 := geometry.dense_gaps (0 : Fin 4)
  have hgap2 := geometry.dense_gaps (1 : Fin 4)
  have hgap3 := geometry.dense_gaps (2 : Fin 4)
  have hgap4 := geometry.dense_gaps (3 : Fin 4)
  norm_num only [Fin.val_zero,Fin.val_one,Fin.reduceFinMk,Nat.reduceAdd] at hgap1 hgap2 hgap3 hgap4
  have hquiet : ∀ t ∈ cadenceForwardBDate v forward 6 :: cadenceForwardHighTail v forward,
      t + 19 / 5 ≤ u.time := by
    intro t ht
    rw [hu]
    apply geometry.quiet t
    rw [geometry.decomposition]
    exact List.mem_append_right _ (by simp only [List.mem_cons] at ht ⊢; tauto)
  obtain ⟨relay⟩ := preB.relay_phase hb hf hv hz
    ⟨hgap1.1,by linarith [hgap1.2]⟩ hgap2 hgap3 hgap4 geometry.high_spacing hquiet
  obtain ⟨calendar⟩ := relay.output_calendar hb hf hv hz hgap1.1 hgap3.1 geometry.high_spacing hquiet
  exact ⟨⟨preB,relay,calendar⟩⟩

end KernelR.Hybrid
