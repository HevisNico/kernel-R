import KernelR.HybridCadenceWeakWarmup
import KernelR.HybridCadenceQuiet
import KernelR.HybridCEntry
/-! Connect the real C birth queue to its first strong period-four input. -/
namespace KernelR.Hybrid

structure CadencePrelude {θ route s u} (e : @Execution 3 θ route s u) where
  entry : Snapshot 3
  head : Execution θ route s entry
  rest : Execution θ route entry u
  reconstruct : e = head.append rest
  date : entry.time = 652
  downstream : CadenceDownstreamIdle head
  c_coordinates : CadenceReadyCoordinates entry 2 (3 / 10)
  c_charge_lower : 1 / 10 ≤ entry.x 2 .q
  c_emissions : head.emissionTimes 2 = []
  c_gain_target : entry.x 2 (.z 0) = s.x 2 (.z 0) + 9 / 5
  c_gain_other : ∀ p, p ≠ 0 → entry.x 2 (.z p) = s.x 2 (.z p)
  c_recovery : entry.x 2 .b = s.x 2 .b
  c_error : head.ledger.error 2 0 = 9 / 5
  c_mark : ∀ p, head.ledger.mark 2 p = 0
  c_raw_active : entry.raw 2 0 = some entry.time
  c_raw_other : ∀ p, p ≠ 0 → entry.raw 2 p = none
  c_pending : (entry.pending.filter (fun d => d.cell = 2)).Perm (sourceTrain 2 0 656 4 21)
  calendar : rest.cellDeliveries 2 = sourceTrain 2 0 656 4 21
  physical : PhysicalInvariant θ entry
  raw_valid : RawValid entry
  pending_future : PendingFuture entry

/-- The preserved twenty-five C sources select its three actual weak cases.
At 652 the next input is already fresh, with the real residual charge; the
twenty-one later sources and all downstream cells are still in the trace. -/
theorem Execution.cadence_prelude {θ ε s u} (forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter forward backward) s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (ha : PreparedSection s 0) (hqa : s.x 0 .q = 1 / 10) (hra : ∀ p, s.raw 0 p = none)
    (hbs : PreparedSection s 1) (hqb : s.x 1 .q = 1 / 10) (hrb : ∀ p, s.raw 1 p = none)
    (hc : PreparedSection s 2) (hqc : s.x 2 .q = 1 / 10) (hrc : ∀ p, s.raw 2 p = none)
    (hzc : s.x 2 (.z 0) ≤ Real.log (3 / 10) + 1 / 100000)
    (hAempty : s.pending.filter (fun d => d.cell = 0) = [])
    (hBempty : s.pending.filter (fun d => d.cell = 1) = [])
    (hCqueue : (s.pending.filter (fun d => d.cell = 2)).Perm (sourceTrain 2 0 640 4 25))
    (hu : u.time = 7899 / 10) (hpf : PendingFuture s)
    (hforward : ∀ t, 0 ≤ forward t) (hbackward : ∀ t, 0 ≤ backward t) :
    Nonempty (CadencePrelude e) := by
  have hcausal := cadenceRouter.causal forward backward hforward hbackward
  have hfuture := e.pending_future hcausal hpf
  obtain ⟨act⟩ := e.cadence_source_activation forward backward hb hf hv hc hqc hrc hCqueue hu hfuture
  let cut := act.cut
  have hcal : cut.rest.cellDeliveries 2 = ⟨2,0,644⟩ :: ⟨2,0,648⟩ :: ⟨2,0,652⟩ ::
      sourceTrain 2 0 656 4 21 := by
    rw [cut.later]
    norm_num only [sourceTrain_succ]
  have hznext : cut.afterArrival.x 2 (.z 0) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [act.input.gain_preserved 0]
    exact hzc
  obtain ⟨warm⟩ := cut.rest.cadence_weak_warmup hb act.physical act.raw_valid 2 0
    act.prepared.ready_coordinates act.charge_rest hznext act.input.raw_active act.input.raw_other
    (sourceTrain 2 0 656 4 21) cut.date.2 hcal
  let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
  let head := advanced.append warm.head
  have he : e = head.append warm.rest := by
    calc
      e = cut.span.append (.cons (.jump cut.entry) cut.rest) := cut.reconstruct
      _ = cut.span.append (.cons (.jump cut.entry) (warm.head.append warm.rest)) :=
        congrArg (fun actual => cut.span.append (.cons (.jump cut.entry) actual)) warm.reconstruct
      _ = _ := by simp only [head,advanced,Execution.append_assoc,Execution.append]
  have hd : (⟨2,0,640⟩ : Delivery 3) ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  have hadvancedQuiet : advanced.emissionTimes 2 = [] := by
    change (cut.span.append (.cons (.jump cut.entry) (.nil _))).emissionTimes 2 = []
    rw [Execution.emissionTimes_append,act.input.emissions_before,List.nil_append]
    rw [Execution.emissionTimes_cons]
    simp only [Move.ledger,cut.entry.no_emissions_of_delivery _ hd,
      Execution.emissionTimes,Execution.ledger,Ledger.zero,List.filter_nil,List.map_nil,List.nil_append]
  have hquiet : head.emissionTimes 2 = [] := by
    change (advanced.append warm.head).emissionTimes 2 = []
    rw [Execution.emissionTimes_append,hadvancedQuiet,warm.emissions,List.nil_append]
  obtain ⟨downstream⟩ := head.cadence_downstream_idle forward backward ha hqa hra hbs hqb hrb
    hAempty hBempty hquiet
  have hgain : warm.entry.x 2 (.z 0) = s.x 2 (.z 0) + 9 / 5 := by
    rw [warm.gain_target,act.input.gain_preserved 0]
    norm_num
  have hother : ∀ p, p ≠ 0 → warm.entry.x 2 (.z p) = s.x 2 (.z p) := by
    intro p hp
    rw [warm.gain_other p hp,act.input.gain_preserved p]
  have hpartition : sourceTrain (2 : Fin 3) 0 640 4 25 =
      [⟨2,0,640⟩,⟨2,0,644⟩,⟨2,0,648⟩,⟨2,0,652⟩] ++ sourceTrain 2 0 656 4 21 := by
    norm_num only [sourceTrain_succ,List.cons_append,List.nil_append]
  have hdel : head.cellDeliveries 2 = [⟨2,0,640⟩,⟨2,0,644⟩,⟨2,0,648⟩,⟨2,0,652⟩] := by
    have h := e.cadence_source_calendar forward backward hCqueue hu hfuture
    rw [he,Execution.cellDeliveries,Execution.deliveries_append,List.filter_append] at h
    change head.cellDeliveries 2 ++ warm.rest.cellDeliveries 2 = _ at h
    rw [warm.calendar,hpartition] at h
    exact List.append_cancel_right h
  have hremain := head.cell_pending_perm_of_prefix 2
    [⟨2,0,640⟩,⟨2,0,644⟩,⟨2,0,648⟩,⟨2,0,652⟩] (sourceTrain 2 0 656 4 21)
    (hCqueue.trans (List.Perm.of_eq hpartition)) (List.Perm.of_eq hdel)
    (fun event _ => cadenceRouter.closed_to_c forward backward event.1 event.2)
  have hstates := head.ready_states_of_no_emissions 2 hc.ready hquiet
  refine ⟨⟨warm.entry,head,warm.rest,he,?_,downstream,warm.coordinates,
    warm.charge_lower (by rw [act.charge_rest]),hquiet,hgain,hother,?_,?_,?_,warm.raw_active,
    warm.raw_other,hremain,warm.calendar,head.physical_invariant hb hf,head.raw_valid hv,
    head.pending_future hcausal hpf⟩⟩
  · simpa using warm.date
  · rw [warm.recovery_preserved,act.input.recovery_preserved]
  · have h := head.gain_balance 2 0
    rw [hgain] at h
    linarith
  · intro p
    exact head.mark_zero_ready 2 p (head.allStates_main_flows 2 .ready hstates)

/-- The complete C-entry theorem supplies every physical state and source
premise of the cadence prelude from each cell's own original birth. -/
theorem CEntry.cadence_prelude {θ freshB freshC ε routeBefore born s u v w}
    {forward backward delay : ℝ → ℝ}
    {teaching : @StagedExecution 1 θ freshB routeBefore (reciprocalEntryRouter forward backward) born s}
    {following : Execution (extendParameters θ freshB) (reciprocalEntryRouter forward backward) s u}
    {introduction : @StagedExecution 2 (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (cTeachingRouter delay) u v}
    (entry : CEntry forward backward delay teaching following introduction)
    (nextForward nextBackward : ℝ → ℝ)
    (next : Execution (extendParameters (extendParameters θ freshB) freshC)
      (cadenceRouter nextForward nextBackward) v w)
    (hb : PhysicalBox (extendParameters (extendParameters θ freshB) freshC) ε)
    (hsources : introduction.birth.sources = sourceTrain 2 0 640 4 25)
    (hw : w.time = 7899 / 10)
    (hforward : ∀ t, 0 ≤ nextForward t) (hbackward : ∀ t, 0 ≤ nextBackward t) :
    Nonempty (CadencePrelude next) := by
  have hz : v.x 2 (.z 0) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [entry.c_introduction.gain_c_other 0 (by decide)]
    simpa [nominalGain] using (introduction.birth.newborn.gain (0 : Port)).2
  exact next.cadence_prelude nextForward nextBackward hb entry.c_introduction.physical entry.c_introduction.raw_valid
    entry.c_introduction.phase.a_idle.prepared entry.c_introduction.phase.a_idle.charge_rest entry.c_introduction.a_raw
    entry.c_introduction.phase.b_train.prepared entry.c_introduction.phase.b_train.charge_rest
    entry.c_introduction.phase.b_train.raw_finished entry.c_introduction.phase.c_phase.prepared
    entry.c_introduction.phase.c_phase.charge_rest entry.c_introduction.phase.c_phase.raw_finished hz
    entry.c_introduction.queues.a_empty entry.c_introduction.queues.b_empty (entry.cadence_sources hsources)
    hw entry.c_introduction.pending_future hforward hbackward

end KernelR.Hybrid
