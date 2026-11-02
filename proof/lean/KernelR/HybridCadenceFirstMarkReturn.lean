import KernelR.HybridCadenceFirstMarkSource
import KernelR.HybridCadenceMarkOnlyExistence

/-! C's actual656 MARK-only response and fresh660 source, while A/B retain
the same unfinished first-wave paths and all carried physical coordinates. -/
namespace KernelR.Hybrid

namespace FirstCadenceMarkSource
variable {θ born freshB freshC newbornB newbornC forward backward delay}
  {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
  {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
  {r : FirstCadenceWire w} {relay : FirstCadenceRelayWire r} {a : FirstCadenceAFire relay}
  (g : FirstCadenceMarkSource a)

/-- C's actual source state, with exactly its still-pending source queue. -/
noncomputable def localC : Snapshot 1 :=
  {cadenceRelayLocal g.final 2 with pending := sourceTrain 0 0 660 4 20}

theorem local_c_physical : PhysicalInvariant (fun _ : Fin 1 => freshC) g.localC :=
  ⟨fun _ => g.physical.region 2,fun _ q => g.physical.gain_cap 2 q,
    fun _ => g.physical.recovery_cap 2,fun _ => g.physical.reserve 2⟩

theorem local_c_raw_valid : RawValid g.localC := fun _ q origin h => g.raw_valid 2 q origin h

end FirstCadenceMarkSource

structure FirstCadenceMarkReturn {θ born freshB freshC newbornB newbornC forward backward delay}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    {r : FirstCadenceWire w} {relay : FirstCadenceRelayWire r} {a : FirstCadenceAFire relay}
    (g : FirstCadenceMarkSource a) where
  localResponse : CadenceMarkOnlyResponse (fun _ : Fin 1 => freshC) (fun _ _ => []) g.localC 0
  localSource : CadenceMarkOnlyNextSource localResponse (sourceTrain 0 0 664 4 19)
  aContinuation : Execution θ (fun _ _ => []) g.aCut.state a.localCycle.returned.final
  a_reconstruct : aContinuation = Execution.cons (.flow g.aCut.flow) g.aCut.rest
  aCut : aContinuation.BeforeFlowCut 660
  bFinal : Snapshot 1
  b_final_state : bFinal = quietAt relay.senderCycle.returned.final
    (max (660 : ℝ) relay.senderCycle.returned.final.time + 1)
  bContinuation : Execution (fun _ : Fin 1 => freshB) (fun _ _ => []) g.bCut.state bFinal
  bCut : bContinuation.BeforeFlowCut 660
  final : Snapshot 3
  final_state : final = (localSource.final.prependQuiet bCut.state).prependQuiet aCut.state
  execution : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) g.final final
  date : final.time = 660
  pending : final.pending = sourceTrain 2 0 664 4 19
  a_values : final.x 0 = aCut.state.x 0
  a_main : final.main 0 = aCut.state.main 0
  a_aux : ∀ q, final.aux 0 q = aCut.state.aux 0 q
  a_raw : ∀ q, final.raw 0 q = aCut.state.raw 0 q
  b_values : final.x 1 = bCut.state.x 0
  b_main : final.main 1 = bCut.state.main 0
  b_aux : ∀ q, final.aux 1 q = bCut.state.aux 0 q
  b_raw : ∀ q, final.raw 1 q = bCut.state.raw 0 q
  c_values : final.x 2 = localSource.final.x 0
  c_ready : ReadyCoordinates final 2
  c_charge : final.x 2 .q = 1 / 10
  c_raw_active : final.raw 2 0 = some final.time
  c_raw_other : ∀ q, q ≠ 0 → final.raw 2 q = none
  gains : ∀ i q, final.x i (.z q) = g.final.x i (.z q)
  recovery_other : ∀ i, i ≠ 2 → final.x i .b = g.final.x i .b
  c_recovery_gain : final.x 2 .b = g.final.x 2 .b + 1 / 10
  c_recovery_own : final.x 2 .b = newbornC.x .b + 1 / 5
  c_gain_target : final.x 2 (.z 0) = newbornC.x (.z 0) + 9 / 5
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨2,0,660⟩]
  c_mark : execution.ledger.mark 2 0 = 1 / 10
  error_zero : ∀ i q, execution.ledger.error i q = 0
  physical : PhysicalInvariant (extendParameters (extendParameters θ freshB) freshC) final
  raw_valid : RawValid final
  complete : CompleteThrough execution 660

private theorem mark_return_snapshot_ext {n} (s u : Snapshot n)
    (ht : s.time = u.time) (hx : s.x = u.x) (hm : s.main = u.main)
    (ha : s.aux = u.aux) (hr : s.raw = u.raw) (hp : s.pending = u.pending) : s = u := by
  cases s; cases u; simp_all only

theorem first_cadence_mark_return_exists {θ born freshB freshC newbornB newbornC forward backward delay ε}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    {r : FirstCadenceWire w} {relay : FirstCadenceRelayWire r} {a : FirstCadenceAFire relay}
    (g : FirstCadenceMarkSource a)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε) :
    Nonempty (FirstCadenceMarkReturn g) := by
  let sC := g.localC
  let route := cadenceRouter cascadeForward cascadeBackward
  let params : Fin 3 → Parameters := extendParameters (extendParameters θ freshB) freshC
  have hSCdate : sC.time = 656 := g.date
  have hCown : g.final.x 2 .b = newbornC.x .b + 1 / 10 := by
    rw [g.recovery,a.recovery,relay.recovery,r.recovery,w.recovery,c.c_recovery]
  have hCb : 17999 / 100000 ≤ sC.x 0 .b ∧ sC.x 0 .b ≤ 18001 / 100000 := by
    change 17999 / 100000 ≤ g.final.x 2 .b ∧ g.final.x 2 .b ≤ 18001 / 100000
    rw [hCown]
    constructor <;> linarith [newbornC.recovery.1,newbornC.recovery.2]
  have hpC : ∀ d ∈ sC.pending, sC.time + 4 ≤ d.due := by
    intro d hd
    change d ∈ sourceTrain (0 : Fin 1) 0 660 4 20 at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [hSCdate]
    change 656 + 4 ≤ 660 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨response⟩ := cadence_mark_only_response_exists (route := fun _ _ => []) hb.extend_new
    sC 0 g.local_c_physical g.local_c_raw_valid g.c_main_slow g.c_charge hCb
    (fun q => ⟨g.c_auxiliary q,g.c_rest q⟩) g.c_raw_active g.c_raw_other hpC
  have hHeadC : sC.pending = ⟨0,0,sC.time + 4⟩ :: sourceTrain 0 0 664 4 19 := by
    change sourceTrain 0 0 660 4 20 = _
    rw [sourceTrain_succ,hSCdate]
    norm_num
  have hLaterC : ∀ d ∈ sourceTrain (0 : Fin 1) 0 664 4 19, sC.time + 4 < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [hSCdate]
    change 656 + 4 < 664 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨cn⟩ := cadence_mark_only_next_source_exists response hb.extend_new
    g.local_c_physical g.local_c_raw_valid _ hHeadC hLaterC
  have hCdate : cn.final.time = 660 := by rw [cn.date,hSCdate]; norm_num
  have heAFull : g.aContinuation.ledger.emissions = [] := by
    rw [g.a_reconstruct,Execution.emissions_append,a.localCycle.fast.emissions,a.localCycle.returned.emissions]
    rfl
  have hdAFull : g.aContinuation.deliveries = [] := by
    rw [g.a_reconstruct,Execution.deliveries_append,a.localCycle.fast.deliveries,a.localCycle.returned.deliveries]
    rfl
  let ae : Execution θ (fun _ _ => []) g.aCut.state a.localCycle.returned.final :=
    .cons (.flow g.aCut.flow) g.aCut.rest
  have heA : ae.ledger.emissions = [] := (List.append_eq_nil_iff.mp (g.aCut.emissions.symm.trans heAFull)).2
  have hdA : ae.deliveries = [] := (List.append_eq_nil_iff.mp (g.aCut.deliveries.symm.trans hdAFull)).2
  have hAEmpty : g.aCut.state.pending = [] := by
    rw [← ae.pending_eq_of_no_events heA hdA]
    exact a.localCycle.pending
  have hAend : (660 : ℝ) < a.localCycle.returned.final.time := by
    rw [a.localCycle.date]
    change 660 < relay.final.time + 69 / 10
    linarith [relay.window.1]
  obtain ⟨acut⟩ := ae.before_flow_cut_exists 660 (by rw [g.aCut.date]; norm_num) hAend
  have heACut : acut.cut.ledger.emissions = [] := (List.append_eq_nil_iff.mp (acut.emissions.symm.trans heA)).1
  have hdACut : acut.cut.deliveries = [] := (List.append_eq_nil_iff.mp (acut.deliveries.symm.trans hdA)).1
  have heBFast : (Execution.cons (.flow relay.bCutA.flow) relay.bCutA.rest).ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (relay.bCutA.emissions.symm.trans relay.senderCycle.fast.emissions)).2
  have hdBFast : (Execution.cons (.flow relay.bCutA.flow) relay.bCutA.rest).deliveries = [] :=
    (List.append_eq_nil_iff.mp (relay.bCutA.deliveries.symm.trans relay.senderCycle.fast.deliveries)).2
  have heBOld : a.bContinuation.ledger.emissions = [] := by
    rw [a.b_reconstruct,Execution.emissions_append,heBFast,relay.senderCycle.returned.emissions]; rfl
  have hdBOld : a.bContinuation.deliveries = [] := by
    rw [a.b_reconstruct,Execution.deliveries_append,hdBFast,relay.senderCycle.returned.deliveries]; rfl
  have heBMid : g.bContinuation.ledger.emissions = [] := by
    rw [g.b_reconstruct]
    exact (List.append_eq_nil_iff.mp (a.bCut.emissions.symm.trans heBOld)).2
  have hdBMid : g.bContinuation.deliveries = [] := by
    rw [g.b_reconstruct]
    exact (List.append_eq_nil_iff.mp (a.bCut.deliveries.symm.trans hdBOld)).2
  let bRest : Execution (fun _ : Fin 1 => freshB) (fun _ _ => []) g.bCut.state relay.senderCycle.returned.final :=
    .cons (.flow g.bCut.flow) g.bCut.rest
  have heBRest : bRest.ledger.emissions = [] := (List.append_eq_nil_iff.mp (g.bCut.emissions.symm.trans heBMid)).2
  have hdBRest : bRest.deliveries = [] := (List.append_eq_nil_iff.mp (g.bCut.deliveries.symm.trans hdBMid)).2
  have hBEmpty : g.bCut.state.pending = [] := by
    rw [← bRest.pending_eq_of_no_events heBRest hdBRest]
    exact relay.senderCycle.pending
  let T := max (660 : ℝ) relay.senderCycle.returned.final.time + 1
  have hBT : relay.senderCycle.returned.final.time < T := by
    dsimp [T]
    linarith [le_max_right (660 : ℝ) relay.senderCycle.returned.final.time]
  let bWaitFlow := quietFlow (θ := fun _ : Fin 1 => freshB) relay.senderCycle.returned.final hBT
    (fun j => (relay.senderCycle.ready j).ready)
    (fun j q => ((relay.senderCycle.ready j).auxiliary q).1) relay.senderCycle.raw_none
    (fun j => by linarith [(relay.senderCycle.ready j).charge.2])
    (fun j q => by linarith [((relay.senderCycle.ready j).auxiliary q).2.2])
    (by intro d hd; rw [relay.senderCycle.pending] at hd; contradiction)
  let bFinal := quietAt relay.senderCycle.returned.final T
  let bWait : Execution (fun _ : Fin 1 => freshB) (fun _ _ => []) relay.senderCycle.returned.final bFinal :=
    .cons (.flow bWaitFlow) (.nil _)
  let be := bRest.append bWait
  have heB : be.ledger.emissions = [] := by rw [Execution.emissions_append,heBRest]; rfl
  have hdB : be.deliveries = [] := by rw [Execution.deliveries_append,hdBRest]; rfl
  obtain ⟨bcut⟩ := be.before_flow_cut_exists 660 (by rw [g.bCut.date]; norm_num)
    (by change (660 : ℝ) < T; dsimp [T]; linarith [le_max_left (660 : ℝ) relay.senderCycle.returned.final.time])
  have heBCut : bcut.cut.ledger.emissions = [] := (List.append_eq_nil_iff.mp (bcut.emissions.symm.trans heB)).1
  have hdBCut : bcut.cut.deliveries = [] := (List.append_eq_nil_iff.mp (bcut.deliveries.symm.trans hdB)).1
  obtain ⟨pair,hePair,hdPair⟩ := cn.execution.prepend_neutral bcut.cut
    (g.date.trans g.bCut.date.symm) (hCdate.trans bcut.date.symm)
    cn.emissions heBCut hdBCut hBEmpty (fun _ _ => [])
  obtain ⟨woven,heW,hdW⟩ := pair.prepend_neutral acut.cut
    (g.date.trans g.aCut.date.symm) (hCdate.trans acut.date.symm)
    hePair heACut hdACut hAEmpty route
  have hSource : (sC.prependQuiet g.bCut.state).prependQuiet g.aCut.state = g.final := by
    apply mark_return_snapshot_ext
    · rfl
    · funext i; fin_cases i
      · exact g.a_values.symm
      · exact g.b_values.symm
      · rfl
    · funext i; fin_cases i
      · exact g.a_main.symm
      · exact g.b_main.symm
      · rfl
    · funext i q; fin_cases i
      · exact (g.a_aux q).symm
      · exact (g.b_aux q).symm
      · rfl
    · funext i q; fin_cases i
      · exact (g.a_raw q).symm
      · exact (g.b_raw q).symm
      · rfl
    · change ((sC.pending.map Delivery.succ).map Delivery.succ) = g.final.pending
      rw [g.pending]
      simp [sC,FirstCadenceMarkSource.localC,sourceTrain,Delivery.succ]
  let final : Snapshot 3 := (cn.final.prependQuiet bcut.state).prependQuiet acut.state
  have hParams : prependParameters θ (prependParameters (fun _ : Fin 1 => freshB) (fun _ : Fin 1 => freshC)) = params :=
    ConstructedCadenceStart.parameters_nested
  let trace : Execution params route g.final final := (woven.cast_source hSource.symm).cast_parameters hParams
  have hLedger : trace.ledger = woven.ledger :=
    ((woven.cast_source hSource.symm).cast_parameters_ledger hParams).trans (woven.cast_source_ledger hSource.symm)
  have hDel : trace.deliveries = woven.deliveries :=
    ((woven.cast_source hSource.symm).cast_parameters_deliveries hParams).trans (woven.cast_source_deliveries hSource.symm)
  have hGains : ∀ i q, final.x i (.z q) = g.final.x i (.z q) := by
    intro i q; fin_cases i
    · have hEndGlobal : a.localCycle.returned.final.x 0 (.z q) = g.final.x 0 (.z q) :=
        (a.localCycle.gains 0 q).trans ((g.gains 0 q).trans (a.gains 0 q)).symm
      have hEnd : a.localCycle.returned.final.x 0 (.z q) = g.aCut.state.x 0 (.z q) :=
        hEndGlobal.trans (congrFun g.a_values (.z q))
      exact (acut.isPrefix.gain_eq_of_final hb.extend_old.extend_old 0 q hEnd).trans (congrFun g.a_values (.z q)).symm
    · have hEndGlobal : bFinal.x 0 (.z q) = g.final.x 1 (.z q) :=
        (relay.senderCycle.gains 0 q).trans ((g.gains 1 q).trans ((a.gains 1 q).trans (relay.gains 1 q))).symm
      have hEnd : bFinal.x 0 (.z q) = g.bCut.state.x 0 (.z q) := hEndGlobal.trans (congrFun g.b_values (.z q))
      exact (bcut.isPrefix.gain_eq_of_final hb.extend_old.extend_new 0 q hEnd).trans (congrFun g.b_values (.z q)).symm
    · exact cn.gains 0 q
  have hRecoveryOther : ∀ i, i ≠ 2 → final.x i .b = g.final.x i .b := by
    intro i hi; fin_cases i
    · have hEndGlobal : a.localCycle.returned.final.x 0 .b = g.final.x 0 .b :=
        (a.localCycle.recovery 0).trans ((g.recovery 0).trans (a.recovery 0)).symm
      have hEnd : a.localCycle.returned.final.x 0 .b = g.aCut.state.x 0 .b := hEndGlobal.trans (congrFun g.a_values .b)
      exact (acut.isPrefix.recovery_eq_of_final hb.extend_old.extend_old 0 hEnd).trans (congrFun g.a_values .b).symm
    · have hEndGlobal : bFinal.x 0 .b = g.final.x 1 .b :=
        (relay.senderCycle.recovery 0).trans ((g.recovery 1).trans ((a.recovery 1).trans (relay.recovery 1))).symm
      have hEnd : bFinal.x 0 .b = g.bCut.state.x 0 .b := hEndGlobal.trans (congrFun g.b_values .b)
      exact (bcut.isPrefix.recovery_eq_of_final hb.extend_old.extend_new 0 hEnd).trans (congrFun g.b_values .b).symm
    · exact False.elim (hi rfl)
  have hCRec : final.x 2 .b = g.final.x 2 .b + 1 / 10 := cn.recovery_gain
  have hCReady : ReadyCoordinates final 2 := ⟨(cn.ready 0).ready,(cn.ready 0).charge,(cn.ready 0).auxiliary⟩
  have hPending : final.pending = sourceTrain 2 0 664 4 19 := by
    change (cn.final.pending.map Delivery.succ).map Delivery.succ = _
    rw [cn.pending]
    simp [sourceTrain,Delivery.succ]
  have hFuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd; rw [hPending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change cn.final.time < 664 + 4 * (k.val : ℝ)
    rw [hCdate]
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  have hGuard : @BeforeGuards 3 final final.x := by
    constructor
    · intro i; fin_cases i
      · exact acut.before_guards.1 0
      · exact bcut.before_guards.1 0
      · change match final.main 2 with
          | .ready => final.x 2 .q < 1
          | .fast => 1 / 4 < final.x 2 .q
          | .slow => 1 / 10 < final.x 2 .q
        rw [hCReady.ready]
        linarith [hCReady.charge.2]
    · intro i q; fin_cases i
      · exact acut.before_guards.2 0 q
      · exact bcut.before_guards.2 0 q
      · change match final.aux 2 q with
          | .ready => final.x 2 (.m q) < 1
          | .mark => 4 / 5 < final.x 2 (.m q)
          | .silent => 1 / 10 < final.x 2 (.m q)
          | .error => 1 / 40 < final.x 2 (.m q)
        rw [(hCReady.auxiliary q).1]
        linarith [(hCReady.auxiliary q).2.2]
  have hComplete : CompleteThrough trace 660 := by
    refine ⟨hCdate,?_,?_⟩
    · intro u; apply hGuard.no_jump
      · intro i q origin hr; fin_cases i
        · change acut.state.raw 0 q = some origin at hr
          change cn.final.time < origin + 1
          rw [hCdate,← acut.date]
          exact acut.flow.initial_raw_strict 0 q origin hr
        · change bcut.state.raw 0 q = some origin at hr
          change cn.final.time < origin + 1
          rw [hCdate,← bcut.date]
          exact bcut.flow.initial_raw_strict 0 q origin hr
        · change cn.final.raw 0 q = some origin at hr
          by_cases hq : q = 0
          · subst q
            have ho : origin = cn.final.time := Option.some.inj (hr.symm.trans cn.raw_active)
            rw [ho]; change cn.final.time < cn.final.time + 1; linarith
          · rw [cn.raw_other q hq] at hr; contradiction
      · exact hFuture
    · intro d hd
      have h := hFuture d hd
      change cn.final.time < d.due at h
      rwa [hCdate] at h
  have hEm : trace.ledger.emissions = [] := (congrArg (fun L : Ledger 3 => L.emissions) hLedger).trans heW
  have hDeliveries : trace.deliveries = [⟨2,0,660⟩] := by
    rw [hDel,hdW,hdPair,cn.deliveries,hSCdate]
    norm_num [Delivery.succ]
  have hError : ∀ i q, trace.ledger.error i q = 0 := by
    intro i q
    have h := trace.gain_balance i q
    rw [hGains] at h
    linarith
  refine ⟨{
    localResponse := response, localSource := cn, aContinuation := ae, a_reconstruct := rfl, aCut := acut
    bFinal := bFinal, b_final_state := rfl, bContinuation := be, bCut := bcut
    final := final, final_state := rfl, execution := trace, date := hCdate, pending := hPending
    a_values := rfl, a_main := rfl, a_aux := fun _ => rfl, a_raw := fun _ => rfl
    b_values := rfl, b_main := rfl, b_aux := fun _ => rfl, b_raw := fun _ => rfl
    c_values := rfl, c_ready := hCReady, c_charge := cn.charge
    c_raw_active := cn.raw_active, c_raw_other := cn.raw_other
    gains := hGains, recovery_other := hRecoveryOther, c_recovery_gain := hCRec
    c_recovery_own := by rw [hCRec,hCown]; ring
    c_gain_target := ?_, emissions := hEm, deliveries := hDeliveries, c_mark := ?_
    error_zero := hError, physical := trace.physical_invariant hb g.physical
    raw_valid := trace.raw_valid g.raw_valid, complete := hComplete
  }⟩
  · rw [hGains,g.gains,a.gains,relay.gains,r.gains,w.c_gain_target,c.c_gain_other 0 (by decide)]
  · have h := trace.recovery_balance 2
    rw [hCRec,trace.recovery_sum_marks] at h
    have hothers : ∀ q, q ≠ 0 → trace.ledger.mark 2 q = 0 := by
      intro q hq
      have hno : NoArrivalAt trace 2 q := by
        simp only [NoArrivalAt,hDeliveries,List.mem_singleton]
        intro d hd
        subst d
        exact Or.inr (Ne.symm hq)
      have hready := trace.aux_ready_without_input_band 2 q (g.c_auxiliary q) (g.c_rest q).2
        (g.c_raw_other q hq) hno
      exact trace.mark_zero_aux 2 q .ready (by decide) (trace.allStates_aux_flows 2 q .ready hready)
    have hs : (∑ q : Port, trace.ledger.mark 2 q) = trace.ledger.mark 2 0 :=
      Finset.sum_eq_single 0 (fun q _ hq => hothers q hq) (by simp)
    rw [hs] at h
    linarith

end KernelR.Hybrid
