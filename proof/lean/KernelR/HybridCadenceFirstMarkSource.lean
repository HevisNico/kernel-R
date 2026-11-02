import KernelR.HybridCadenceFirstAFire

/-! Continue the same first-wave A/B/C paths to the real source656 arrival.
C is still SLOW; no prepared return or charge reset is imposed on A or B. -/
namespace KernelR.Hybrid

structure FirstCadenceMarkSource {θ born freshB freshC newbornB newbornC forward backward delay}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    {r : FirstCadenceWire w} {relay : FirstCadenceRelayWire r} (a : FirstCadenceAFire relay) where
  aContinuation : Execution θ (fun _ _ => []) a.localCycle.fire.final a.localCycle.returned.final
  a_reconstruct : aContinuation = a.localCycle.fast.execution.append a.localCycle.returned.execution
  aCut : aContinuation.BeforeFlowCut 656
  bContinuation : Execution (fun _ : Fin 1 => freshB) (fun _ _ => []) a.bCut.state relay.senderCycle.returned.final
  b_reconstruct : bContinuation = Execution.cons (.flow a.bCut.flow) a.bCut.rest
  bCut : bContinuation.BeforeFlowCut 656
  cContinuation : Execution (fun _ : Fin 1 => freshC) (fun _ _ => []) a.cCut.state relay.cSpan.final
  c_reconstruct : cContinuation = Execution.cons (.flow a.cCut.flow) a.cCut.rest
  before : Snapshot 3
  before_state : before = (bCut.state.product relay.cSpan.final (sourceTrain 1 0 656 4 21)).prependQuiet aCut.state
  final : Snapshot 3
  final_state : final = {setRaw before 2 0 (some before.time) with pending := sourceTrain 2 0 660 4 20}
  wait : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) a.final before
  arrival : Jump (cadenceRouter cascadeForward cascadeBackward) before final
  execution : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) a.final final
  reconstruct : execution = wait.append (.cons (.jump arrival) (.nil _))
  before_date : before.time = 656
  date : final.time = 656
  pending : final.pending = sourceTrain 2 0 660 4 20
  a_values : final.x 0 = aCut.state.x 0
  a_main : final.main 0 = aCut.state.main 0
  a_aux : ∀ q, final.aux 0 q = aCut.state.aux 0 q
  a_raw : ∀ q, final.raw 0 q = aCut.state.raw 0 q
  b_values : final.x 1 = bCut.state.x 0
  b_main : final.main 1 = bCut.state.main 0
  b_aux : ∀ q, final.aux 1 q = bCut.state.aux 0 q
  b_raw : ∀ q, final.raw 1 q = bCut.state.raw 0 q
  c_values : final.x 2 = relay.cSpan.final.x 0
  c_main_slow : final.main 2 = .slow
  c_charge : 37 / 250 ≤ final.x 2 .q ∧ final.x 2 .q ≤ 1 / 4
  c_auxiliary : ∀ q, final.aux 2 q = .ready
  c_rest : ∀ q, RestBand (final.x 2 (.m q))
  c_trained_rest : final.x 2 (.m 0) = 1 / 40
  c_raw_active : final.raw 2 0 = some final.time
  c_raw_other : ∀ q, q ≠ 0 → final.raw 2 q = none
  gains : ∀ i q, final.x i (.z q) = a.final.x i (.z q)
  recovery : ∀ i, final.x i .b = a.final.x i .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨2,0,656⟩]
  physical : PhysicalInvariant (extendParameters (extendParameters θ freshB) freshC) final
  raw_valid : RawValid final
  complete : CompleteThrough execution 656

theorem first_cadence_mark_source_exists {θ born freshB freshC newbornB newbornC forward backward delay ε}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    {r : FirstCadenceWire w} {relay : FirstCadenceRelayWire r} (a : FirstCadenceAFire relay)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε) :
    Nonempty (FirstCadenceMarkSource a) := by
  let Q := sourceTrain (1 : Fin 2) 0 656 4 21
  let later := sourceTrain (2 : Fin 3) 0 660 4 20
  let route := cadenceRouter cascadeForward cascadeBackward
  let params : Fin 3 → Parameters := extendParameters (extendParameters θ freshB) freshC
  let ae := a.localCycle.fast.execution.append a.localCycle.returned.execution
  have heA : ae.ledger.emissions = [] := by
    rw [Execution.emissions_append,a.localCycle.fast.emissions,a.localCycle.returned.emissions]; rfl
  have hdA : ae.deliveries = [] := by
    rw [Execution.deliveries_append,a.localCycle.fast.deliveries,a.localCycle.returned.deliveries]; rfl
  have hAend : (656 : ℝ) < a.localCycle.returned.final.time := by
    rw [a.localCycle.date]
    change 656 < relay.final.time + 69 / 10
    linarith [relay.window.1]
  obtain ⟨acut⟩ := ae.before_flow_cut_exists 656 (by linarith [a.window.2,a.date]) hAend
  have heACut : acut.cut.ledger.emissions = [] := (List.append_eq_nil_iff.mp (acut.emissions.symm.trans heA)).1
  have hdACut : acut.cut.deliveries = [] := (List.append_eq_nil_iff.mp (acut.deliveries.symm.trans hdA)).1
  have heBFast : (Execution.cons (.flow relay.bCutA.flow) relay.bCutA.rest).ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (relay.bCutA.emissions.symm.trans relay.senderCycle.fast.emissions)).2
  have hdBFast : (Execution.cons (.flow relay.bCutA.flow) relay.bCutA.rest).deliveries = [] :=
    (List.append_eq_nil_iff.mp (relay.bCutA.deliveries.symm.trans relay.senderCycle.fast.deliveries)).2
  have heBFull : a.bContinuation.ledger.emissions = [] := by
    rw [a.b_reconstruct,Execution.emissions_append,heBFast,relay.senderCycle.returned.emissions]; rfl
  have hdBFull : a.bContinuation.deliveries = [] := by
    rw [a.b_reconstruct,Execution.deliveries_append,hdBFast,relay.senderCycle.returned.deliveries]; rfl
  let be : Execution (fun _ : Fin 1 => freshB) (fun _ _ => []) a.bCut.state relay.senderCycle.returned.final :=
    .cons (.flow a.bCut.flow) a.bCut.rest
  have heB : be.ledger.emissions = [] := (List.append_eq_nil_iff.mp (a.bCut.emissions.symm.trans heBFull)).2
  have hdB : be.deliveries = [] := (List.append_eq_nil_iff.mp (a.bCut.deliveries.symm.trans hdBFull)).2
  have hBend : (656 : ℝ) < relay.senderCycle.returned.final.time := by
    rw [relay.senderCycle.date]
    change 656 < r.final.time + 69 / 10
    linarith [r.window.1]
  obtain ⟨bcut⟩ := be.before_flow_cut_exists 656
    (by rw [a.bCut.date]; linarith [a.window.2,a.date]) hBend
  have heBCut : bcut.cut.ledger.emissions = [] := (List.append_eq_nil_iff.mp (bcut.emissions.symm.trans heB)).1
  have hdBCut : bcut.cut.deliveries = [] := (List.append_eq_nil_iff.mp (bcut.deliveries.symm.trans hdB)).1
  have heCT : (Execution.cons (.flow relay.cCutF.flow) relay.cCutF.rest).ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (relay.cCutF.emissions.symm.trans (relay.cSpan.fromCut_emissions r.cutH))).2
  have hdCT : (Execution.cons (.flow relay.cCutF.flow) relay.cCutF.rest).deliveries = [] :=
    (List.append_eq_nil_iff.mp (relay.cCutF.deliveries.symm.trans (relay.cSpan.fromCut_deliveries r.cutH))).2
  have heCFull : a.cContinuation.ledger.emissions = [] := by
    rw [a.c_reconstruct]
    exact (List.append_eq_nil_iff.mp (relay.cCutA.emissions.symm.trans heCT)).2
  have hdCFull : a.cContinuation.deliveries = [] := by
    rw [a.c_reconstruct]
    exact (List.append_eq_nil_iff.mp (relay.cCutA.deliveries.symm.trans hdCT)).2
  let ce : Execution (fun _ : Fin 1 => freshC) (fun _ _ => []) a.cCut.state relay.cSpan.final :=
    .cons (.flow a.cCut.flow) a.cCut.rest
  have heC : ce.ledger.emissions = [] := (List.append_eq_nil_iff.mp (a.cCut.emissions.symm.trans heCFull)).2
  have hdC : ce.deliveries = [] := (List.append_eq_nil_iff.mp (a.cCut.deliveries.symm.trans hdCFull)).2
  have hCend : relay.cSpan.final.time = 656 := by
    rw [relay.cSpan.date]
    have ht : w.localWarmup.final.time = 652 := w.localWarmup.date
    rw [ht]; norm_num
  have hQ : ∀ d ∈ Q, bcut.state.time ≤ d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [bcut.date]
    change 656 ≤ 656 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨pair,hePair,hdPair⟩ := bcut.cut.product_neutral ce
    (a.bCut.date.trans a.cCut.date.symm) (bcut.date.trans hCend.symm)
    heBCut hdBCut heC hdC Q hQ (fun _ _ => [])
  have hHeadPending : a.localCycle.fire.final.pending = [] := by
    rw [a.localCycle.fire.pending]
    rfl
  obtain ⟨woven,heW,hdW⟩ := pair.prepend_neutral acut.cut a.bCut.date
    (bcut.date.trans acut.date.symm) hePair heACut hdACut hHeadPending route
  let before : Snapshot 3 := (bcut.state.product relay.cSpan.final Q).prependQuiet acut.state
  have hParams : prependParameters θ (cBirthPairParameters freshB freshC) = params :=
    cBirthPairParameters_prepend θ freshB freshC
  let wait : Execution params route a.final before := (woven.cast_source a.final_state).cast_parameters hParams
  have hWaitLedger : wait.ledger = woven.ledger :=
    ((woven.cast_source a.final_state).cast_parameters_ledger hParams).trans (woven.cast_source_ledger a.final_state)
  have heWait : wait.ledger.emissions = [] := (congrArg (fun L : Ledger 3 => L.emissions) hWaitLedger).trans heW
  have hdWait : wait.deliveries = [] := by
    have h : wait.deliveries = woven.deliveries :=
      ((woven.cast_source a.final_state).cast_parameters_deliveries hParams).trans (woven.cast_source_deliveries a.final_state)
    rw [h,hdW,hdPair]; rfl
  have hBeforeDate : before.time = 656 := bcut.date
  have hQueueMap : Q.map Delivery.succ = sourceTrain 2 0 656 4 21 := by simp [Q,sourceTrain,Delivery.succ]
  have hHead : before.pending = [] ++ (⟨2,0,656⟩ : Delivery 3) :: later := by
    change Q.map Delivery.succ = _
    rw [hQueueMap,sourceTrain_succ]
    norm_num [later]
  let final : Snapshot 3 := {setRaw before 2 0 (some before.time) with pending := later}
  let arrival : Jump route before final := .arrive before ⟨2,0,656⟩ [] later hHead hBeforeDate.symm (relay.cSpan.raw_none 0 0)
  let trace := wait.append (.cons (.jump arrival) (.nil _))
  have hRawA (q : Port) : final.raw 0 q = acut.state.raw 0 q := by
    change (setRaw before 2 0 (some before.time)).raw 0 q = acut.state.raw 0 q
    rw [raw_update_other _ _ _ _ _ _ (Or.inl (by decide))]; rfl
  have hRawB (q : Port) : final.raw 1 q = bcut.state.raw 0 q := by
    change (setRaw before 2 0 (some before.time)).raw 1 q = bcut.state.raw 0 q
    rw [raw_update_other _ _ _ _ _ _ (Or.inl (by decide))]; rfl
  have hRawC : final.raw 2 0 = some final.time := by simp [final,setRaw]
  have hRawCOther (q : Port) (hq : q ≠ 0) : final.raw 2 q = none := by
    change (setRaw before 2 0 (some before.time)).raw 2 q = none
    rw [raw_update_other _ _ _ _ _ _ (Or.inr hq)]
    exact relay.cSpan.raw_none 0 q
  have hGainA (q : Port) : final.x 0 (.z q) = a.final.x 0 (.z q) := by
    have hEnd : a.localCycle.returned.final.x 0 (.z q) = a.final.x 0 (.z q) :=
      (a.localCycle.gains 0 q).trans (a.gains 0 q).symm
    have hOwn := acut.isPrefix.gain_eq_of_final hb.extend_old.extend_old 0 q
      (hEnd.trans (congrFun a.a_values (.z q)))
    exact hOwn.trans (congrFun a.a_values (.z q)).symm
  have hRecA : final.x 0 .b = a.final.x 0 .b := by
    have hEnd : a.localCycle.returned.final.x 0 .b = a.final.x 0 .b :=
      (a.localCycle.recovery 0).trans (a.recovery 0).symm
    have hOwn := acut.isPrefix.recovery_eq_of_final hb.extend_old.extend_old 0
      (hEnd.trans (congrFun a.a_values .b))
    exact hOwn.trans (congrFun a.a_values .b).symm
  have hGainB (q : Port) : final.x 1 (.z q) = a.final.x 1 (.z q) := by
    have hEnd : relay.senderCycle.returned.final.x 0 (.z q) = a.final.x 1 (.z q) :=
      (relay.senderCycle.gains 0 q).trans ((a.gains 1 q).trans (relay.gains 1 q)).symm
    have hOwn := bcut.isPrefix.gain_eq_of_final hb.extend_old.extend_new 0 q
      (hEnd.trans (congrFun a.b_values (.z q)))
    exact hOwn.trans (congrFun a.b_values (.z q)).symm
  have hRecB : final.x 1 .b = a.final.x 1 .b := by
    have hEnd : relay.senderCycle.returned.final.x 0 .b = a.final.x 1 .b :=
      (relay.senderCycle.recovery 0).trans ((a.recovery 1).trans (relay.recovery 1)).symm
    have hOwn := bcut.isPrefix.recovery_eq_of_final hb.extend_old.extend_new 0
      (hEnd.trans (congrFun a.b_values .b))
    exact hOwn.trans (congrFun a.b_values .b).symm
  have hGainC (q : Port) : final.x 2 (.z q) = a.final.x 2 (.z q) := by
    have h : relay.cSpan.final.x 0 (.z q) = w.localWarmup.final.x 0 (.z q) :=
      (relay.cSpan.gains 0 q).trans ((r.fast.gains 0 q).trans (r.fire.gain_preserved 0 q))
    change relay.cSpan.final.x 0 (.z q) = a.final.x 2 (.z q)
    rw [a.gains,relay.gains,r.gains,w.final_state]
    exact h
  have hRecC : final.x 2 .b = a.final.x 2 .b := by
    have h : relay.cSpan.final.x 0 .b = w.localWarmup.final.x 0 .b :=
      (relay.cSpan.recovery 0).trans ((r.fast.recovery 0).trans (r.fire.recovery_preserved 0))
    change relay.cSpan.final.x 0 .b = a.final.x 2 .b
    rw [a.recovery,relay.recovery,r.recovery,w.final_state]
    exact h
  have hGains : ∀ i q, final.x i (.z q) = a.final.x i (.z q) := by
    intro i q; fin_cases i
    · exact hGainA q
    · exact hGainB q
    · exact hGainC q
  have hRecovery : ∀ i, final.x i .b = a.final.x i .b := by
    intro i; fin_cases i
    · exact hRecA
    · exact hRecB
    · exact hRecC
  have hFuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change bcut.state.time < 660 + 4 * (k.val : ℝ)
    rw [bcut.date]
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  have hGuard : BeforeGuards final final.x := by
    constructor
    · intro i
      rcases (show i = (0 : Fin 3) ∨ i = 1 ∨ i = 2 by fin_cases i <;> norm_num) with hi | hi | hi <;> subst i
      · exact acut.before_guards.1 0
      · exact bcut.before_guards.1 0
      · change (match relay.cSpan.final.main 0 with
            | .ready => relay.cSpan.final.x 0 .q < 1
            | .fast => 1 / 4 < relay.cSpan.final.x 0 .q
            | .slow => 1 / 10 < relay.cSpan.final.x 0 .q)
        rw [relay.cSpan.main_slow]
        linarith [relay.cSpan.charge.1]
    · intro i q
      rcases (show i = (0 : Fin 3) ∨ i = 1 ∨ i = 2 by fin_cases i <;> norm_num) with hi | hi | hi <;> subst i
      · exact acut.before_guards.2 0 q
      · exact bcut.before_guards.2 0 q
      · change (match relay.cSpan.final.aux 0 q with
            | .ready => relay.cSpan.final.x 0 (.m q) < 1
            | .mark => 4 / 5 < relay.cSpan.final.x 0 (.m q)
            | .silent => 1 / 10 < relay.cSpan.final.x 0 (.m q)
            | .error => 1 / 40 < relay.cSpan.final.x 0 (.m q))
        rw [relay.cSpan.auxiliary]
        linarith [(relay.cSpan.rest q).2]
  have hComplete : CompleteThrough trace 656 := by
    refine ⟨bcut.date,?_,?_⟩
    · intro u; apply hGuard.no_jump
      · intro i q origin hr
        rcases (show i = (0 : Fin 3) ∨ i = 1 ∨ i = 2 by fin_cases i <;> norm_num) with hi | hi | hi <;> subst i
        · rw [hRawA] at hr
          change bcut.state.time < origin + 1
          rw [bcut.date,← acut.date]
          exact acut.flow.initial_raw_strict 0 q origin hr
        · rw [hRawB] at hr
          exact bcut.flow.initial_raw_strict 0 q origin hr
        · by_cases hq : q = 0
          · subst q
            have ho : origin = final.time := Option.some.inj (hr.symm.trans hRawC)
            rw [ho]; linarith
          · rw [hRawCOther q hq] at hr; contradiction
      · exact hFuture
    · intro d hd
      have hdate : final.time = 656 := bcut.date
      simpa only [hdate] using hFuture d hd
  refine ⟨{
    aContinuation := ae, a_reconstruct := rfl, aCut := acut
    bContinuation := be, b_reconstruct := rfl, bCut := bcut
    cContinuation := ce, c_reconstruct := rfl, before := before, before_state := rfl
    final := final, final_state := rfl, wait := wait, arrival := arrival, execution := trace
    reconstruct := rfl, before_date := hBeforeDate, date := bcut.date, pending := rfl
    a_values := rfl, a_main := rfl, a_aux := fun _ => rfl, a_raw := hRawA
    b_values := rfl, b_main := rfl, b_aux := fun _ => rfl, b_raw := hRawB
    c_values := rfl, c_main_slow := relay.cSpan.main_slow, c_charge := relay.cSpan.charge
    c_auxiliary := fun q => relay.cSpan.auxiliary 0 q, c_rest := relay.cSpan.rest
    c_trained_rest := relay.cSpan.trained_rest, c_raw_active := hRawC, c_raw_other := hRawCOther
    gains := hGains, recovery := hRecovery, emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb a.physical, raw_valid := trace.raw_valid a.raw_valid
    complete := hComplete
  }⟩
  · have hj : arrival.ledger.emissions = [] := rfl
    simp only [trace,Execution.emissions_append,heWait,Execution.ledger,Move.ledger,hj,
      Ledger.add,Ledger.zero,List.nil_append]
  · have hj : arrival.deliveries = [⟨2,0,656⟩] := rfl
    simp only [trace,Execution.deliveries_append,hdWait,Execution.deliveries,Move.deliveries,hj,
      List.nil_append,List.append_nil]

end KernelR.Hybrid
