import KernelR.HybridCadenceFirstRelayWire

/-! A's first actual cadence FIRE. Its own learned response is woven with
B's retained FAST/return path and C's retained first SLOW span. -/
namespace KernelR.Hybrid

private theorem a_fire_snapshot_ext {n} (s u : Snapshot n)
    (ht : s.time = u.time) (hx : s.x = u.x) (hm : s.main = u.main)
    (ha : s.aux = u.aux) (hr : s.raw = u.raw) (hp : s.pending = u.pending) : s = u := by
  cases s; cases u; simp_all only

structure FirstCadenceAFire {θ born freshB freshC newbornB newbornC forward backward delay}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    {r : FirstCadenceWire w} (relay : FirstCadenceRelayWire r) where
  localCycle : ShortLearnedCycle θ (cadenceRelayLocal relay.final 0) 2
  bContinuation : Execution (fun _ : Fin 1 => freshB) (fun _ _ => []) relay.bCutA.state relay.senderCycle.returned.final
  b_reconstruct : bContinuation = (Execution.cons (.flow relay.bCutA.flow) relay.bCutA.rest).append
    relay.senderCycle.returned.execution
  bCut : bContinuation.BeforeFlowCut localCycle.fire.final.time
  cContinuation : Execution (fun _ : Fin 1 => freshC) (fun _ _ => []) relay.cCutA.state relay.cSpan.final
  c_reconstruct : cContinuation = Execution.cons (.flow relay.cCutA.flow) relay.cCutA.rest
  cCut : cContinuation.BeforeFlowCut localCycle.fire.final.time
  before : Snapshot 3
  final : Snapshot 3
  before_state : before = (bCut.state.product cCut.state (sourceTrain 1 0 656 4 21)).prependQuiet localCycle.fire.portBefore
  final_state : final = (bCut.state.product cCut.state (sourceTrain 1 0 656 4 21)).prependQuiet localCycle.fire.final
  span : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) relay.final before
  fire : Jump (cadenceRouter cascadeForward cascadeBackward) before final
  execution : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) relay.final final
  reconstruct : execution = span.append (.cons (.jump fire) (.nil _))
  date : final.time = localCycle.fire.final.time
  window : 6538 / 10 < final.time ∧ final.time < 6551 / 10
  pending : final.pending = sourceTrain 2 0 656 4 21
  a_values : final.x 0 = localCycle.fire.final.x 0
  a_main_fast : final.main 0 = .fast
  a_charge : final.x 0 .q = 1
  a_aux : ∀ q, final.aux 0 q = localCycle.fire.final.aux 0 q
  a_raw : ∀ q, final.raw 0 q = localCycle.fire.final.raw 0 q
  b_values : final.x 1 = bCut.state.x 0
  b_main : final.main 1 = bCut.state.main 0
  b_aux : ∀ q, final.aux 1 q = bCut.state.aux 0 q
  b_raw : ∀ q, final.raw 1 q = bCut.state.raw 0 q
  c_values : final.x 2 = cCut.state.x 0
  c_main : final.main 2 = cCut.state.main 0
  c_aux : ∀ q, final.aux 2 q = cCut.state.aux 0 q
  c_raw : ∀ q, final.raw 2 q = cCut.state.raw 0 q
  gains : ∀ i q, final.x i (.z q) = relay.final.x i (.z q)
  recovery : ∀ i, final.x i .b = relay.final.x i .b
  emissions : execution.ledger.emissions = [(0,localCycle.fire.final.time)]
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant (extendParameters (extendParameters θ freshB) freshC) final
  raw_valid : RawValid final
  complete : CompleteThrough execution final.time

/-- The original birth band determines A's own acquired gain. Every new local
response, retained-path cut, global interleaving and A FIRE is constructed. -/
theorem first_cadence_a_fire_exists {θ born freshB freshC newbornB newbornC forward backward delay ε}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    {r : FirstCadenceWire w} (relay : FirstCadenceRelayWire r)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hborn : BirthState born) : Nonempty (FirstCadenceAFire relay) := by
  let a := cadenceRelayLocal relay.final 0
  let Q := sourceTrain (1 : Fin 2) 0 656 4 21
  let route := cadenceRouter cascadeForward cascadeBackward
  let params : Fin 3 → Parameters := extendParameters (extendParameters θ freshB) freshC
  have hA : PreparedSection a 0 :=
    ⟨relay.a_prepared.ready,relay.a_prepared.charge,relay.a_prepared.recovery,relay.a_prepared.auxiliary⟩
  have hfA : PhysicalInvariant θ a := by
    refine ⟨fun _ => relay.physical.region 0,?_,fun _ => relay.physical.recovery_cap 0,fun _ => relay.physical.reserve 0⟩
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact relay.physical.gain_cap 0 q
  have hvA : RawValid a := fun _ q origin h => relay.raw_valid 0 q origin h
  have hzA : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ a.x 0 (.z 2) ∧
      a.x 0 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    change Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ relay.final.x 0 (.z 2) ∧
      relay.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000
    rw [relay.gains,r.gains,w.gains_other 0 2 (Or.inl (by decide)),c.a_gain_target]
    have h := ((hborn.2.2 0).2.2.2.2 (2 : Port)).1
    simp only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] at h
    constructor <;> linarith [h.1,h.2]
  have hgA := cadence_three_dose_gain_bounds hzA
  obtain ⟨ac⟩ := short_learned_cycle_exists hb.extend_old.extend_old a 2 hfA hvA hA
    ⟨hgA.1,by linarith [hgA.2]⟩ relay.a_raw_active relay.a_raw_other
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let F := ac.fire.final.time
  have hF : relay.final.time + 2 / 5 < F ∧ F < relay.final.time + 7 / 10 := ac.fire_bounds
  have hWindow : 6538 / 10 < F ∧ F < 6551 / 10 := by
    constructor <;> linarith [relay.window.1,relay.window.2,hF.1,hF.2]
  let bFastTail : Execution (fun _ : Fin 1 => freshB) (fun _ _ => []) relay.bCutA.state relay.senderCycle.fast.final :=
    .cons (.flow relay.bCutA.flow) relay.bCutA.rest
  let be := bFastTail.append relay.senderCycle.returned.execution
  have heBFast : bFastTail.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (relay.bCutA.emissions.symm.trans relay.senderCycle.fast.emissions)).2
  have hdBFast : bFastTail.deliveries = [] :=
    (List.append_eq_nil_iff.mp (relay.bCutA.deliveries.symm.trans relay.senderCycle.fast.deliveries)).2
  have heB : be.ledger.emissions = [] := by
    rw [Execution.emissions_append,heBFast,relay.senderCycle.returned.emissions]
    rfl
  have hdB : be.deliveries = [] := by
    rw [Execution.deliveries_append,hdBFast,relay.senderCycle.returned.deliveries]
    rfl
  let ce : Execution (fun _ : Fin 1 => freshC) (fun _ _ => []) relay.cCutA.state relay.cSpan.final :=
    .cons (.flow relay.cCutA.flow) relay.cCutA.rest
  have heCT : (Execution.cons (.flow relay.cCutF.flow) relay.cCutF.rest).ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (relay.cCutF.emissions.symm.trans (relay.cSpan.fromCut_emissions r.cutH))).2
  have hdCT : (Execution.cons (.flow relay.cCutF.flow) relay.cCutF.rest).deliveries = [] :=
    (List.append_eq_nil_iff.mp (relay.cCutF.deliveries.symm.trans (relay.cSpan.fromCut_deliveries r.cutH))).2
  have heC : ce.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (relay.cCutA.emissions.symm.trans heCT)).2
  have hdC : ce.deliveries = [] :=
    (List.append_eq_nil_iff.mp (relay.cCutA.deliveries.symm.trans hdCT)).2
  have hBstart : relay.bCutA.state.time = relay.final.time := relay.bCutA.date.trans relay.date.symm
  have hCstart : relay.cCutA.state.time = relay.final.time := relay.cCutA.date.trans relay.date.symm
  have hBend : F < relay.senderCycle.returned.final.time := by
    rw [relay.senderCycle.date]
    change F < r.final.time + 69 / 10
    linarith [r.window.1,hWindow.2]
  have hCend : relay.cSpan.final.time = 656 := by
    rw [relay.cSpan.date]
    have ht : w.localWarmup.final.time = 652 := w.localWarmup.date
    rw [ht]
    norm_num
  obtain ⟨bcut⟩ := be.before_flow_cut_exists F
    (by rw [hBstart]; linarith [hF.1]) hBend
  obtain ⟨ccut⟩ := ce.before_flow_cut_exists F
    (by rw [hCstart]; linarith [hF.1]) (by rw [hCend]; linarith [hWindow.2])
  have heBCut : bcut.cut.ledger.emissions = [] := (List.append_eq_nil_iff.mp (bcut.emissions.symm.trans heB)).1
  have hdBCut : bcut.cut.deliveries = [] := (List.append_eq_nil_iff.mp (bcut.deliveries.symm.trans hdB)).1
  have heCCut : ccut.cut.ledger.emissions = [] := (List.append_eq_nil_iff.mp (ccut.emissions.symm.trans heC)).1
  have hdCCut : ccut.cut.deliveries = [] := (List.append_eq_nil_iff.mp (ccut.deliveries.symm.trans hdC)).1
  have hQ : ∀ d ∈ Q, bcut.state.time ≤ d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [bcut.date]
    change F ≤ 656 + 4 * (k.val : ℝ)
    nlinarith [hWindow.2,Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨pair,hePair,hdPair⟩ := bcut.cut.product_neutral ccut.cut
    (hBstart.trans hCstart.symm) (bcut.date.trans ccut.date.symm) heBCut hdBCut heCCut hdCCut
    Q hQ (fun _ _ => [])
  obtain ⟨woven,heW,hdW⟩ := pair.prepend_neutral ac.fire.portBeforeExecution hBstart bcut.date
    hePair ac.fire.portBefore_emissions ac.fire.portBefore_deliveries rfl route
  have hSource : (relay.bCutA.state.product relay.cCutA.state Q).prependQuiet a = relay.final := by
    apply a_fire_snapshot_ext
    · exact hBstart
    · funext i; fin_cases i
      · rfl
      · exact relay.b_values.symm
      · exact relay.c_values.symm
    · funext i; fin_cases i
      · rfl
      · exact relay.b_main.symm
      · exact relay.c_main.symm
    · funext i q; fin_cases i
      · rfl
      · exact (relay.b_aux q).symm
      · exact (relay.c_aux q).symm
    · funext i q; fin_cases i
      · rfl
      · exact (relay.b_raw q).symm
      · exact (relay.c_raw q).symm
    · change Q.map Delivery.succ = relay.final.pending
      rw [relay.pending]
      simp [Q,sourceTrain,Delivery.succ]
  let before : Snapshot 3 := (bcut.state.product ccut.state Q).prependQuiet ac.fire.portBefore
  let final : Snapshot 3 := (bcut.state.product ccut.state Q).prependQuiet ac.fire.final
  have hParams : prependParameters θ (cBirthPairParameters freshB freshC) = params :=
    cBirthPairParameters_prepend θ freshB freshC
  let span : Execution params route relay.final before :=
    (woven.cast_source hSource.symm).cast_parameters hParams
  have hSpanLedger : span.ledger = woven.ledger :=
    ((woven.cast_source hSource.symm).cast_parameters_ledger hParams).trans (woven.cast_source_ledger hSource.symm)
  have heSpan : span.ledger.emissions = [] :=
    (congrArg (fun L : Ledger 3 => L.emissions) hSpanLedger).trans heW
  have hdSpan : span.deliveries = [] := by
    have h : span.deliveries = woven.deliveries :=
      ((woven.cast_source hSource.symm).cast_parameters_deliveries hParams).trans (woven.cast_source_deliveries hSource.symm)
    rw [h,hdW,hdPair]
    rfl
  have hRouteA (t : ℝ) : route 0 t = [] := by
    simp [route,cadenceRouter,cadenceForwardContact,cadenceReturnContact,Contact.route]
  have hAfter : final = {setMain before 0 .fast with pending := before.pending ++ route 0 before.time} := by
    dsimp [final,before]
    rw [ac.fire.port_final_empty,Snapshot.prependQuiet_setMain_head,hRouteA]
    rfl
  let fire : Jump route before final := hAfter.symm ▸ Jump.fire before 0 (ac.fire.firstSilent.main_ready 0) ac.fire.threshold
  have heFire : fire.ledger.emissions = [(0,F)] := by
    have h := fire.ready_main_departure_emission 0 (ac.fire.firstSilent.main_ready 0)
      (by have h : final.main 0 = .fast := ac.fire.main_fast; rw [h]; decide)
    change fire.ledger.emissions = [(0,bcut.state.time)] at h
    rw [bcut.date] at h
    exact h
  have hdFire : fire.deliveries = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have h := fire.no_emissions_of_delivery d hd
    rw [heFire] at h
    contradiction
  let trace : Execution params route relay.final final := span.append (.cons (.jump fire) (.nil _))
  have hBFinalGain (q : Port) : relay.senderCycle.returned.final.x 0 (.z q) = relay.bCutA.state.x 0 (.z q) := by
    have h := relay.bCutA.isPrefix.gain_eq_of_final hb.extend_old.extend_new 0 q (relay.senderCycle.fast.gains 0 q)
    exact (relay.senderCycle.returned.gains 0 q).trans ((relay.senderCycle.fast.gains 0 q).trans h.symm)
  have hBFinalRec : relay.senderCycle.returned.final.x 0 .b = relay.bCutA.state.x 0 .b := by
    have h := relay.bCutA.isPrefix.recovery_eq_of_final hb.extend_old.extend_new 0 (relay.senderCycle.fast.recovery 0)
    exact (relay.senderCycle.returned.recovery 0).trans ((relay.senderCycle.fast.recovery 0).trans h.symm)
  have hCFinalGain (q : Port) : relay.cSpan.final.x 0 (.z q) = relay.cCutA.state.x 0 (.z q) := by
    have h0 := relay.cSpan.fromCut_gains hb.extend_new r.cutH q
    have h1 := relay.cCutF.isPrefix.gain_eq_of_final hb.extend_new 0 q h0
    have hend : relay.cSpan.final.x 0 (.z q) = relay.cCutF.state.x 0 (.z q) := h0.trans h1.symm
    have h2 := relay.cCutA.isPrefix.gain_eq_of_final hb.extend_new 0 q hend
    exact hend.trans h2.symm
  have hCFinalRec : relay.cSpan.final.x 0 .b = relay.cCutA.state.x 0 .b := by
    have h0 := relay.cSpan.fromCut_recovery hb.extend_new r.cutH
    have h1 := relay.cCutF.isPrefix.recovery_eq_of_final hb.extend_new 0 h0
    have hend : relay.cSpan.final.x 0 .b = relay.cCutF.state.x 0 .b := h0.trans h1.symm
    have h2 := relay.cCutA.isPrefix.recovery_eq_of_final hb.extend_new 0 hend
    exact hend.trans h2.symm
  have hGains : ∀ i q, final.x i (.z q) = relay.final.x i (.z q) := by
    intro i q; fin_cases i
    · exact ac.fire.gain_preserved 0 q
    · exact (bcut.isPrefix.gain_eq_of_final hb.extend_old.extend_new 0 q (hBFinalGain q)).trans
        (congrFun relay.b_values (.z q)).symm
    · exact (ccut.isPrefix.gain_eq_of_final hb.extend_new 0 q (hCFinalGain q)).trans
        (congrFun relay.c_values (.z q)).symm
  have hRecovery : ∀ i, final.x i .b = relay.final.x i .b := by
    intro i; fin_cases i
    · exact ac.fire.recovery_preserved 0
    · exact (bcut.isPrefix.recovery_eq_of_final hb.extend_old.extend_new 0 hBFinalRec).trans
        (congrFun relay.b_values .b).symm
    · exact (ccut.isPrefix.recovery_eq_of_final hb.extend_new 0 hCFinalRec).trans
        (congrFun relay.c_values .b).symm
  have hPending : final.pending = sourceTrain 2 0 656 4 21 := by
    change Q.map Delivery.succ = _
    simp [Q,sourceTrain,Delivery.succ]
  have hFuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    rw [hPending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change bcut.state.time < 656 + 4 * (k.val : ℝ)
    rw [bcut.date]
    nlinarith [hWindow.2,Nat.cast_nonneg (α := ℝ) k.val]
  have hCapA : CadenceReadyCoordinates a 0 (3 / 10) :=
    ⟨hA.ready,⟨hA.charge.1,by linarith [hA.charge.2]⟩,hA.auxiliary⟩
  have hGuard : @BeforeGuards 3 final final.x := by
    constructor
    · intro i; fin_cases i
      · change match ac.fire.final.main 0 with
          | .ready => ac.fire.final.x 0 .q < 1
          | .fast => 1 / 4 < ac.fire.final.x 0 .q
          | .slow => 1 / 10 < ac.fire.final.x 0 .q
        rw [ac.fire.main_fast,ac.fire.charge]; norm_num
      · exact bcut.before_guards.1 0
      · exact ccut.before_guards.1 0
    · intro i q; fin_cases i
      · by_cases hq : q = 2
        · subst q
          change match ac.fire.final.aux 0 2 with
            | .ready => ac.fire.final.x 0 (.m 2) < 1
            | .mark => 4 / 5 < ac.fire.final.x 0 (.m 2)
            | .silent => 1 / 10 < ac.fire.final.x 0 (.m 2)
            | .error => 1 / 40 < ac.fire.final.x 0 (.m 2)
          rw [ac.fire.aux_silent]
          exact ac.fire.sensor_above_floor
        · have hm : final.aux 0 q = .ready := ac.fire.aux_other 0 q (Or.inr hq)
          change (match final.aux 0 q with
            | .ready => final.x 0 (.m q) < 1
            | .mark => 4 / 5 < final.x 0 (.m q)
            | .silent => 1 / 10 < final.x 0 (.m q)
            | .error => 1 / 40 < final.x 0 (.m q))
          rw [hm]
          have h := ac.fire.cadence_residual_other_rest hCapA relay.a_raw_other q hq
          change ac.fire.final.x 0 (.m q) < 1
          linarith [h.2]
      · exact bcut.before_guards.2 0 q
      · exact ccut.before_guards.2 0 q
  have hComplete : CompleteThrough trace final.time := by
    refine ⟨rfl,?_,hFuture⟩
    intro u; apply hGuard.no_jump
    · intro i q origin hr; fin_cases i
      · change ac.fire.final.raw 0 q = some origin at hr
        by_cases hq : q = 2
        · subst q
          have ho : origin = a.time := Option.some.inj (hr.symm.trans ac.fire.raw_active)
          change bcut.state.time < origin + 1
          rw [bcut.date,ho]
          change F < relay.final.time + 1
          linarith [hF.2]
        · rw [ac.fire.raw_other 0 q (Or.inr hq)] at hr; contradiction
      · change bcut.state.raw 0 q = some origin at hr
        exact bcut.flow.initial_raw_strict 0 q origin hr
      · change ccut.state.raw 0 q = some origin at hr
        change bcut.state.time < origin + 1
        rw [bcut.date,← ccut.date]
        exact ccut.flow.initial_raw_strict 0 q origin hr
    · exact hFuture
  refine ⟨{
    localCycle := ac, bContinuation := be, b_reconstruct := rfl, bCut := bcut
    cContinuation := ce, c_reconstruct := rfl, cCut := ccut
    before := before, final := final, before_state := rfl, final_state := rfl
    span := span, fire := fire, execution := trace, reconstruct := rfl
    date := bcut.date, window := ?_, pending := hPending
    a_values := rfl, a_main_fast := ac.fire.main_fast, a_charge := ac.fire.charge
    a_aux := fun _ => rfl, a_raw := fun _ => rfl
    b_values := rfl, b_main := rfl, b_aux := fun _ => rfl, b_raw := fun _ => rfl
    c_values := rfl, c_main := rfl, c_aux := fun _ => rfl, c_raw := fun _ => rfl
    gains := hGains, recovery := hRecovery, emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb relay.physical
    raw_valid := trace.raw_valid relay.raw_valid, complete := hComplete
  }⟩
  · change 6538 / 10 < bcut.state.time ∧ bcut.state.time < 6551 / 10
    rw [bcut.date]
    exact hWindow
  · rw [Execution.emissions_append,heSpan]
    change [] ++ (fire.ledger.emissions ++ []) = _
    rw [heFire]
    rfl
  · rw [Execution.deliveries_append,hdSpan]
    change [] ++ (fire.deliveries ++ []) = []
    rw [hdFire]
    rfl

end KernelR.Hybrid
