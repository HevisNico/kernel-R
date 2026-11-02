import KernelR.HybridCadenceFirstWire
import KernelR.HybridCadenceStrongSlowSpan
import KernelR.HybridShortLearnedCycle
import KernelR.HybridNeutralHeadExecutionProduct

/-! The first genuine B relay FIRE and its actual A receipt. B and C retain
the same unfinished physical paths, while the global C queue remains exact. -/
namespace KernelR.Hybrid

/-- Empty-queue coordinate projection for local construction; the global queue
is carried independently by the product, never physically deleted. -/
noncomputable def cadenceRelayLocal (s : Snapshot 3) (i : Fin 3) : Snapshot 1 where
  time := s.time
  x := fun _ => s.x i
  main := fun _ => s.main i
  aux := fun _ => s.aux i
  raw := fun _ => s.raw i
  pending := []

private theorem relay_physical {θ freshB freshC s}
    (hf : PhysicalInvariant (extendParameters (extendParameters θ freshB) freshC) s) :
    PhysicalInvariant (fun _ : Fin 1 => freshB) (cadenceRelayLocal s 1) :=
  ⟨fun _ => hf.region 1,fun _ q => hf.gain_cap 1 q,
    fun _ => hf.recovery_cap 1,fun _ => hf.reserve 1⟩

private theorem relay_snapshot_ext {n} (s u : Snapshot n)
    (ht : s.time = u.time) (hx : s.x = u.x) (hm : s.main = u.main)
    (ha : s.aux = u.aux) (hr : s.raw = u.raw) (hp : s.pending = u.pending) : s = u := by
  cases s; cases u; simp_all only

structure FirstCadenceRelayWire {θ born freshB freshC newbornB newbornC forward backward delay}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    (r : FirstCadenceWire w) where
  senderCycle : ShortLearnedCycle (fun _ : Fin 1 => freshB) (cadenceRelayLocal r.final 1) 2
  cSpan : CadenceStrongSlowSpan r.fast
  cCutF : (cSpan.fromCut r.cutH).BeforeFlowCut senderCycle.fire.final.time
  cCutA : (Execution.cons (.flow cCutF.flow) cCutF.rest).BeforeFlowCut
    (senderCycle.fire.final.time + cascadeBackward senderCycle.fire.final.time)
  bCutA : senderCycle.fast.execution.BeforeFlowCut
    (senderCycle.fire.final.time + cascadeBackward senderCycle.fire.final.time)
  final : Snapshot 3
  execution : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) r.final final
  date : final.time = senderCycle.fire.final.time + cascadeBackward senderCycle.fire.final.time
  window : 6534 / 10 < final.time ∧ final.time < 6544 / 10
  pending : final.pending = sourceTrain 2 0 656 4 21
  a_values : final.x 0 = (quietAt (cadenceRelayLocal r.final 0) final.time).x 0
  a_prepared : PreparedSection final 0
  a_charge : final.x 0 .q = 1 / 10
  a_raw_active : final.raw 0 2 = some final.time
  a_raw_other : ∀ q, q ≠ 2 → final.raw 0 q = none
  b_values : final.x 1 = bCutA.state.x 0
  b_main : final.main 1 = bCutA.state.main 0
  b_aux : ∀ q, final.aux 1 q = bCutA.state.aux 0 q
  b_raw : ∀ q, final.raw 1 q = bCutA.state.raw 0 q
  c_values : final.x 2 = cCutA.state.x 0
  c_main : final.main 2 = cCutA.state.main 0
  c_aux : ∀ q, final.aux 2 q = cCutA.state.aux 0 q
  c_raw : ∀ q, final.raw 2 q = cCutA.state.raw 0 q
  gains : ∀ i q, final.x i (.z q) = r.final.x i (.z q)
  recovery : ∀ i, final.x i .b = r.final.x i .b
  emissions : execution.ledger.emissions = [(1,senderCycle.fire.final.time)]
  deliveries : execution.deliveries = [⟨0,2,final.time⟩]
  physical : PhysicalInvariant (extendParameters (extendParameters θ freshB) freshC) final
  raw_valid : RawValid final
  complete : CompleteThrough execution final.time

theorem first_cadence_relay_wire_exists {θ born freshB freshC newbornB newbornC forward backward delay ε}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward} {w : ConstructedCadenceWarmup c cascadeForward cascadeBackward}
    (r : FirstCadenceWire w)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ cascadeBackward t ∧ cascadeBackward t ≤ 2 / 5) :
    Nonempty (FirstCadenceRelayWire r) := by
  let a := cadenceRelayLocal r.final 0
  let b := cadenceRelayLocal r.final 1
  let Q := sourceTrain (1 : Fin 2) 0 656 4 21
  let route := cadenceRouter cascadeForward cascadeBackward
  let params := extendParameters (extendParameters θ freshB) freshC
  have hB : PreparedSection b 0 :=
    ⟨r.b_prepared.ready,r.b_prepared.charge,r.b_prepared.recovery,r.b_prepared.auxiliary⟩
  have hzB : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ b.x 0 (.z 2) ∧
      b.x 0 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    change Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ r.final.x 1 (.z 2) ∧
      r.final.x 1 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000
    rw [r.gains,w.gains_other 1 2 (Or.inl (by decide)),c.b_gain_target]
    have h := newbornB.gain 2
    simp only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] at h
    constructor <;> linarith [h.1,h.2]
  have hgB := cadence_three_dose_gain_bounds hzB
  obtain ⟨bc⟩ := short_learned_cycle_exists hb.extend_old.extend_new b 2 (relay_physical r.physical)
    (fun _ q origin h => r.raw_valid 1 q origin h) hB
    ⟨hgB.1,by linarith [hgB.2]⟩ r.b_raw_active r.b_raw_other
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  have hzC : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ w.localWarmup.final.x 0 (.z 0) ∧
      w.localWarmup.final.x 0 (.z 0) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [ConstructedCadenceWeakWarmup.final,w.localWarmup.gain_target]
    constructor <;> linarith [w.start.c_gain_low.1,w.start.c_gain_low.2]
  have hgC := cadence_three_dose_gain_bounds hzC
  have hBC : 17999 / 100000 ≤ w.localWarmup.final.x 0 .b ∧
      w.localWarmup.final.x 0 .b ≤ 18001 / 100000 := by
    rw [ConstructedCadenceWeakWarmup.final,w.localWarmup.recovery]
    exact w.start.c_recovery_band
  have hpC : ∀ d ∈ w.localWarmup.final.pending, w.localWarmup.final.time + 4 ≤ d.due := by
    intro d hd
    simp only [ConstructedCadenceWeakWarmup.final] at hd ⊢
    rw [w.localWarmup.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [w.localWarmup.date]
    change 652 + 4 ≤ 656 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨span⟩ := r.fire.cadence_strong_slow_span_exists hb.extend_new r.fast
    w.localWarmup.coordinates hgC.2 hBC hpC
  let ce := span.fromCut r.cutH
  have heC : ce.ledger.emissions = [] := span.fromCut_emissions r.cutH
  have hdC : ce.deliveries = [] := span.fromCut_deliveries r.cutH
  let F := bc.fire.final.time
  let H := F + cascadeBackward F
  have hF : r.final.time + 2 / 5 < F ∧ F < r.final.time + 7 / 10 := bc.fire_bounds
  have hH : 6534 / 10 < H ∧ H < 6544 / 10 := by
    constructor <;> dsimp [H] <;> linarith [r.window.1,r.window.2,hF.1,hF.2,(hdelay F).1,(hdelay F).2]
  have hFH : F < H := by dsimp [H]; linarith [(hdelay F).1]
  have hcStart : r.cutH.state.time = r.final.time := r.cutH.date.trans r.date.symm
  have hcEnd : span.final.time = 656 := by rw [span.date,ConstructedCadenceWeakWarmup.final,w.localWarmup.date]; norm_num
  obtain ⟨cutF⟩ := ce.before_flow_cut_exists F
    (by change r.cutH.state.time ≤ F; rw [hcStart]; linarith [hF.1])
    (by rw [hcEnd]; linarith [hF.2,r.window.2])
  let ctail : Execution (fun _ : Fin 1 => freshC) (fun _ _ => []) cutF.state span.final :=
    .cons (.flow cutF.flow) cutF.rest
  obtain ⟨cutA⟩ := ctail.before_flow_cut_exists H
    (by rw [cutF.date]; exact hFH.le) (by rw [hcEnd]; exact lt_trans hH.2 (by norm_num))
  obtain ⟨bcut⟩ := bc.fast.execution.before_flow_cut_exists H hFH.le
    (by rw [bc.fast.date]; dsimp [H,F]; linarith [(hdelay bc.fire.final.time).2])
  have heCF : cutF.cut.ledger.emissions = [] := (List.append_eq_nil_iff.mp (cutF.emissions.symm.trans heC)).1
  have hdCF : cutF.cut.deliveries = [] := (List.append_eq_nil_iff.mp (cutF.deliveries.symm.trans hdC)).1
  have heCT : ctail.ledger.emissions = [] := (List.append_eq_nil_iff.mp (cutF.emissions.symm.trans heC)).2
  have hdCT : ctail.deliveries = [] := (List.append_eq_nil_iff.mp (cutF.deliveries.symm.trans hdC)).2
  have heCA : cutA.cut.ledger.emissions = [] := (List.append_eq_nil_iff.mp (cutA.emissions.symm.trans heCT)).1
  have hdCA : cutA.cut.deliveries = [] := (List.append_eq_nil_iff.mp (cutA.deliveries.symm.trans hdCT)).1
  have heB : bcut.cut.ledger.emissions = [] := (List.append_eq_nil_iff.mp (bcut.emissions.symm.trans bc.fast.emissions)).1
  have hdB : bcut.cut.deliveries = [] := (List.append_eq_nil_iff.mp (bcut.deliveries.symm.trans bc.fast.deliveries)).1
  have hQ (t : ℝ) (ht : t < 656) : ∀ d ∈ Q, t ≤ d.due := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change t ≤ 656 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  have hParams : prependParameters θ (cBirthPairParameters freshB freshC) = params :=
    cBirthPairParameters_prepend θ freshB freshC
  have haReady : ∀ j, ReadyCoordinates a j := fun _ =>
    ⟨r.a_prepared.ready,r.a_prepared.charge,r.a_prepared.auxiliary⟩
  have haRaw : ∀ j q, a.raw j q = none := fun _ q => r.a_raw_none q
  have haQueue : a.pending = [] := rfl
  obtain ⟨pair,hePair,hdPair⟩ := bc.fire.portBeforeExecution.product_neutral cutF.cut
    hcStart.symm cutF.date.symm bc.fire.portBefore_emissions bc.fire.portBefore_deliveries heCF hdCF
    Q (hQ F (by linarith [hF.2,r.window.2])) (fun _ _ => [])
  obtain ⟨woven,heW,hdW⟩ := pair.prepend_quiet_neutral hePair θ a rfl haReady haRaw haQueue route
  have hSource : (b.product r.cutH.state Q).prependQuiet a = r.final := by
    apply relay_snapshot_ext
    · rfl
    · funext i; fin_cases i
      · rfl
      · rfl
      · exact r.c_values.symm
    · funext i; fin_cases i
      · rfl
      · rfl
      · exact r.c_main.symm
    · funext i q; fin_cases i
      · rfl
      · rfl
      · exact (r.c_aux q).symm
    · funext i q; fin_cases i
      · rfl
      · rfl
      · exact (r.c_raw q).symm
    · rw [r.pending]
      simp [Snapshot.prependQuiet,Snapshot.product,Q,sourceTrain,Delivery.succ]
  let before : Snapshot 3 := (bc.fire.portBefore.product cutF.state Q).prependQuiet (quietAt a F)
  let pre : Execution params route r.final before := (woven.cast_source hSource.symm).cast_parameters hParams
  have hPreLedger : pre.ledger = woven.ledger :=
    ((woven.cast_source hSource.symm).cast_parameters_ledger hParams).trans (woven.cast_source_ledger hSource.symm)
  have hePre : pre.ledger.emissions = [] := (congrArg (fun L : Ledger 3 => L.emissions) hPreLedger).trans heW
  have hdPre : pre.deliveries = [] := by
    have h : pre.deliveries = woven.deliveries :=
      ((woven.cast_source hSource.symm).cast_parameters_deliveries hParams).trans (woven.cast_source_deliveries hSource.symm)
    rw [h,hdW,hdPair]; rfl
  have hroute : route 1 F = [⟨0,2,H⟩] := by
    have hlo : (640 : ℝ) ≤ F := by linarith [hF.1,r.window.1]
    have hhi : F < (780 : ℝ) := by linarith [hF.2,r.window.2]
    simp [route,cadenceRouter,cadenceForwardContact,cadenceReturnContact,Contact.route,Contact.token,hlo,hhi,H]
  let after : Snapshot 3 := {setMain before 1 .fast with pending := before.pending ++ route 1 F}
  let firing : Jump route before after := .fire before 1 (bc.fire.firstSilent.main_ready 0) bc.fire.threshold
  have heFire : firing.ledger.emissions = [(1,F)] := rfl
  have hdFire : firing.deliveries = [] := rfl
  let fireTrace := pre.append (.cons (.jump firing) (.nil _))
  have heFireTrace : fireTrace.ledger.emissions = [(1,F)] := by
    simp only [fireTrace,Execution.emissions_append,hePre,Execution.ledger,Move.ledger,heFire,Ledger.add,Ledger.zero,List.nil_append,List.append_nil]
  have hdFireTrace : fireTrace.deliveries = [] := by
    simp only [fireTrace,Execution.deliveries_append,hdPre,Execution.deliveries,Move.deliveries,hdFire,List.append_nil]
  have haF : ∀ j, ReadyCoordinates (quietAt a F) j := fun j =>
    quietAt_ready_coordinates a j (haReady j) (by change r.final.time ≤ F; linarith [hF.1])
  obtain ⟨postPair,hePostPair,hdPostPair⟩ := bcut.cut.product_neutral cutA.cut
    cutF.date.symm (bcut.date.trans cutA.date.symm) heB hdB heCA hdCA
    Q (by intro d hd; rw [bcut.date]; exact hQ H (lt_trans hH.2 (by norm_num)) d hd) (fun _ _ => [])
  obtain ⟨postW,hePostW,hdPostW⟩ := postPair.prepend_quiet_neutral hePostPair θ (quietAt a F) rfl haF haRaw haQueue route
  let post := postW.cast_parameters hParams
  have hePost : post.ledger.emissions = [] := by rw [Execution.cast_parameters_ledger]; exact hePostW
  have hdPost : post.deliveries = [] := by rw [Execution.cast_parameters_deliveries,hdPostW,hdPostPair]; rfl
  obtain ⟨framed,hFrame,hFrameDel⟩ := post.appendFuture_neutral hePost [⟨0,2,H⟩]
    (by intro d hd; have he : d = (⟨0,2,H⟩ : Delivery 3) := List.mem_singleton.mp hd
        subst d; exact bcut.date.le)
  have hAfter : after = appendPending ((bc.fire.final.product cutF.state Q).prependQuiet (quietAt a F)) [⟨0,2,H⟩] := by
    dsimp [after,before,appendPending]
    rw [bc.fire.port_final_empty,Snapshot.product_setMain_left,Snapshot.prependQuiet_setMain,hroute]
    rfl
  let aH := quietAt (quietAt a F) bcut.state.time
  let beforeWire : Snapshot 3 := appendPending ((bcut.state.product cutA.state Q).prependQuiet aH) [⟨0,2,H⟩]
  let wireTrace : Execution params route after beforeWire := framed.cast_source hAfter
  have hWireLedger : wireTrace.ledger = post.ledger := (framed.cast_source_ledger hAfter).trans hFrame
  have heWire : wireTrace.ledger.emissions = [] :=
    (congrArg (fun L : Ledger 3 => L.emissions) hWireLedger).trans hePost
  have hdWire : wireTrace.deliveries = [] :=
    (framed.cast_source_deliveries hAfter).trans (hFrameDel.trans hdPost)
  let Qglobal := Q.map Delivery.succ
  let final : Snapshot 3 := {setRaw beforeWire 0 2 (some beforeWire.time) with pending := Qglobal ++ []}
  let arrival : Jump route beforeWire final := .arrive beforeWire ⟨0,2,H⟩ Qglobal [] rfl bcut.date.symm (haRaw 0 2)
  have heArrival : arrival.ledger.emissions = [] := rfl
  have hdArrival : arrival.deliveries = [⟨0,2,H⟩] := rfl
  let trace : Execution params route r.final final := fireTrace.append (wireTrace.append (.cons (.jump arrival) (.nil _)))
  have hAvalues : final.x 0 = (quietAt a final.time).x 0 := by
    change aH.x 0 = (quietAt a bcut.state.time).x 0
    dsimp [aH]; rw [quietAt_quietAt]
  have hAready : ReadyCoordinates aH 0 := quietAt_ready_coordinates (quietAt a F) 0 (haF 0)
    (by change F ≤ bcut.state.time; rw [bcut.date]; exact hFH.le)
  have hAprepared : PreparedSection final 0 :=
    ⟨hAready.ready,hAready.charge,r.a_prepared.recovery,hAready.auxiliary⟩
  have hAcharge : final.x 0 .q = 1 / 10 := by
    rw [hAvalues]
    change relax (1 / 2) (1 / 10) (r.final.x 0 .q) r.final.time final.time = _
    rw [r.a_charge]; simp [relax]
  have hRawA : final.raw 0 2 = some final.time := by simp [final,setRaw]
  have hRawAOther : ∀ q, q ≠ 2 → final.raw 0 q = none := by
    intro q hq
    change (setRaw beforeWire 0 2 (some beforeWire.time)).raw 0 q = none
    rw [raw_update_other _ _ _ _ _ _ (Or.inr hq)]; exact haRaw 0 q
  have hRawB : ∀ q, final.raw 1 q = bcut.state.raw 0 q := by
    intro q
    change (setRaw beforeWire 0 2 (some beforeWire.time)).raw 1 q = bcut.state.raw 0 q
    rw [raw_update_other _ _ _ _ _ _ (Or.inl (by decide))]; rfl
  have hRawC : ∀ q, final.raw 2 q = cutA.state.raw 0 q := by
    intro q
    change (setRaw beforeWire 0 2 (some beforeWire.time)).raw 2 q = cutA.state.raw 0 q
    rw [raw_update_other _ _ _ _ _ _ (Or.inl (by decide))]; rfl
  have hGainB (q : Port) : final.x 1 (.z q) = r.final.x 1 (.z q) :=
    (bcut.isPrefix.gain_eq_of_final hb.extend_old.extend_new 0 q (bc.fast.gains 0 q)).trans
      (bc.fire.gain_preserved 0 q)
  have hRecB : final.x 1 .b = r.final.x 1 .b :=
    (bcut.isPrefix.recovery_eq_of_final hb.extend_old.extend_new 0 (bc.fast.recovery 0)).trans
      (bc.fire.recovery_preserved 0)
  have hGainC (q : Port) : final.x 2 (.z q) = r.final.x 2 (.z q) := by
    have hEnd := span.fromCut_gains hb.extend_new r.cutH q
    have hF := cutF.isPrefix.gain_eq_of_final hb.extend_new 0 q hEnd
    have hA := cutA.isPrefix.gain_eq_of_final hb.extend_new 0 q (hEnd.trans hF.symm)
    exact (hA.trans hF).trans (congrFun r.c_values (.z q)).symm
  have hRecC : final.x 2 .b = r.final.x 2 .b := by
    have hEnd := span.fromCut_recovery hb.extend_new r.cutH
    have hF := cutF.isPrefix.recovery_eq_of_final hb.extend_new 0 hEnd
    have hA := cutA.isPrefix.recovery_eq_of_final hb.extend_new 0 (hEnd.trans hF.symm)
    exact (hA.trans hF).trans (congrFun r.c_values .b).symm
  have hGains : ∀ i q, final.x i (.z q) = r.final.x i (.z q) := by
    intro i q; fin_cases i
    · change final.x 0 (.z q) = r.final.x 0 (.z q); rw [hAvalues]; rfl
    · exact hGainB q
    · exact hGainC q
  have hRecovery : ∀ i, final.x i .b = r.final.x i .b := by
    intro i; fin_cases i
    · change final.x 0 .b = r.final.x 0 .b; rw [hAvalues]; rfl
    · exact hRecB
    · exact hRecC
  have hPending : final.pending = sourceTrain 2 0 656 4 21 := by
    change Q.map Delivery.succ ++ [] = _
    simp [Q,sourceTrain,Delivery.succ]
  have hFuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd; rw [hPending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change bcut.state.time < 656 + 4 * (k.val : ℝ)
    rw [bcut.date]
    nlinarith [hH.2,Nat.cast_nonneg (α := ℝ) k.val]
  have hGuard : BeforeGuards final final.x := by
    constructor
    · intro i
      rcases (show i = (0 : Fin 3) ∨ i = 1 ∨ i = 2 by fin_cases i <;> norm_num) with hi | hi | hi <;> subst i
      · rw [hAprepared.ready,hAcharge]; norm_num
      · exact bcut.before_guards.1 0
      · exact cutA.before_guards.1 0
    · intro i q
      rcases (show i = (0 : Fin 3) ∨ i = 1 ∨ i = 2 by fin_cases i <;> norm_num) with hi | hi | hi <;> subst i
      · rw [(hAprepared.auxiliary q).1]; linarith [(hAprepared.auxiliary q).2.2]
      · exact bcut.before_guards.2 0 q
      · exact cutA.before_guards.2 0 q
  have hComplete : CompleteThrough trace final.time := by
    refine ⟨rfl,?_,hFuture⟩
    intro u; apply hGuard.no_jump
    · intro i q origin hr
      rcases (show i = (0 : Fin 3) ∨ i = 1 ∨ i = 2 by fin_cases i <;> norm_num) with hi | hi | hi <;> subst i
      · by_cases hq : q = 2
        · subst q
          have ho : origin = final.time := Option.some.inj (hr.symm.trans hRawA)
          rw [ho]; linarith
        · rw [hRawAOther q hq] at hr; contradiction
      · rw [hRawB] at hr; exact bcut.flow.initial_raw_strict 0 q origin hr
      · rw [hRawC] at hr
        have h := cutA.flow.initial_raw_strict 0 q origin hr
        change bcut.state.time < origin + 1
        rw [bcut.date,← cutA.date]; exact h
    · exact hFuture
  refine ⟨{
    senderCycle := bc, cSpan := span, cCutF := cutF, cCutA := cutA, bCutA := bcut
    final := final, execution := trace, date := bcut.date, window := ?_, pending := hPending
    a_values := hAvalues, a_prepared := hAprepared, a_charge := hAcharge
    a_raw_active := hRawA, a_raw_other := hRawAOther
    b_values := rfl, b_main := rfl, b_aux := fun _ => rfl, b_raw := hRawB
    c_values := rfl, c_main := rfl, c_aux := fun _ => rfl, c_raw := hRawC
    gains := hGains, recovery := hRecovery, emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb r.physical, raw_valid := trace.raw_valid r.raw_valid
    complete := hComplete
  }⟩
  · change 6534 / 10 < bcut.state.time ∧ bcut.state.time < 6544 / 10
    rw [bcut.date]; exact hH
  · rw [Execution.emissions_append,heFireTrace,Execution.emissions_append,heWire]
    simp only [Execution.ledger,Move.ledger,heArrival,Ledger.add,Ledger.zero,List.append_nil]
    rfl
  · rw [Execution.deliveries_append,hdFireTrace,Execution.deliveries_append,hdWire]
    simp only [Execution.deliveries,Move.deliveries,hdArrival,List.nil_append,List.append_nil]
    change [⟨0,2,H⟩] = ([⟨0,2,bcut.state.time⟩] : List (Delivery 3))
    rw [bcut.date]

end KernelR.Hybrid
