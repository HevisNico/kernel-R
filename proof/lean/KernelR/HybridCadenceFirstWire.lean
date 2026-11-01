import KernelR.HybridBirthCadenceWeakWarmup
import KernelR.HybridCadenceFirstStrongFireExistence
import KernelR.HybridFirstReceiverFire
import KernelR.HybridNeutralFutureFrame
import KernelR.HybridQuietLeftWireArrival
import KernelR.HybridPrefixStableMemory

/-! The first cadence C FIRE issues a real C-to-B wire. Only the retained
post-FIRE FAST path is framed with that already-issued token, in queue order. -/
namespace KernelR.Hybrid

structure FirstCadenceWire {θ born freshB freshC newbornB newbornC forward backward delay}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward}
    (w : ConstructedCadenceWarmup c cascadeForward cascadeBackward) where
  fire : FirstLearnedFire (fun _ : Fin 1 => freshC) (fun _ _ => []) w.localWarmup.final 0 0
  fast : PortFastCompletion (fun _ : Fin 1 => freshC) (fun _ _ => []) fire.final 0
  cutH : fast.execution.BeforeFlowCut (fire.final.time + cascadeForward fire.final.time)
  final : Snapshot 3
  execution : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) w.final final
  date : final.time = fire.final.time + cascadeForward fire.final.time
  window : 6527 / 10 < final.time ∧ final.time < 6533 / 10
  pending : final.pending = sourceTrain 2 0 656 4 21
  a_values : final.x 0 = (quietAt w.start.quietA final.time).x 0
  a_prepared : PreparedSection final 0
  a_charge : final.x 0 .q = 1 / 10
  a_raw_none : ∀ q, final.raw 0 q = none
  b_values : final.x 1 = (quietAt w.start.quietB final.time).x 0
  b_prepared : PreparedSection final 1
  b_charge : final.x 1 .q = 1 / 10
  b_raw_active : final.raw 1 2 = some final.time
  b_raw_other : ∀ q, q ≠ 2 → final.raw 1 q = none
  c_values : final.x 2 = cutH.state.x 0
  c_main : final.main 2 = cutH.state.main 0
  c_aux : ∀ q, final.aux 2 q = cutH.state.aux 0 q
  c_raw : ∀ q, final.raw 2 q = cutH.state.raw 0 q
  gains : ∀ i q, final.x i (.z q) = w.final.x i (.z q)
  recovery : ∀ i, final.x i .b = w.final.x i .b
  emissions : execution.ledger.emissions = [(2,fire.final.time)]
  deliveries : execution.deliveries = [⟨1,2,final.time⟩]
  physical : PhysicalInvariant (extendParameters (extendParameters θ freshB) freshC) final
  raw_valid : RawValid final
  complete : CompleteThrough execution final.time

/-- The weak warmup's real carried charge constructs C's threshold. Quiet A/B
are woven only before that actual FIRE and along the retained FAST prefix;
the resulting source equality identifies the true appended wire token. -/
theorem first_cadence_wire_exists {θ born freshB freshC newbornB newbornC forward backward delay ε}
    {c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay}
    {cascadeForward cascadeBackward}
    (w : ConstructedCadenceWarmup c cascadeForward cascadeBackward)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ cascadeForward t ∧ cascadeForward t ≤ 2 / 5) :
    Nonempty (FirstCadenceWire w) := by
  let s := w.localWarmup.final
  let a := quietAt w.start.quietA s.time
  let b := quietAt w.start.quietB s.time
  let route := cadenceRouter cascadeForward cascadeBackward
  let params : Fin 3 → Parameters := extendParameters (extendParameters θ freshB) freshC
  have hs : s.time = 652 := w.localWarmup.date
  have hQ : s.pending = sourceTrain 0 0 656 4 21 := w.localWarmup.pending
  have hcap : CadenceReadyCoordinates s 0 (3 / 10) := w.localWarmup.coordinates
  have hzOwn : s.x 0 (.z 0) = w.start.sC.x 0 (.z 0) + 9 / 5 := w.localWarmup.gain_target
  have hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z 0) ∧
      s.x 0 (.z 0) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [hzOwn]
    constructor <;> linarith [w.start.c_gain_low.1,w.start.c_gain_low.2]
  have hg := cadence_three_dose_gain_bounds hz
  have hFuture : ∀ d ∈ s.pending, s.time + 4 ≤ d.due := by
    intro d hd
    rw [hQ] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [hs]
    change 652 + 4 ≤ 656 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨fire⟩ := cadence_first_strong_fire_exists hb.extend_new s 0
    w.localWarmup.physical w.localWarmup.raw_valid hcap hg w.localWarmup.raw_active
    w.localWarmup.raw_other hFuture
  obtain ⟨fast⟩ := fire.cadence_residual_fast_completion_exists hb.extend_new hcap hg.2
    w.localWarmup.raw_other hFuture
  let F := fire.final.time
  let H := F + cascadeForward F
  have hF : (652 : ℝ) + 2 / 5 < F ∧ F < 652 + 9 / 10 := by
    simpa only [hs] using fire.cadence_residual_window hcap hg.2
  have hH : 6527 / 10 < H ∧ H < 6533 / 10 := by
    constructor <;> dsimp [H] <;> linarith [(hdelay F).1,(hdelay F).2]
  have hFH : F < H := by dsimp [H]; linarith [(hdelay F).1]
  have haReady : ∀ j, ReadyCoordinates a j := fun j =>
    quietAt_ready_coordinates w.start.quietA j (w.start.quiet_a_prepared j).ready_coordinates
      (by rw [w.start.quiet_a_date,hs]; norm_num)
  have hbReady : ∀ j, ReadyCoordinates b j := fun j =>
    quietAt_ready_coordinates w.start.quietB j (w.start.quiet_b_prepared j).ready_coordinates
      (by rw [w.start.quiet_b_date,hs]; norm_num)
  have haRaw : ∀ j q, a.raw j q = none := w.start.quiet_a_raw_none
  have hbRaw : ∀ j q, b.raw j q = none := w.start.quiet_b_raw_none
  have haQueue : a.pending = [] := w.start.quiet_a_pending
  have hbQueue : b.pending = [] := w.start.quiet_b_pending
  have hSource : (s.prependQuiet b).prependQuiet a = w.final := w.final_state.symm
  obtain ⟨prePair,hePair,hdPair⟩ := fire.portBeforeExecution.prepend_quiet_neutral
    fire.portBefore_emissions (fun _ : Fin 1 => freshB) b rfl hbReady hbRaw hbQueue (fun _ _ => [])
  obtain ⟨preGlobal,heGlobal,hdGlobal⟩ := prePair.prepend_quiet_neutral hePair θ a rfl
    haReady haRaw haQueue route
  let before : Snapshot 3 := (fire.portBefore.prependQuiet (quietAt b F)).prependQuiet (quietAt a F)
  let pre : Execution params route w.final before := (preGlobal.cast_source hSource.symm).cast_parameters
    (ConstructedCadenceStart.parameters_nested (θ := θ) (freshB := freshB) (freshC := freshC))
  have hParams : prependParameters θ (prependParameters (fun _ : Fin 1 => freshB)
      (fun _ : Fin 1 => freshC)) = params := ConstructedCadenceStart.parameters_nested
  have hPreLedger : pre.ledger = preGlobal.ledger :=
    ((preGlobal.cast_source hSource.symm).cast_parameters_ledger hParams).trans
      (preGlobal.cast_source_ledger hSource.symm)
  have hePre : pre.ledger.emissions = [] :=
    (congrArg (fun L : Ledger 3 => L.emissions) hPreLedger).trans heGlobal
  have hdPre : pre.deliveries = [] := by
    have h : pre.deliveries = preGlobal.deliveries :=
      ((preGlobal.cast_source hSource.symm).cast_parameters_deliveries hParams).trans
        (preGlobal.cast_source_deliveries hSource.symm)
    rw [h,hdGlobal,hdPair,fire.portBefore_deliveries]
    rfl
  have hroute : route 2 F = [⟨1,2,H⟩] := by
    have hlo : (640 : ℝ) ≤ F := by linarith [hF.1]
    have hhi : F < (780 : ℝ) := by linarith [hF.2]
    simp [route,cadenceRouter,cadenceForwardContact,cadenceReturnContact,Contact.route,
      Contact.token,hlo,hhi,H]
  let after : Snapshot 3 := {setMain before 2 .fast with pending := before.pending ++ route 2 F}
  let fireGlobal : Jump route before after := .fire before 2 (fire.firstSilent.main_ready 0) fire.threshold
  have heFire : fireGlobal.ledger.emissions = [(2,F)] := rfl
  have hdFire : fireGlobal.deliveries = [] := rfl
  let firing : Execution params route w.final after := pre.append (.cons (.jump fireGlobal) (.nil _))
  have heFiring : firing.ledger.emissions = [(2,F)] := by
    change (pre.append (.cons (.jump fireGlobal) (.nil _))).ledger.emissions = _
    rw [Execution.emissions_append,hePre]
    change [] ++ (fireGlobal.ledger.emissions ++ []) = _
    rw [heFire]
    rfl
  have hdFiring : firing.deliveries = [] := by
    change (pre.append (.cons (.jump fireGlobal) (.nil _))).deliveries = _
    rw [Execution.deliveries_append,hdPre]
    change [] ++ (fireGlobal.deliveries ++ []) = _
    rw [hdFire]
    rfl
  obtain ⟨cut⟩ := fast.execution.before_flow_cut_exists H hFH.le
    (by rw [fast.date]; dsimp [H,F]; linarith [(hdelay fire.final.time).2])
  have heCut : cut.cut.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (cut.emissions.symm.trans fast.emissions)).1
  have hdCut : cut.cut.deliveries = [] :=
    (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans fast.deliveries)).1
  have haFReady : ∀ j, ReadyCoordinates (quietAt a F) j := fun j =>
    quietAt_ready_coordinates a j (haReady j) (by change s.time ≤ F; rw [hs]; linarith [hF.1])
  have hbFReady : ∀ j, ReadyCoordinates (quietAt b F) j := fun j =>
    quietAt_ready_coordinates b j (hbReady j) (by change s.time ≤ F; rw [hs]; linarith [hF.1])
  obtain ⟨postPair,hePostPair,hdPostPair⟩ := cut.cut.prepend_quiet_neutral heCut
    (fun _ : Fin 1 => freshB) (quietAt b F) rfl hbFReady hbRaw hbQueue (fun _ _ => [])
  obtain ⟨postGlobal,hePostGlobal,hdPostGlobal⟩ := postPair.prepend_quiet_neutral hePostPair θ
    (quietAt a F) rfl haFReady haRaw haQueue route
  let post : Execution params route
      ((fire.final.prependQuiet (quietAt b F)).prependQuiet (quietAt a F))
      ((cut.state.prependQuiet (quietAt (quietAt b F) cut.state.time)).prependQuiet
        (quietAt (quietAt a F) cut.state.time)) := postGlobal.cast_parameters
    (ConstructedCadenceStart.parameters_nested (θ := θ) (freshB := freshB) (freshC := freshC))
  have hPostLedger : post.ledger = postGlobal.ledger := postGlobal.cast_parameters_ledger hParams
  have hePost : post.ledger.emissions = [] :=
    (congrArg (fun L : Ledger 3 => L.emissions) hPostLedger).trans hePostGlobal
  have hdPost : post.deliveries = [] := by
    have h : post.deliveries = postGlobal.deliveries := postGlobal.cast_parameters_deliveries hParams
    rw [h,hdPostGlobal,hdPostPair,hdCut]
    rfl
  obtain ⟨framed,hFrameLedger,hFrameDel⟩ := post.appendFuture_neutral hePost [⟨1,2,H⟩]
    (by intro d hd; have he : d = (⟨1,2,H⟩ : Delivery 3) := List.mem_singleton.mp hd
        subst d; exact cut.date.le)
  have hAfter : after = appendPending
      ((fire.final.prependQuiet (quietAt b F)).prependQuiet (quietAt a F)) [⟨1,2,H⟩] := by
    dsimp [after,before,appendPending]
    rw [fire.port_final_empty,Snapshot.prependQuiet_setMain,Snapshot.prependQuiet_setMain,hroute]
    rfl
  let aH := quietAt (quietAt a F) cut.state.time
  let bH := quietAt (quietAt b F) cut.state.time
  let beforeWire : Snapshot 3 := appendPending ((cut.state.prependQuiet bH).prependQuiet aH) [⟨1,2,H⟩]
  let wireTrace : Execution params route after beforeWire := framed.cast_source hAfter
  have hWireLedger : wireTrace.ledger = post.ledger :=
    (framed.cast_source_ledger hAfter).trans hFrameLedger
  have heWire : wireTrace.ledger.emissions = [] :=
    (congrArg (fun L : Ledger 3 => L.emissions) hWireLedger).trans hePost
  have hdWire : wireTrace.deliveries = [] :=
    (framed.cast_source_deliveries hAfter).trans (hFrameDel.trans hdPost)
  let Q := (cut.state.pending.map Delivery.succ).map Delivery.succ
  let final : Snapshot 3 := {setRaw beforeWire 1 2 (some beforeWire.time) with pending := Q ++ []}
  let arrival : Jump route beforeWire final := .arrive beforeWire ⟨1,2,H⟩ Q [] rfl cut.date.symm (hbRaw 0 2)
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨1,2,H⟩] := rfl
  let trace : Execution params route w.final final := firing.append (wireTrace.append (.cons (.jump arrival) (.nil _)))
  have hPendingC : cut.state.pending = s.pending := by
    rw [cut.cut.pending_eq_of_no_events heCut hdCut,fire.pending]
    simp only [List.append_nil]
  have hPending : final.pending = sourceTrain 2 0 656 4 21 := by
    change ((cut.state.pending.map Delivery.succ).map Delivery.succ) ++ [] = _
    rw [hPendingC,hQ,List.append_nil]
    simp [sourceTrain,Delivery.succ]
  have haValues : final.x 0 = (quietAt w.start.quietA final.time).x 0 := by
    change aH.x 0 = (quietAt w.start.quietA cut.state.time).x 0
    dsimp [aH,a]
    rw [quietAt_quietAt,quietAt_quietAt]
  have hbValues : final.x 1 = (quietAt w.start.quietB final.time).x 0 := by
    change bH.x 0 = (quietAt w.start.quietB cut.state.time).x 0
    dsimp [bH,b]
    rw [quietAt_quietAt,quietAt_quietAt]
  have haHReady : ReadyCoordinates aH 0 := quietAt_ready_coordinates (quietAt a F) 0 (haFReady 0)
    (by change F ≤ cut.state.time; rw [cut.date]; exact hFH.le)
  have hbHReady : ReadyCoordinates bH 0 := quietAt_ready_coordinates (quietAt b F) 0 (hbFReady 0)
    (by change F ≤ cut.state.time; rw [cut.date]; exact hFH.le)
  have haPrepared : PreparedSection final 0 :=
    ⟨haHReady.ready,haHReady.charge,(w.start.quiet_a_prepared 0).recovery,haHReady.auxiliary⟩
  have hbPrepared : PreparedSection final 1 :=
    ⟨hbHReady.ready,hbHReady.charge,(w.start.quiet_b_prepared 0).recovery,hbHReady.auxiliary⟩
  have haCharge : final.x 0 .q = 1 / 10 := by
    rw [haValues]
    change relax (1 / 2) (1 / 10) (w.start.quietA.x 0 .q) w.start.quietA.time final.time = _
    rw [show w.start.quietA.x 0 .q = 1 / 10 from w.start.charge 0]
    simp [relax]
  have hbCharge : final.x 1 .q = 1 / 10 := by
    rw [hbValues]
    change relax (1 / 2) (1 / 10) (w.start.quietB.x 0 .q) w.start.quietB.time final.time = _
    rw [show w.start.quietB.x 0 .q = 1 / 10 from w.start.charge 1]
    simp [relax]
  have hRawA : ∀ q, final.raw 0 q = none := by
    intro q
    change (setRaw beforeWire 1 2 (some beforeWire.time)).raw 0 q = none
    rw [raw_update_other _ _ _ _ _ _ (Or.inl (by decide))]
    exact haRaw 0 q
  have hRawB : final.raw 1 2 = some final.time := by simp [final,setRaw]
  have hRawBOther : ∀ q, q ≠ 2 → final.raw 1 q = none := by
    intro q hq
    change (setRaw beforeWire 1 2 (some beforeWire.time)).raw 1 q = none
    rw [raw_update_other _ _ _ _ _ _ (Or.inr hq)]
    exact hbRaw 0 q
  have hRawC : ∀ q, final.raw 2 q = cut.state.raw 0 q := by
    intro q
    change (setRaw beforeWire 1 2 (some beforeWire.time)).raw 2 q = cut.state.raw 0 q
    rw [raw_update_other _ _ _ _ _ _ (Or.inl (by decide))]
    rfl
  have hGainC (q : Port) : final.x 2 (.z q) = w.final.x 2 (.z q) := by
    have h := cut.isPrefix.gain_eq_of_final hb.extend_new 0 q (fast.gains 0 q)
    have hg := h.trans (fire.gain_preserved 0 q)
    change cut.state.x 0 (.z q) = _
    rw [w.final_state]
    exact hg
  have hRecC : final.x 2 .b = w.final.x 2 .b := by
    have h := cut.isPrefix.recovery_eq_of_final hb.extend_new 0 (fast.recovery 0)
    have hr := h.trans (fire.recovery_preserved 0)
    change cut.state.x 0 .b = _
    rw [w.final_state]
    exact hr
  have hGains : ∀ i q, final.x i (.z q) = w.final.x i (.z q) := by
    intro i q
    fin_cases i
    · change final.x 0 (.z q) = w.final.x 0 (.z q)
      rw [haValues,w.final_state]; rfl
    · change final.x 1 (.z q) = w.final.x 1 (.z q)
      rw [hbValues,w.final_state]; rfl
    · exact hGainC q
  have hRecovery : ∀ i, final.x i .b = w.final.x i .b := by
    intro i
    fin_cases i
    · change final.x 0 .b = w.final.x 0 .b
      rw [haValues,w.final_state]; rfl
    · change final.x 1 .b = w.final.x 1 .b
      rw [hbValues,w.final_state]; rfl
    · exact hRecC
  have hFutureFinal : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    rw [hPending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change cut.state.time < 656 + 4 * (k.val : ℝ)
    rw [cut.date]
    nlinarith [hH.2,Nat.cast_nonneg (α := ℝ) k.val]
  have hGuard : @BeforeGuards 3 final final.x := by
    constructor
    · intro i
      rcases (show i = (0 : Fin 3) ∨ i = (1 : Fin 3) ∨ i = (2 : Fin 3) by fin_cases i <;> norm_num) with hi | hi | hi <;> subst i
      · rw [haPrepared.ready,haCharge]; norm_num
      · rw [hbPrepared.ready,hbCharge]; norm_num
      · exact cut.before_guards.1 0
    · intro i q
      rcases (show i = (0 : Fin 3) ∨ i = (1 : Fin 3) ∨ i = (2 : Fin 3) by fin_cases i <;> norm_num) with hi | hi | hi <;> subst i
      · rw [(haPrepared.auxiliary q).1]; linarith [(haPrepared.auxiliary q).2.2]
      · rw [(hbPrepared.auxiliary q).1]; linarith [(hbPrepared.auxiliary q).2.2]
      · exact cut.before_guards.2 0 q
  have hComplete : CompleteThrough trace final.time := by
    refine ⟨rfl,?_,hFutureFinal⟩
    intro u
    apply hGuard.no_jump
    · intro i q origin hr
      rcases (show i = (0 : Fin 3) ∨ i = (1 : Fin 3) ∨ i = (2 : Fin 3) by fin_cases i <;> norm_num) with hi | hi | hi <;> subst i
      · rw [hRawA] at hr; contradiction
      · by_cases hq : q = 2
        · subst q
          have ho : origin = final.time := Option.some.inj (hr.symm.trans hRawB)
          rw [ho]; linarith
        · rw [hRawBOther q hq] at hr; contradiction
      · rw [hRawC] at hr
        exact cut.flow.initial_raw_strict 0 q origin hr
    · exact hFutureFinal
  refine ⟨{
    fire := fire, fast := fast, cutH := cut, final := final, execution := trace, date := cut.date
    window := ?_, pending := hPending, a_values := haValues, a_prepared := haPrepared
    a_charge := haCharge, a_raw_none := hRawA, b_values := hbValues, b_prepared := hbPrepared
    b_charge := hbCharge, b_raw_active := hRawB, b_raw_other := hRawBOther
    c_values := rfl, c_main := rfl, c_aux := fun _ => rfl, c_raw := hRawC
    gains := hGains, recovery := hRecovery, emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb w.physical, raw_valid := trace.raw_valid w.raw_valid
    complete := hComplete
  }⟩
  · change 6527 / 10 < cut.state.time ∧ cut.state.time < 6533 / 10
    rw [cut.date]
    exact hH
  · rw [Execution.emissions_append,heFiring,Execution.emissions_append,heWire]
    simp only [Execution.ledger,Move.ledger,haEm,Ledger.add,Ledger.zero,List.append_nil]
    rfl
  · rw [Execution.deliveries_append,hdFiring,Execution.deliveries_append,hdWire]
    simp only [Execution.deliveries,Move.deliveries,haDel,List.nil_append,List.append_nil]
    change [⟨1,2,H⟩] = ([⟨1,2,cut.state.time⟩] : List (Delivery 3))
    rw [cut.date]

end KernelR.Hybrid
