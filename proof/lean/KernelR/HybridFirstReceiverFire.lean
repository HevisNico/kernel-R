import KernelR.HybridSecondWiredArrival
import KernelR.HybridMidLearnedFire
import KernelR.HybridNeutralExecutionProduct
import KernelR.HybridPreparedSlowReturn

/-! The newborn receiver's first genuine FIRE is built from its second actual
wire input, while the sender follows its retained physical continuation. -/
namespace KernelR.Hybrid

noncomputable def FirstLearnedFire.portBefore {n θ s i p}
    (f : @FirstLearnedFire n θ (fun _ _ => []) s i p) : Snapshot n :=
  f.firstSilent.learnedFireBefore f.latency

noncomputable def FirstLearnedFire.portBeforeExecution {n θ s i p}
    (f : @FirstLearnedFire n θ (fun _ _ => []) s i p) : Execution θ (fun _ _ => []) s f.portBefore :=
  (f.firstSilent.execution (fun _ _ => [])).append (.cons (.flow f.flow) (.nil _))

theorem FirstLearnedFire.portBefore_emissions {n θ s i p}
    (f : @FirstLearnedFire n θ (fun _ _ => []) s i p) :
    f.portBeforeExecution.ledger.emissions = [] := by
  simp [portBeforeExecution,FirstInputSilent.execution,FirstInputSilent.continuation,
    FirstInputMark.execution,Execution.emissions_append,Execution.ledger,Move.ledger,
    Flow.ledger,Jump.ledger,Ledger.add,Ledger.zero]

theorem FirstLearnedFire.portBefore_deliveries {n θ s i p}
    (f : @FirstLearnedFire n θ (fun _ _ => []) s i p) : f.portBeforeExecution.deliveries = [] := by
  simp [portBeforeExecution,FirstInputSilent.execution,FirstInputSilent.continuation,
    FirstInputMark.execution,Execution.deliveries_append,Execution.deliveries,Move.deliveries,Jump.deliveries]

theorem FirstLearnedFire.port_final_empty {n θ s i p}
    (f : @FirstLearnedFire n θ (fun _ _ => []) s i p) :
    f.final = setMain f.portBefore i .fast := by
  simp only [final,FirstInputSilent.learnedFireFinal,List.append_nil,portBefore]
  rfl

namespace SecondWiredArrival
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} (w : SecondWiredArrival s)

noncomputable def receiverFireLocal : Snapshot 1 := w.final.cellProjection 1 []

theorem receiver_fire_physical : PhysicalInvariant (fun _ : Fin 1 => fresh) w.receiverFireLocal := by
  have hθ : extendParameters θ fresh (1 : Fin 2) = fresh := rfl
  refine ⟨fun j => w.receipt.physical.region 1,?_,
    fun j => w.receipt.physical.recovery_cap 1,fun j => w.receipt.physical.reserve 1⟩
  intro j p
  change w.final.x 1 (.z p) ≤ Real.log (fresh.cap p)
  have h := w.receipt.physical.gain_cap 1 p
  change w.final.x 1 (.z p) ≤ Real.log ((extendParameters θ fresh 1).cap p) at h
  rwa [hθ] at h

theorem receiver_fire_raw_valid : RawValid w.receiverFireLocal :=
  fun _ p o h => w.receipt.raw_valid 1 p o h

theorem receiver_fire_ready : ∀ j, ReadyCoordinates w.receiverFireLocal j :=
  fun _ => ⟨w.receiver_ready.ready,w.receiver_ready.charge,w.receiver_ready.auxiliary⟩

theorem receiver_fire_raw : w.receiverFireLocal.raw 0 1 = some w.receiverFireLocal.time := w.raw_receiver

theorem receiver_fire_raw_other : ∀ j p, j ≠ (0 : Fin 1) ∨ p ≠ 1 → w.receiverFireLocal.raw j p = none := by
  intro j p h
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact w.raw_receiver_other p (by simpa using h)

theorem receiver_fire_product_initial :
    w.cut.state.product w.receiverFireLocal firstInterleavedPending = w.final := by
  have extensionality {n} (a u : Snapshot n) (ht : a.time = u.time) (hx : a.x = u.x)
      (hm : a.main = u.main) (ha : a.aux = u.aux) (hr : a.raw = u.raw)
      (hp : a.pending = u.pending) : a = u := by
    cases a
    cases u
    simp_all only
  apply extensionality
  · exact w.receipt.date.symm
  · funext j
    by_cases hj : j = 0
    · subst j; exact w.receipt.sender_values.symm
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; rfl
  · funext j
    by_cases hj : j = 0
    · subst j; exact w.receipt.sender_main.symm
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; rfl
  · funext j
    by_cases hj : j = 0
    · subst j; funext p; exact (w.receipt.sender_aux p).symm
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; rfl
  · funext j
    by_cases hj : j = 0
    · subst j; funext p; exact (w.receipt.sender_raw p).symm
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j; rfl
  · exact w.pending.symm

end SecondWiredArrival

structure FirstReceiverFire {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} (w : SecondWiredArrival s) where
  firelocal : FirstLearnedFire (fun _ : Fin 1 => fresh) (fun _ _ => []) w.receiverFireLocal 0 1
  senderReturnA : PreparedSlowReturn θ (fun _ _ => []) w.fast.final 168
  senderTraceA : Execution θ (fun _ _ => []) w.cut.state senderReturnA.final
  senderTrace_emissions : senderTraceA.ledger.emissions = []
  senderTrace_deliveries : senderTraceA.deliveries = []
  cutA : senderTraceA.BeforeFlowCut firelocal.final.time
  cutA_emissions : cutA.cut.ledger.emissions = []
  cutA_deliveries : cutA.cut.deliveries = []
  before : Snapshot 2
  final : Snapshot 2
  span : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) w.final before
  fire : Jump (reciprocalEntryRouter forward backward) before final
  execution : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) w.final final
  product_before : before = cutA.state.product firelocal.portBefore firstInterleavedPending
  product_final : final = cutA.state.product firelocal.final firstInterleavedPending
  clock : final.time = firelocal.final.time
  date : final.time = w.final.time + firelocal.latency
  early : w.final.time + 2 / 5 < final.time
  deadline : final.time < w.final.time + 9 / 10
  horizon : final.time < 851 / 5
  pending : final.pending = firstInterleavedPending
  span_emissions : span.ledger.emissions = []
  span_deliveries : span.deliveries = []
  emissions : execution.ledger.emissions = [(1,final.time)]
  deliveries : execution.deliveries = []
  sender_values : final.x 0 = cutA.state.x 0
  sender_main : final.main 0 = cutA.state.main 0
  sender_aux : ∀ p, final.aux 0 p = cutA.state.aux 0 p
  sender_raw : ∀ p, final.raw 0 p = cutA.state.raw 0 p
  receiver_values : final.x 1 = firelocal.final.x 0
  receiver_main_fast : final.main 1 = .fast
  receiver_charge : final.x 1 .q = 1
  receiver_aux_silent : final.aux 1 1 = .silent
  receiver_sensor_above : 1 / 10 < final.x 1 (.m 1)
  receiver_aux_other : ∀ p, p ≠ 1 → final.aux 1 p = .ready ∧ RestBand (final.x 1 (.m p))
  raw_active : final.raw 1 1 = some w.final.time
  raw_other : ∀ p, p ≠ 1 → final.raw 1 p = none
  gains : ∀ j p, final.x j (.z p) = w.final.x j (.z p)
  recovery : ∀ j, final.x j .b = w.final.x j .b
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final

/-- Construct B's own first threshold and interleave its pre-FIRE segment
with a maximal real prefix of A's retained return execution. -/
theorem first_receiver_fire_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (w : SecondWiredArrival s)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (FirstReceiverFire w) := by
  have hg : 9 / 5 ≤ Real.exp (w.receiverFireLocal.x 0 (.z 1)) ∧
      Real.exp (w.receiverFireLocal.x 0 (.z 1)) ≤ 11 / 5 := w.receiver_gain_bounds hb hdelay
  obtain ⟨f⟩ := first_mid_learned_fire_exists (route := fun _ _ => []) w.receiverFireLocal hb.extend_new
    w.receiver_fire_physical w.receiver_fire_raw_valid 0 1 w.receiver_fire_ready hg
    w.receiver_fire_raw w.receiver_fire_raw_other (by
      intro d hd
      change d ∈ ([] : List (Delivery 1)) at hd
      contradiction)
  have hdate : f.final.time = w.final.time + f.latency := f.date
  have hearly : w.final.time + 2 / 5 < f.final.time :=
    readyPulse_mid_root_after_four_tenths (w.receiver_fire_ready 0).charge.2 hg.2
      (by rw [hdate]; linarith [f.early]) f.response_root
  have hdeadline : f.final.time < w.final.time + 9 / 10 := by rw [hdate]; linarith [f.deadline]
  have hupper : f.final.time < (851 / 5 : ℝ) := by linarith [(w.date_bounds hdelay).2]
  let tailA : Execution θ (fun _ _ => []) w.cut.state w.fast.final :=
    .cons (.flow w.cut.flow) w.cut.rest
  have heTail : tailA.ledger.emissions = [] := by
    have h := w.cut.emissions.symm.trans w.fast.emissions
    change [] ++ w.cut.rest.ledger.emissions = []
    simpa using (List.append_eq_nil_iff.mp h).2
  have hdTail : tailA.deliveries = [] := by
    have h := w.cut.deliveries.symm.trans w.fast.deliveries
    change [] ++ w.cut.rest.deliveries = []
    simpa using (List.append_eq_nil_iff.mp h).2
  have hAstartgain (j : Fin 1) (p : Port) : w.cut.state.x j (.z p) = w.fast.final.x j (.z p) := by
    have h1 := w.cut.cut.gain_nondecreasing hb.extend_old j p
    have h2 := tailA.gain_nondecreasing hb.extend_old j p
    have h3 := w.fast.gains j p
    linarith
  have hAstartrecovery (j : Fin 1) : w.cut.state.x j .b = w.fast.final.x j .b := by
    have h1 := w.cut.cut.recovery_nondecreasing hb.extend_old j
    have h2 := tailA.recovery_nondecreasing hb.extend_old j
    have h3 := w.fast.recovery j
    linarith
  have hB : 17999 / 100000 ≤ w.fast.final.x 0 .b ∧ w.fast.final.x 0 .b ≤ 18001 / 100000 := by
    rw [w.fast.recovery,w.fire.firelocal.recovery_preserved]
    exact s.a_prepared.recovery
  have htime : w.fast.final.time = 168 + w.fire.firelocal.latency + 1 := by
    rw [w.fast.date,w.fire.firelocal.date]
    change s.final.time + _ + 1 = _
    rw [s.date]
  have hfastPending : w.fast.final.pending = [] := by
    rw [w.fast.pending,w.fire.firelocal.pending]
    simp only [List.append_nil]
    rfl
  obtain ⟨ret⟩ := prepared_slow_return_exists (route := fun _ _ => []) hb.extend_old w.fast.final
    168 w.fire.firelocal.latency w.fast.physical w.fast.raw_valid w.fast.main_slow w.fast.charge hB
    (fun p => ⟨w.fast.auxiliary 0 p,w.fast.rest p⟩) w.fast.raw_none htime
    ⟨by linarith [w.fire.firelocal.early],w.fire.firelocal.deadline⟩ (by
      intro d hd
      rw [hfastPending] at hd
      contradiction)
  let senderTrace : Execution θ (fun _ _ => []) w.cut.state ret.final := tailA.append ret.execution
  have heSender : senderTrace.ledger.emissions = [] := by
    rw [Execution.emissions_append,heTail,ret.emissions]
    rfl
  have hdSender : senderTrace.deliveries = [] := by
    rw [Execution.deliveries_append,hdTail,ret.deliveries]
    rfl
  obtain ⟨cut⟩ := senderTrace.before_flow_cut_exists f.final.time
    (by have ht := w.receipt.date; change w.final.time = w.cut.state.time at ht
        rw [← ht]; linarith)
    (by rw [ret.date]; linarith)
  have heCut : cut.cut.ledger.emissions = [] := by
    have h := cut.emissions.symm.trans heSender
    exact (List.append_eq_nil_iff.mp h).1
  have hdCut : cut.cut.deliveries = [] := by
    have h := cut.deliveries.symm.trans hdSender
    exact (List.append_eq_nil_iff.mp h).1
  let restA : Execution θ (fun _ _ => []) cut.state ret.final := .cons (.flow cut.flow) cut.rest
  have hAgains (j : Fin 1) (p : Port) : cut.state.x j (.z p) = w.cut.state.x j (.z p) := by
    have h1 := cut.cut.gain_nondecreasing hb.extend_old j p
    have h2 := restA.gain_nondecreasing hb.extend_old j p
    have h3 := (ret.gains j p).trans (hAstartgain j p).symm
    linarith
  have hArecovery (j : Fin 1) : cut.state.x j .b = w.cut.state.x j .b := by
    have h1 := cut.cut.recovery_nondecreasing hb.extend_old j
    have h2 := restA.recovery_nondecreasing hb.extend_old j
    have h3 := (ret.recovery j).trans (hAstartrecovery j).symm
    linarith
  have hstart : w.cut.state.time = w.receiverFireLocal.time := w.receipt.date.symm
  have hfinish : cut.state.time = f.portBefore.time := cut.date
  have hQ : ∀ d ∈ firstInterleavedPending, cut.state.time ≤ d.due := by
    intro d hd
    rw [cut.date]
    linarith [FirstInterleavedPair.queue_future d hd]
  obtain ⟨woven,heW,hdW⟩ := cut.cut.product_neutral f.portBeforeExecution hstart hfinish
    heCut hdCut f.portBefore_emissions f.portBefore_deliveries firstInterleavedPending hQ
    (reciprocalEntryRouter forward backward)
  let before := cut.state.product f.portBefore firstInterleavedPending
  let final := cut.state.product f.final firstInterleavedPending
  let span : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) w.final before :=
    woven.cast_source w.receiver_fire_product_initial.symm
  have hroute : reciprocalEntryRouter forward backward 1 before.time = [] := by
    rw [reciprocalEntryRouter.before_reverse forward backward 1 (by
      change cut.state.time < (320 : ℝ); rw [cut.date]; linarith)]
    simp [Contact.route,teachingContact]
  have hmode : before.main 1 = .ready := f.firstSilent.main_ready 0
  have hthreshold : before.x 1 .q = 1 := f.threshold
  have hfinal : final = { (setMain before 1 .fast) with
      pending := before.pending ++ reciprocalEntryRouter forward backward 1 before.time } := by
    rw [hroute]
    simp only [List.append_nil]
    dsimp [final,before]
    calc
      cut.state.product f.final firstInterleavedPending =
          cut.state.product (setMain f.portBefore 0 .fast) firstInterleavedPending :=
        congrArg (fun v : Snapshot 1 => cut.state.product v firstInterleavedPending) f.port_final_empty
      _ = setMain (cut.state.product f.portBefore firstInterleavedPending) 1 .fast :=
        Snapshot.product_setMain_right _ _ _ _
      _ = _ := rfl
  let jump : Jump (reciprocalEntryRouter forward backward) before final :=
    hfinal.symm ▸ Jump.fire before 1 hmode hthreshold
  let e : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) w.final final :=
    span.append (.cons (.jump jump) (.nil _))
  have hFast : final.main 1 = .fast := f.main_fast
  have hjEm : jump.ledger.emissions = [(1,before.time)] :=
    jump.ready_main_departure_emission 1 hmode (by rw [hFast]; decide)
  have hjDel : jump.deliveries = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have hz := jump.no_emissions_of_delivery d hd
    rw [hjEm] at hz
    contradiction
  have hsEm : span.ledger.emissions = [] := by
    simpa only [span,Execution.cast_source_ledger] using heW
  have hsDel : span.deliveries = [] := by
    simpa only [span,Execution.cast_source_deliveries] using hdW
  refine ⟨{
    firelocal := f, senderReturnA := ret, senderTraceA := senderTrace
    senderTrace_emissions := heSender, senderTrace_deliveries := hdSender
    cutA := cut, cutA_emissions := heCut, cutA_deliveries := hdCut
    before := before, final := final, span := span, fire := jump, execution := e
    product_before := rfl, product_final := rfl, clock := cut.date
    date := cut.date.trans hdate, early := ?_, deadline := ?_, horizon := ?_
    pending := rfl, span_emissions := hsEm, span_deliveries := hsDel
    emissions := ?_, deliveries := ?_
    sender_values := rfl, sender_main := rfl, sender_aux := fun _ => rfl, sender_raw := fun _ => rfl
    receiver_values := rfl, receiver_main_fast := hFast, receiver_charge := f.charge
    receiver_aux_silent := f.aux_silent, receiver_sensor_above := f.sensor_above
    receiver_aux_other := ?_, raw_active := f.raw_active, raw_other := ?_
    gains := ?_, recovery := ?_
    physical := e.physical_invariant hb w.receipt.physical, raw_valid := e.raw_valid w.receipt.raw_valid
  }⟩
  · change w.final.time + 2 / 5 < cut.state.time
    rw [cut.date]; exact hearly
  · change cut.state.time < w.final.time + 9 / 10
    rw [cut.date]; exact hdeadline
  · change cut.state.time < (851 / 5 : ℝ)
    rw [cut.date]; exact hupper
  · simp only [e,Execution.emissions_append,hsEm,Execution.ledger,Move.ledger,
      hjEm,Ledger.add,Ledger.zero,List.nil_append,List.append_nil]
    rfl
  · simp only [e,Execution.deliveries_append,hsDel,Execution.deliveries,Move.deliveries,
      hjDel,List.append_nil]
  · intro p hp
    exact (f.execution.aux_no_input_rest_band 0 p ((w.receiver_fire_ready 0).auxiliary p).1
      ((w.receiver_fire_ready 0).auxiliary p).2 (w.receiver_fire_raw_other 0 p (Or.inr hp))
      (by simp [NoArrivalAt,f.deliveries])).1
  · intro p hp
    exact f.raw_other 0 p (Or.inr hp)
  · intro j p
    fin_cases j
    · exact (hAgains 0 p).trans (congrFun w.receipt.sender_values (.z p)).symm
    · exact f.gain_preserved 0 p
  · intro j
    fin_cases j
    · exact (hArecovery 0).trans (congrFun w.receipt.sender_values .b).symm
    · exact f.recovery_preserved 0

namespace FirstReceiverFire
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s} (f : FirstReceiverFire w)

noncomputable def localBfire : FirstLearnedFire (fun _ : Fin 1 => fresh) (fun _ _ => []) w.receiverFireLocal 0 1 :=
  f.firelocal

theorem route_closed : reciprocalEntryRouter forward backward 1 f.final.time = [] := by
  rw [reciprocalEntryRouter.before_reverse forward backward 1 (by linarith [f.horizon])]
  simp [Contact.route,teachingContact]

theorem pending_length : f.final.pending.length = 46 := by
  rw [f.pending]
  simp [firstInterleavedPending,constructedBBirthSources,sourceTrain]

theorem receiver_recovery : f.final.x 1 .b = newborn.x .b := by
  rw [f.recovery,w.receiver_recovery]

theorem receiver_gain_target {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    f.final.x 1 (.z 1) = newborn.x (.z 1) + 3 / 5 := by
  rw [f.gains,w.receiver_gain_target hb hdelay]

theorem complete : CompleteThrough f.execution f.final.time := by
  have hg := f.cutA.flow.initial_before_guards
  have hguard : BeforeGuards f.final f.final.x := by
    constructor
    · intro j
      by_cases hj : j = 0
      · subst j
        rw [f.sender_main,f.sender_values]
        exact hg.1 0
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst j
        rw [f.receiver_main_fast,f.receiver_charge]
        norm_num
    · intro j p
      by_cases hj : j = 0
      · subst j
        rw [f.sender_aux,f.sender_values]
        exact hg.2 0 p
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst j
        by_cases hp : p = 1
        · subst p
          rw [f.receiver_aux_silent]
          exact f.receiver_sensor_above
        · rw [(f.receiver_aux_other p hp).1]
          linarith [(f.receiver_aux_other p hp).2.2]
  have hfuture : ∀ d ∈ f.final.pending, f.final.time < d.due := by
    intro d hd
    rw [f.pending] at hd
    linarith [FirstInterleavedPair.queue_future d hd,f.horizon]
  refine ⟨rfl,?_,hfuture⟩
  intro u
  apply hguard.no_jump
  · intro j p origin hraw
    by_cases hj : j = 0
    · subst j
      rw [f.sender_raw] at hraw
      rw [f.clock,← f.cutA.date]
      exact f.cutA.flow.initial_raw_strict 0 p origin hraw
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j
      by_cases hp : p = 1
      · subst p
        have ho : origin = w.final.time := Option.some.inj (hraw.symm.trans f.raw_active)
        rw [ho]
        linarith [f.deadline]
      · rw [f.raw_other p hp] at hraw
        contradiction
  · exact hfuture

end FirstReceiverFire
end KernelR.Hybrid
