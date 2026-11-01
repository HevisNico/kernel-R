import KernelR.HybridFirstReceiverFire
import KernelR.HybridMidLearnedFastEnd

/-! B's real protected FAST phase is interleaved with A's retained return.
The source-H2 raw tag expires physically before this new FAST endpoint. -/
namespace KernelR.Hybrid

structure FirstReceiverFastEnd {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    (f : FirstReceiverFire w) where
  fastB : MidLearnedFastEnd f.firelocal
  senderRemainderA : Execution θ (fun _ _ => []) f.cutA.state f.senderReturnA.final
  sender_emissions : senderRemainderA.ledger.emissions = []
  sender_deliveries : senderRemainderA.deliveries = []
  cutA : senderRemainderA.BeforeFlowCut fastB.final.time
  cutA_emissions : cutA.cut.ledger.emissions = []
  cutA_deliveries : cutA.cut.deliveries = []
  final : Snapshot 2
  execution : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) f.final final
  product_final : final = cutA.state.product fastB.final firstInterleavedPending
  clock : final.time = fastB.final.time
  date : final.time = f.final.time + 1
  horizon : final.time < 856 / 5
  pending : final.pending = firstInterleavedPending
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  sender_values : final.x 0 = cutA.state.x 0
  sender_main : final.main 0 = cutA.state.main 0
  sender_aux : ∀ p, final.aux 0 p = cutA.state.aux 0 p
  sender_raw : ∀ p, final.raw 0 p = cutA.state.raw 0 p
  receiver_values : final.x 1 = fastB.final.x 0
  b_main_slow : final.main 1 = .slow
  b_charge : final.x 1 .q = 1 / 4
  b_aux_rest : ∀ p, final.aux 1 p = .ready ∧ RestBand (final.x 1 (.m p))
  b_raw_none : ∀ p, final.raw 1 p = none
  gains : ∀ j p, final.x j (.z p) = f.final.x j (.z p)
  recovery : ∀ j, final.x j .b = f.final.x j .b
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final

/-- Complete the actual SILENT/ERROR/RAW phases and FAST guard of the first
B output while A follows a true maximal prefix of its existing continuation. -/
theorem first_receiver_fast_end_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (f : FirstReceiverFire w)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (FirstReceiverFastEnd f) := by
  obtain ⟨fast⟩ := f.firelocal.mid_learned_fast_end_exists hb.extend_new (w.receiver_fire_ready 0)
    (w.receiver_gain_bounds hb hdelay).2
    (fun p hp => w.receiver_fire_raw_other 0 p (Or.inr hp)) (by
      intro d hd
      change d ∈ ([] : List (Delivery 1)) at hd
      contradiction)
  let remainder : Execution θ (fun _ _ => []) f.cutA.state f.senderReturnA.final :=
    .cons (.flow f.cutA.flow) f.cutA.rest
  have heRem : remainder.ledger.emissions = [] := by
    have h := f.cutA.emissions.symm.trans f.senderTrace_emissions
    change [] ++ f.cutA.rest.ledger.emissions = []
    simpa using (List.append_eq_nil_iff.mp h).2
  have hdRem : remainder.deliveries = [] := by
    have h := f.cutA.deliveries.symm.trans f.senderTrace_deliveries
    change [] ++ f.cutA.rest.deliveries = []
    simpa using (List.append_eq_nil_iff.mp h).2
  have htime : fast.final.time = f.final.time + 1 := by rw [fast.date,← f.clock]
  have hupper : fast.final.time < (856 / 5 : ℝ) := by rw [htime]; linarith [f.horizon]
  obtain ⟨cut⟩ := remainder.before_flow_cut_exists fast.final.time
    (by rw [f.cutA.date,fast.date]; linarith)
    (by rw [f.senderReturnA.date]; linarith)
  have heCut : cut.cut.ledger.emissions = [] := by
    have h := cut.emissions.symm.trans heRem
    exact (List.append_eq_nil_iff.mp h).1
  have hdCut : cut.cut.deliveries = [] := by
    have h := cut.deliveries.symm.trans hdRem
    exact (List.append_eq_nil_iff.mp h).1
  let oldTail : Execution θ (fun _ _ => []) w.cut.state w.fast.final :=
    .cons (.flow w.cut.flow) w.cut.rest
  have hOldGain (p : Port) : w.cut.state.x 0 (.z p) = w.fast.final.x 0 (.z p) := by
    have h1 := w.cut.cut.gain_nondecreasing hb.extend_old 0 p
    have h2 := oldTail.gain_nondecreasing hb.extend_old 0 p
    have h3 := w.fast.gains 0 p
    linarith
  have hOldRecovery : w.cut.state.x 0 .b = w.fast.final.x 0 .b := by
    have h1 := w.cut.cut.recovery_nondecreasing hb.extend_old 0
    have h2 := oldTail.recovery_nondecreasing hb.extend_old 0
    have h3 := w.fast.recovery 0
    linarith
  have hStartGain (p : Port) : f.cutA.state.x 0 (.z p) = w.cut.state.x 0 (.z p) :=
    (congrFun f.sender_values (.z p)).symm.trans
      ((f.gains 0 p).trans (congrFun w.receipt.sender_values (.z p)))
  have hStartRecovery : f.cutA.state.x 0 .b = w.cut.state.x 0 .b :=
    (congrFun f.sender_values .b).symm.trans
      ((f.recovery 0).trans (congrFun w.receipt.sender_values .b))
  let afterCut : Execution θ (fun _ _ => []) cut.state f.senderReturnA.final :=
    .cons (.flow cut.flow) cut.rest
  have hAgains (p : Port) : cut.state.x 0 (.z p) = f.cutA.state.x 0 (.z p) := by
    have h1 := cut.cut.gain_nondecreasing hb.extend_old 0 p
    have h2 := afterCut.gain_nondecreasing hb.extend_old 0 p
    have h3 := (f.senderReturnA.gains 0 p).trans (hOldGain p).symm
    linarith [hStartGain p]
  have hArecovery : cut.state.x 0 .b = f.cutA.state.x 0 .b := by
    have h1 := cut.cut.recovery_nondecreasing hb.extend_old 0
    have h2 := afterCut.recovery_nondecreasing hb.extend_old 0
    have h3 := (f.senderReturnA.recovery 0).trans hOldRecovery.symm
    linarith
  have hstart : f.cutA.state.time = f.firelocal.final.time := f.cutA.date
  have hQ : ∀ d ∈ firstInterleavedPending, cut.state.time ≤ d.due := by
    intro d hd
    rw [cut.date]
    linarith [FirstInterleavedPair.queue_future d hd]
  obtain ⟨woven,heW,hdW⟩ := cut.cut.product_neutral fast.execution hstart cut.date
    heCut hdCut fast.emissions fast.deliveries firstInterleavedPending hQ
    (reciprocalEntryRouter forward backward)
  let final := cut.state.product fast.final firstInterleavedPending
  let e : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) f.final final :=
    woven.cast_source f.product_final
  have hem : e.ledger.emissions = [] := by
    simpa only [e,Execution.cast_source_ledger] using heW
  have hdel : e.deliveries = [] := by
    simpa only [e,Execution.cast_source_deliveries] using hdW
  refine ⟨{
    fastB := fast, senderRemainderA := remainder, sender_emissions := heRem, sender_deliveries := hdRem
    cutA := cut, cutA_emissions := heCut, cutA_deliveries := hdCut
    final := final, execution := e, product_final := rfl, clock := cut.date
    date := cut.date.trans htime, horizon := ?_, pending := rfl, emissions := hem, deliveries := hdel
    sender_values := rfl, sender_main := rfl, sender_aux := fun _ => rfl, sender_raw := fun _ => rfl
    receiver_values := rfl, b_main_slow := fast.main_slow, b_charge := fast.charge
    b_aux_rest := fun p => ⟨fast.auxiliary 0 p,fast.rest p⟩, b_raw_none := fun p => fast.raw_none 0 p
    gains := ?_, recovery := ?_, physical := e.physical_invariant hb f.physical, raw_valid := e.raw_valid f.raw_valid
  }⟩
  · change cut.state.time < (856 / 5 : ℝ)
    rw [cut.date]; exact hupper
  · intro j p
    fin_cases j
    · exact (hAgains p).trans (congrFun f.sender_values (.z p)).symm
    · exact (fast.gains 0 p).trans (congrFun f.receiver_values (.z p)).symm
  · intro j
    fin_cases j
    · exact hArecovery.trans (congrFun f.sender_values .b).symm
    · exact (fast.recovery 0).trans (congrFun f.receiver_values .b).symm

namespace FirstReceiverFastEnd
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
  {f : FirstReceiverFire w} (v : FirstReceiverFastEnd f)

theorem pending_length : v.final.pending.length = 46 := by
  rw [v.pending]
  simp [firstInterleavedPending,constructedBBirthSources,sourceTrain]

theorem b_recovery : v.final.x 1 .b = newborn.x .b := by rw [v.recovery,f.receiver_recovery]

theorem b_gain_target {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    v.final.x 1 (.z 1) = newborn.x (.z 1) + 3 / 5 := by
  rw [v.gains,f.receiver_gain_target hb hdelay]

theorem complete : CompleteThrough v.execution v.final.time := by
  have hg := v.cutA.flow.initial_before_guards
  have hguard : BeforeGuards v.final v.final.x := by
    constructor
    · intro j
      by_cases hj : j = 0
      · subst j
        rw [v.sender_main,v.sender_values]
        exact hg.1 0
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst j
        rw [v.b_main_slow,v.b_charge]
        norm_num
    · intro j p
      by_cases hj : j = 0
      · subst j
        rw [v.sender_aux,v.sender_values]
        exact hg.2 0 p
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst j
        rw [(v.b_aux_rest p).1]
        linarith [(v.b_aux_rest p).2.2]
  have hfuture : ∀ d ∈ v.final.pending, v.final.time < d.due := by
    intro d hd
    rw [v.pending] at hd
    linarith [FirstInterleavedPair.queue_future d hd,v.horizon]
  refine ⟨rfl,?_,hfuture⟩
  intro u
  apply hguard.no_jump
  · intro j p origin hraw
    by_cases hj : j = 0
    · subst j
      rw [v.sender_raw] at hraw
      rw [v.clock,← v.cutA.date]
      exact v.cutA.flow.initial_raw_strict 0 p origin hraw
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j
      rw [v.b_raw_none p] at hraw
      contradiction
  · exact hfuture

end FirstReceiverFastEnd
end KernelR.Hybrid
