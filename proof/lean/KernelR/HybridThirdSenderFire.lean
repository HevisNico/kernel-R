import KernelR.HybridFirstPostReceiverPair
import KernelR.HybridLowRecoverySlowContinuation
import KernelR.HybridSameGainLatency

/-! Source176 generates the third actual A firing. B follows an actual tail
of its existing SLOW span, retaining its physical energy and sensor residues. -/
namespace KernelR.Hybrid
namespace FirstPostReceiverPair
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
  {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} (v : FirstPostReceiverPair g)

theorem localA_date : v.localA.time = 176 := by rw [localA,v.sender_final]; rfl

theorem localA_prepared : PreparedSection v.localA 0 := by
  have h : PreparedSection (v.localA.product v.localB firstPostReceiverPending) 0 := by
    rw [v.product_initial]
    exact v.a_prepared
  exact ⟨h.ready,h.charge,h.recovery,h.auxiliary⟩

theorem localA_ready : ∀ j, ReadyCoordinates v.localA j := by
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact ⟨v.localA_prepared.ready,v.localA_prepared.charge,v.localA_prepared.auxiliary⟩

theorem localA_physical : PhysicalInvariant θ v.localA := by
  have hf : PhysicalInvariant (extendParameters θ fresh)
      (v.localA.product v.localB firstPostReceiverPending) := by rw [v.product_initial]; exact v.physical
  have hθ : extendParameters θ fresh (0 : Fin 2) = θ (0 : Fin 1) := rfl
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hf.region 0
  · intro j p
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have h := hf.gain_cap 0 p
    change v.localA.x 0 (.z p) ≤ Real.log ((extendParameters θ fresh 0).cap p) at h
    rwa [hθ] at h
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hf.recovery_cap 0
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hf.reserve 0

theorem localA_raw_valid : RawValid v.localA := by
  have hf : RawValid (v.localA.product v.localB firstPostReceiverPending) := by
    rw [v.product_initial]; exact v.raw_valid
  intro j p origin hr
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact hf 0 p origin hr

theorem localA_raw_active : v.localA.raw 0 0 = some v.localA.time := by
  rw [v.localA_date]
  simp [localA,setRaw]

theorem localA_raw_other (p : Port) (hp : p ≠ 0) : v.localA.raw 0 p = none := by
  have h : (v.localA.product v.localB firstPostReceiverPending).raw 0 p = none := by
    rw [v.product_initial]
    exact v.raw_other_a p hp
  exact h

theorem localA_charge : v.localA.x 0 .q = 1 / 10 := by
  have h : (v.localA.product v.localB firstPostReceiverPending).x 0 .q = 1 / 10 := by
    rw [v.product_initial]; exact v.a_charge
  exact h

theorem localA_gain_preserved (p : Port) : v.localA.x 0 (.z p) = s.localA.x 0 (.z p) := by
  change v.senderFinalA.x 0 (.z p) = s.localA.x 0 (.z p)
  rw [v.sender_final]
  change f.senderReturnA.final.x 0 (.z p) = _
  rw [f.senderReturnA.gains,w.fast.gains,w.fire.firelocal.gain_preserved]

theorem localA_gain {ε} (hb : PhysicalBox θ ε) :
    9 / 5 ≤ Real.exp (v.localA.x 0 (.z 0)) ∧ Real.exp (v.localA.x 0 (.z 0)) ≤ 2 := by
  rw [v.localA_gain_preserved]
  exact s.localA_gain hb

theorem queue_future (d : Delivery 2) (hd : d ∈ firstPostReceiverPending) : (184 : ℝ) ≤ d.due := by
  simp only [firstPostReceiverPending,constructedBBirthSources,List.mem_append] at hd
  rcases hd with hd | hd | hd <;> obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd <;>
    change (184 : ℝ) ≤ _ + 8 * (k.val : ℝ) <;> nlinarith [Nat.cast_nonneg (α := ℝ) k.val]

end FirstPostReceiverPair

structure ThirdSenderFire {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} (v : FirstPostReceiverPair g) where
  firelocal : FirstLearnedFire θ (fun _ _ => []) v.localA 0 0
  receiverSpan : LowRecoverySlowSpan g.fastB firelocal.final.time
  receiverTail : Execution (fun _ : Fin 1 => fresh) (fun _ _ => []) v.localB receiverSpan.final
  receiver_emissions : receiverTail.ledger.emissions = []
  receiver_deliveries : receiverTail.deliveries = []
  receiver_concat : receiverSpan.execution = v.receiverSpan.execution.append receiverTail
  before : Snapshot 2
  final : Snapshot 2
  span : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) v.final before
  fire : Jump (reciprocalEntryRouter forward backward) before final
  execution : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) v.final final
  product_before : before = firelocal.before.product receiverSpan.final firstPostReceiverPending
  product_final : final = firelocal.final.product receiverSpan.final
    (firstPostReceiverPending ++ reciprocalEntryRouter forward backward 0 final.time)
  clock : final.time = firelocal.final.time
  date : final.time = 176 + firelocal.latency
  early : 176 + 2 / 5 < final.time
  deadline : final.time < 176 + 9 / 10
  firing_gap : final.time = w.fire.final.time + 8
  pending : final.pending = firstPostReceiverPending ++ reciprocalEntryRouter forward backward 0 final.time
  span_emissions : span.ledger.emissions = []
  span_deliveries : span.deliveries = []
  emissions : execution.ledger.emissions = [(0,final.time)]
  deliveries : execution.deliveries = []
  a_values : final.x 0 = firelocal.final.x 0
  a_main_fast : final.main 0 = .fast
  a_charge : final.x 0 .q = 1
  a_aux_silent : final.aux 0 0 = .silent
  a_sensor_above : 1 / 10 < final.x 0 (.m 0)
  a_aux_other : ∀ p, p ≠ 0 → final.aux 0 p = .ready ∧ RestBand (final.x 0 (.m p))
  b_values : final.x 1 = receiverSpan.final.x 0
  b_main_slow : final.main 1 = .slow
  b_charge : 1 / 10 < final.x 1 .q ∧ final.x 1 .q ≤ 1 / 4
  b_aux_rest : ∀ p, final.aux 1 p = .ready ∧ RestBand (final.x 1 (.m p))
  b_raw_none : ∀ p, final.raw 1 p = none
  raw_active : final.raw 0 0 = some (176 : ℝ)
  raw_other_a : ∀ p, p ≠ 0 → final.raw 0 p = none
  gains : ∀ j p, final.x j (.z p) = v.final.x j (.z p)
  recovery : ∀ j, final.x j .b = v.final.x j .b
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final

/-- Construct A's own fresh response and extend the already existing B SLOW
execution to that actual firing date, then issue the new contact token. -/
theorem third_sender_fire_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (v : FirstPostReceiverPair g)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (ThirdSenderFire v) := by
  have hg := v.localA_gain hb.extend_old
  have ho : ∀ j p, j ≠ (0 : Fin 1) ∨ p ≠ 0 → v.localA.raw j p = none := by
    intro j p h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact v.localA_raw_other p (by simpa using h)
  obtain ⟨a⟩ := first_learned_fire_exists (route := fun _ _ => []) v.localA hb.extend_old
    v.localA_physical v.localA_raw_valid 0 0 v.localA_ready hg v.localA_raw_active ho (by
      intro d hd
      rw [v.localA_pending] at hd
      contradiction)
  have hdate : a.final.time = 176 + a.latency := by rw [a.date,v.localA_date]
  have hearly : 176 + 2 / 5 < a.final.time := by
    have h : v.localA.time + 2 / 5 < a.final.time := readyPulse_root_after_four_tenths (v.localA_ready 0).charge.2 hg.2
      (by rw [a.date]; linarith [a.early]) a.response_root
    rw [v.localA_date] at h
    exact h
  have hdeadline : a.final.time < 176 + 9 / 10 := by rw [hdate]; linarith [a.deadline]
  have hz : s.localA.x 0 (.z 0) = v.localA.x 0 (.z 0) := (v.localA_gain_preserved 0).symm
  have hstep : v.localA.time = s.localA.time + 8 := by
    change v.localA.time = s.final.time + 8
    rw [v.localA_date,s.date]
    norm_num
  have hgapLocal := w.fire.firelocal.firing_gap_eight_of_rest_gain a s.a_charge v.localA_charge hz hstep
  have hclockOld : w.fire.firelocal.final.time = w.fire.final.time :=
    (congrArg Snapshot.time w.fire.product_final).symm
  have hgap : a.final.time = w.fire.final.time + 8 := by rw [hgapLocal,hclockOld]
  have hend : a.final.time ≤ w.receiverFireLocal.time + 81 / 10 := by
    change a.final.time ≤ w.final.time + 81 / 10
    rw [hgap,w.date]
    linarith [(hdelay w.fire.final.time).1]
  have hBp : v.receiverSpan.final.pending = [] := by
    rw [v.receiverSpan.pending,g.fastB.pending,f.firelocal.pending]
    simp only [List.append_nil]
    rfl
  obtain ⟨bspan,btail,heB,hdB,hconcat⟩ := v.receiverSpan.continuation_exists hb.extend_new a.final.time
    (by linarith) hend (by intro d hd; rw [hBp] at hd; contradiction)
  have hstart : v.localA.time = v.localB.time := v.local_clock
  have hfinish : a.before.time = bspan.final.time := bspan.date.symm
  have hQ : ∀ d ∈ firstPostReceiverPending, a.before.time ≤ d.due := by
    intro d hd
    change a.final.time ≤ d.due
    linarith [FirstPostReceiverPair.queue_future d hd]
  obtain ⟨woven,heW,hdW⟩ := a.beforeExecution.product_neutral btail hstart hfinish
    a.before_emissions a.before_deliveries heB hdB firstPostReceiverPending hQ
    (reciprocalEntryRouter forward backward)
  let before := a.before.product bspan.final firstPostReceiverPending
  let final := a.final.product bspan.final
    (firstPostReceiverPending ++ reciprocalEntryRouter forward backward 0 a.final.time)
  let span : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) v.final before :=
    woven.cast_source v.product_initial.symm
  have hmode : before.main 0 = .ready := a.firstSilent.main_ready 0
  have hthreshold : before.x 0 .q = 1 := a.threshold
  have hfinal : final = { (setMain before 0 .fast) with
      pending := before.pending ++ reciprocalEntryRouter forward backward 0 before.time } := by
    dsimp [final,before]
    calc
      a.final.product bspan.final (firstPostReceiverPending ++ reciprocalEntryRouter forward backward 0 a.final.time) =
          (setMain a.before 0 .fast).product bspan.final
            (firstPostReceiverPending ++ reciprocalEntryRouter forward backward 0 a.final.time) :=
        congrArg (fun q : Snapshot 1 => q.product bspan.final
          (firstPostReceiverPending ++ reciprocalEntryRouter forward backward 0 a.final.time)) a.final_empty
      _ = _ := by rw [Snapshot.product_setMain_left]; rfl
  let jump : Jump (reciprocalEntryRouter forward backward) before final :=
    hfinal.symm ▸ Jump.fire before 0 hmode hthreshold
  let e : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) v.final final :=
    span.append (.cons (.jump jump) (.nil _))
  have hFast : final.main 0 = .fast := a.main_fast
  have hjEm : jump.ledger.emissions = [(0,before.time)] :=
    jump.ready_main_departure_emission 0 hmode (by rw [hFast]; decide)
  have hjDel : jump.deliveries = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have hz := jump.no_emissions_of_delivery d hd
    rw [hjEm] at hz
    contradiction
  have hsEm : span.ledger.emissions = [] := by
    exact (congrArg (fun L : Ledger 2 => L.emissions)
      (woven.cast_source_ledger v.product_initial.symm)).trans heW
  have hsDel : span.deliveries = [] := by
    exact (woven.cast_source_deliveries v.product_initial.symm).trans hdW
  refine ⟨{
    firelocal := a, receiverSpan := bspan, receiverTail := btail
    receiver_emissions := heB, receiver_deliveries := hdB, receiver_concat := hconcat
    before := before, final := final, span := span, fire := jump, execution := e
    product_before := rfl, product_final := rfl, clock := rfl, date := hdate, early := hearly, deadline := hdeadline
    firing_gap := hgap, pending := rfl, span_emissions := hsEm, span_deliveries := hsDel
    emissions := ?_, deliveries := ?_, a_values := rfl, a_main_fast := hFast, a_charge := a.charge
    a_aux_silent := a.aux_silent, a_sensor_above := a.sensor_above, a_aux_other := ?_
    b_values := rfl, b_main_slow := bspan.main_slow, b_charge := bspan.charge
    b_aux_rest := fun p => ⟨bspan.auxiliary 0 p,bspan.rest p⟩, b_raw_none := fun p => bspan.raw_none 0 p
    raw_active := ?_, raw_other_a := ?_, gains := ?_, recovery := ?_
    physical := e.physical_invariant hb v.physical, raw_valid := e.raw_valid v.raw_valid
  }⟩
  · simp only [e,Execution.emissions_append,hsEm,Execution.ledger,Move.ledger,
      hjEm,Ledger.add,Ledger.zero,List.nil_append,List.append_nil]
    rfl
  · simp only [e,Execution.deliveries_append,hsDel,Execution.deliveries,Move.deliveries,
      hjDel,List.append_nil]
  · intro p hp
    exact (a.execution.aux_no_input_rest_band 0 p ((v.localA_ready 0).auxiliary p).1
      ((v.localA_ready 0).auxiliary p).2 (v.localA_raw_other p hp)
      (by simp [NoArrivalAt,a.deliveries])).1
  · rw [show final.raw 0 0 = a.final.raw 0 0 from rfl,a.raw_active,v.localA_date]
  · intro p hp
    exact a.raw_other 0 p (Or.inr hp)
  · intro j p
    fin_cases j
    · have h := a.gain_preserved 0 p
      have hx : v.localA.x 0 = v.final.x 0 := by change v.senderFinalA.x 0 = _; exact v.a_values.symm
      exact h.trans (congrFun hx (.z p))
    · exact ((bspan.gains 0 p).trans (v.receiverSpan.gains 0 p).symm).trans (congrFun v.b_values (.z p)).symm
  · intro j
    fin_cases j
    · have h := a.recovery_preserved 0
      have hx : v.localA.x 0 = v.final.x 0 := by change v.senderFinalA.x 0 = _; exact v.a_values.symm
      exact h.trans (congrFun hx .b)
    · exact ((bspan.recovery 0).trans (v.receiverSpan.recovery 0).symm).trans (congrFun v.b_values .b).symm

namespace ThirdSenderFire
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
  {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} {v : FirstPostReceiverPair g} (a : ThirdSenderFire v)

theorem protocol_route : reciprocalEntryRouter forward backward 0 a.final.time =
    [⟨1,1,a.final.time + forward a.final.time⟩] := by
  classical
  rw [reciprocalEntryRouter.before_reverse forward backward 0 (by linarith [a.deadline])]
  have hg : (160 : ℝ) ≤ a.final.time ∧ a.final.time < 310 := by
    constructor <;> linarith [a.early,a.deadline]
  simp [Contact.route,teachingContact,hg.1,hg.2,Contact.token]

theorem protocol_pending : a.final.pending = firstPostReceiverPending ++
    [⟨1,1,a.final.time + forward a.final.time⟩] := by rw [a.pending,a.protocol_route]

theorem pending_length : a.final.pending.length = 46 := by
  rw [a.protocol_pending]
  simp [firstPostReceiverPending,constructedBBirthSources,sourceTrain]

theorem received_gap
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    79 / 10 ≤ (a.final.time + forward a.final.time) - w.final.time ∧
      (a.final.time + forward a.final.time) - w.final.time ≤ 81 / 10 := by
  rw [w.date]
  exact received_gap_eight_of_fire_gap a.firing_gap (hdelay w.fire.final.time) (hdelay a.final.time)

theorem receiver_recovery : a.final.x 1 .b = newborn.x .b := by rw [a.recovery,v.b_recovery]

theorem complete
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    CompleteThrough a.execution a.final.time := by
  have hfuture : ∀ d ∈ a.final.pending, a.final.time < d.due := by
    intro d hd
    rw [a.protocol_pending] at hd
    rcases List.mem_append.mp hd with h | h
    · linarith [FirstPostReceiverPair.queue_future d h,a.deadline]
    · have he := List.mem_singleton.mp h
      subst d
      change a.final.time < a.final.time + forward a.final.time
      linarith [(hdelay a.final.time).1]
  refine ⟨rfl,?_,hfuture⟩
  intro u
  apply BeforeGuards.no_jump
  · constructor
    · intro j
      by_cases hj : j = 0
      · subst j
        rw [a.a_main_fast,a.a_charge]
        norm_num
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst j
        rw [a.b_main_slow]
        exact a.b_charge.1
    · intro j p
      by_cases hj : j = 0
      · subst j
        by_cases hp : p = 0
        · subst p
          rw [a.a_aux_silent]
          exact a.a_sensor_above
        · rw [(a.a_aux_other p hp).1]
          linarith [(a.a_aux_other p hp).2.2]
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst j
        rw [(a.b_aux_rest p).1]
        linarith [(a.b_aux_rest p).2.2]
  · intro j p origin hraw
    by_cases hj : j = 0
    · subst j
      by_cases hp : p = 0
      · subst p
        have ho : origin = (176 : ℝ) := Option.some.inj (hraw.symm.trans a.raw_active)
        rw [ho]
        linarith [a.deadline]
      · rw [a.raw_other_a p hp] at hraw
        contradiction
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j
      rw [a.b_raw_none p] at hraw
      contradiction
  · exact hfuture

end ThirdSenderFire
end KernelR.Hybrid
