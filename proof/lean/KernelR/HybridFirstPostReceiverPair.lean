import KernelR.HybridFirstReceiverFastEnd
import KernelR.HybridConstructedReceiverFire
import KernelR.HybridLowRecoverySlowSpan

/-! Reach the actual common clock176, retaining B's low-recovery SLOW residue,
then consume exactly the existing A176 source. No B arrival is scheduled. -/
namespace KernelR.Hybrid

noncomputable def firstPostReceiverPending : List (Delivery 2) :=
  sourceTrain 0 0 184 8 13 ++ constructedBBirthSources

structure FirstPostReceiverPair {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    {f : FirstReceiverFire w} (g : FirstReceiverFastEnd f) where
  receiverSpan : LowRecoverySlowSpan g.fastB 176
  senderFinalA : Snapshot 1
  sender_final : senderFinalA = quietAt f.senderReturnA.final 176
  senderRemainderA : Execution θ (fun _ _ => []) g.cutA.state senderFinalA
  sender_pending : senderFinalA.pending = []
  sender_emissions : senderRemainderA.ledger.emissions = []
  sender_deliveries : senderRemainderA.deliveries = []
  before : Snapshot 2
  final : Snapshot 2
  span : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) g.final before
  arrival : Jump (reciprocalEntryRouter forward backward) before final
  execution : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) g.final final
  product_before : before = senderFinalA.product receiverSpan.final firstInterleavedPending
  product_final : final = (setRaw senderFinalA 0 0 (some (176 : ℝ))).product receiverSpan.final firstPostReceiverPending
  date : final.time = 176
  pending : final.pending = firstPostReceiverPending
  a_prepared : PreparedSection final 0
  a_charge : final.x 0 .q = 1 / 10
  a_values : final.x 0 = senderFinalA.x 0
  b_values : final.x 1 = receiverSpan.final.x 0
  b_main_slow : final.main 1 = .slow
  b_aux_rest : ∀ p, final.aux 1 p = .ready ∧ RestBand (final.x 1 (.m p))
  b_sensor_rest : final.x 1 (.m 1) = 1 / 40
  b_charge : 1 / 10 < final.x 1 .q ∧ final.x 1 .q ≤ 1 / 4
  b_charge_clock : final.x 1 .q = (1 / 4 : ℝ) * Real.exp (-w.receiverFireLocal.x 0 .b *
    (176 - (w.receiverFireLocal.time + f.firelocal.latency + 1)))
  b_raw_none : ∀ p, final.raw 1 p = none
  raw_active : final.raw 0 0 = some (176 : ℝ)
  raw_other_a : ∀ p, p ≠ 0 → final.raw 0 p = none
  gains : ∀ j p, final.x j (.z p) = g.final.x j (.z p)
  recovery : ∀ j, final.x j .b = g.final.x j .b
  span_emissions : span.ledger.emissions = []
  span_deliveries : span.deliveries = []
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨0,0,176⟩]
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final

/-- Resume A's real remaining path, carry B's actual SLOW decay to176, weave
these empty-event traces, then perform the existing A-source arrival. -/
theorem first_post_receiver_pair_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    {f : FirstReceiverFire w}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (g : FirstReceiverFastEnd f)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (FirstPostReceiverPair g) := by
  have hbLow : 7999 / 100000 ≤ w.receiverFireLocal.x 0 .b ∧
      w.receiverFireLocal.x 0 .b ≤ 8001 / 100000 := by
    change 7999 / 100000 ≤ w.final.x 1 .b ∧ w.final.x 1 .b ≤ 8001 / 100000
    rw [w.receiver_recovery]
    constructor <;> linarith [newborn.recovery.1,newborn.recovery.2]
  have hBpending : g.fastB.final.pending = [] := by
    rw [g.fastB.pending,f.firelocal.pending]
    simp only [List.append_nil]
    rfl
  obtain ⟨bspan⟩ := f.firelocal.low_recovery_slow_span_exists hb.extend_new g.fastB
    (w.receiver_fire_ready 0) (w.receiver_gain_bounds hb hdelay).2 hbLow 176
    (by rw [← g.clock]; linarith [g.horizon])
    (by change (176 : ℝ) ≤ w.final.time + 81 / 10; linarith [(w.date_bounds hdelay).1]) (by
      intro d hd
      rw [hBpending] at hd
      contradiction)
  let restA : Execution θ (fun _ _ => []) g.cutA.state f.senderReturnA.final :=
    .cons (.flow g.cutA.flow) g.cutA.rest
  have heRest : restA.ledger.emissions = [] := by
    have h := g.cutA.emissions.symm.trans g.sender_emissions
    change [] ++ g.cutA.rest.ledger.emissions = []
    simpa using (List.append_eq_nil_iff.mp h).2
  have hdRest : restA.deliveries = [] := by
    have h := g.cutA.deliveries.symm.trans g.sender_deliveries
    change [] ++ g.cutA.rest.deliveries = []
    simpa using (List.append_eq_nil_iff.mp h).2
  have hApending : f.senderReturnA.final.pending = [] := by
    rw [f.senderReturnA.pending,w.fast.pending,w.fire.firelocal.pending]
    simp only [List.append_nil]
    rfl
  have hwait : f.senderReturnA.final.time < (176 : ℝ) := by rw [f.senderReturnA.date]; norm_num
  let flowA : Flow θ f.senderReturnA.final (quietAt f.senderReturnA.final 176) :=
    quietFlow f.senderReturnA.final hwait
      (fun j => (f.senderReturnA.ready j).ready)
      (fun j p => ((f.senderReturnA.ready j).auxiliary p).1) f.senderReturnA.raw_none
      (fun j => by linarith [(f.senderReturnA.ready j).charge.2])
      (fun j p => by linarith [((f.senderReturnA.ready j).auxiliary p).2.2]) (by
        intro d hd
        rw [hApending] at hd
        contradiction)
  let waitA : Execution θ (fun _ _ => []) f.senderReturnA.final (quietAt f.senderReturnA.final 176) :=
    .cons (.flow flowA) (.nil _)
  let afinal := quietAt f.senderReturnA.final 176
  let aexec : Execution θ (fun _ _ => []) g.cutA.state afinal := restA.append waitA
  have heA : aexec.ledger.emissions = [] := by
    rw [Execution.emissions_append,heRest]
    rfl
  have hdA : aexec.deliveries = [] := by
    rw [Execution.deliveries_append,hdRest]
    rfl
  have hAready : ∀ j, ReadyCoordinates afinal j :=
    fun j => quietAt_ready_coordinates f.senderReturnA.final j (f.senderReturnA.ready j) hwait.le
  have hAprepared : PreparedSection afinal 0 :=
    ⟨(hAready 0).ready,(hAready 0).charge,(f.senderReturnA.prepared 0).recovery,(hAready 0).auxiliary⟩
  have hAcharge : afinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (f.senderReturnA.final.x 0 .q) f.senderReturnA.final.time 176 = _
    rw [f.senderReturnA.charge]
    simp [relax]
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
  have hAgains (p : Port) : afinal.x 0 (.z p) = g.final.x 0 (.z p) := by
    have hStart : g.final.x 0 (.z p) = w.cut.state.x 0 (.z p) :=
      (g.gains 0 p).trans ((f.gains 0 p).trans (congrFun w.receipt.sender_values (.z p)))
    have hEnd := (f.senderReturnA.gains 0 p).trans (hOldGain p).symm
    exact hEnd.trans hStart.symm
  have hArecovery : afinal.x 0 .b = g.final.x 0 .b := by
    have hStart : g.final.x 0 .b = w.cut.state.x 0 .b :=
      (g.recovery 0).trans ((f.recovery 0).trans (congrFun w.receipt.sender_values .b))
    have hEnd := (f.senderReturnA.recovery 0).trans hOldRecovery.symm
    exact hEnd.trans hStart.symm
  have hstart : g.cutA.state.time = g.fastB.final.time := g.cutA.date
  have hfinish : afinal.time = bspan.final.time := by change (176 : ℝ) = bspan.final.time; exact bspan.date.symm
  have hQ : ∀ d ∈ firstInterleavedPending, afinal.time ≤ d.due :=
    FirstInterleavedPair.queue_future
  obtain ⟨woven,heW,hdW⟩ := aexec.product_neutral bspan.execution hstart hfinish heA hdA
    bspan.emissions bspan.deliveries firstInterleavedPending hQ (reciprocalEntryRouter forward backward)
  let before := afinal.product bspan.final firstInterleavedPending
  let span : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) g.final before :=
    woven.cast_source g.product_final
  have hsEm : span.ledger.emissions = [] := by
    simpa only [span,Execution.cast_source_ledger] using heW
  have hsDel : span.deliveries = [] := by
    simpa only [span,Execution.cast_source_deliveries] using hdW
  have hqueue : before.pending = [] ++ (⟨0,0,176⟩ : Delivery 2) :: firstPostReceiverPending := by
    change firstInterleavedPending = _
    rw [firstInterleavedPending,sourceTrain_succ]
    norm_num [firstPostReceiverPending]
  have hfree : before.raw 0 0 = none := f.senderReturnA.raw_none 0 0
  let final : Snapshot 2 := { (setRaw before 0 0 (some before.time)) with pending := [] ++ firstPostReceiverPending }
  let arrival : Jump (reciprocalEntryRouter forward backward) before final :=
    .arrive before ⟨0,0,176⟩ [] firstPostReceiverPending hqueue rfl hfree
  let e := span.append (.cons (.jump arrival) (.nil _))
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨0,0,176⟩] := rfl
  refine ⟨{
    receiverSpan := bspan, senderFinalA := afinal, sender_final := rfl, senderRemainderA := aexec
    sender_pending := hApending, sender_emissions := heA, sender_deliveries := hdA
    before := before, final := final, span := span, arrival := arrival, execution := e
    product_before := rfl, product_final := ?_, date := rfl, pending := rfl
    a_prepared := ⟨hAprepared.ready,hAprepared.charge,hAprepared.recovery,hAprepared.auxiliary⟩
    a_charge := hAcharge, a_values := rfl, b_values := rfl
    b_main_slow := bspan.main_slow, b_aux_rest := fun p => ⟨bspan.auxiliary 0 p,bspan.rest p⟩
    b_sensor_rest := bspan.trained_rest, b_charge := bspan.charge, b_charge_clock := bspan.charge_clock
    b_raw_none := ?_, raw_active := ?_, raw_other_a := ?_, gains := ?_, recovery := ?_
    span_emissions := hsEm, span_deliveries := hsDel, emissions := ?_, deliveries := ?_
    physical := e.physical_invariant hb g.physical, raw_valid := e.raw_valid g.raw_valid
  }⟩
  · dsimp [final,before]
    rw [Snapshot.product_setRaw_left]
    rfl
  · intro p
    have h : before.raw 1 p = none := bspan.raw_none 0 p
    simpa [final,setRaw,Function.update_apply] using h
  · simp [final,setRaw,before,Snapshot.product,afinal,quietAt]
  · intro p hp
    have h : before.raw 0 p = none := f.senderReturnA.raw_none 0 p
    simpa [final,setRaw,Function.update_apply,hp] using h
  · intro j p
    fin_cases j
    · exact hAgains p
    · exact (bspan.gains 0 p).trans (congrFun g.receiver_values (.z p)).symm
  · intro j
    fin_cases j
    · exact hArecovery
    · exact (bspan.recovery 0).trans (congrFun g.receiver_values .b).symm
  · simp only [e,Execution.emissions_append,hsEm,Execution.ledger,Move.ledger,
      Ledger.add,Ledger.zero,haEm,List.append_nil]
  · simp only [e,Execution.deliveries_append,hsDel,Execution.deliveries,
      Move.deliveries,haDel,List.nil_append,List.append_nil]

namespace FirstPostReceiverPair
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
  {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} (v : FirstPostReceiverPair g)

noncomputable def localA : Snapshot 1 := setRaw v.senderFinalA 0 0 (some (176 : ℝ))
noncomputable def localB : Snapshot 1 := v.receiverSpan.final

theorem product_initial : v.localA.product v.localB firstPostReceiverPending = v.final := v.product_final.symm

theorem pending_length : v.final.pending.length = 45 := by
  rw [v.pending]
  simp [firstPostReceiverPending,constructedBBirthSources,sourceTrain]

theorem localA_pending : v.localA.pending = [] := v.sender_pending

theorem local_clock : v.localA.time = v.localB.time := by
  change v.senderFinalA.time = v.receiverSpan.final.time
  rw [v.sender_final,v.receiverSpan.date]
  rfl

theorem b_recovery : v.final.x 1 .b = newborn.x .b := by rw [v.recovery,g.b_recovery]

theorem b_gain_target {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    v.final.x 1 (.z 1) = newborn.x (.z 1) + 3 / 5 := by
  rw [v.gains,g.b_gain_target hb hdelay]

theorem b_clock : v.final.x 1 .q = (1 / 4 : ℝ) * Real.exp (-newborn.x .b * (176 - g.fastB.final.time)) := by
  have ht : g.fastB.final.time = w.receiverFireLocal.time + f.firelocal.latency + 1 := by
    rw [g.fastB.date,f.firelocal.date]
  rw [v.b_charge_clock,ht]
  change (1 / 4 : ℝ) * Real.exp (-w.final.x 1 .b * _) = _
  rw [w.receiver_recovery]

theorem complete : CompleteThrough v.execution 176 := by
  have hguard : BeforeGuards v.final v.final.x := by
    constructor
    · intro j
      by_cases hj : j = 0
      · subst j
        rw [v.a_prepared.ready,v.a_charge]
        norm_num
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst j
        rw [v.b_main_slow]
        exact v.b_charge.1
    · intro j p
      by_cases hj : j = 0
      · subst j
        rw [(v.a_prepared.auxiliary p).1]
        linarith [(v.a_prepared.auxiliary p).2.2]
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst j
        rw [(v.b_aux_rest p).1]
        linarith [(v.b_aux_rest p).2.2]
  have hfuture : ∀ d ∈ v.final.pending, (176 : ℝ) < d.due := by
    intro d hd
    rw [v.pending] at hd
    simp only [firstPostReceiverPending,constructedBBirthSources,List.mem_append] at hd
    rcases hd with hd | hd | hd <;> obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd <;>
      dsimp <;> nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  refine ⟨v.date,?_,hfuture⟩
  intro u
  apply hguard.no_jump
  · intro j p origin hraw
    by_cases hj : j = 0
    · subst j
      by_cases hp : p = 0
      · subst p
        have ho : origin = (176 : ℝ) := Option.some.inj (hraw.symm.trans v.raw_active)
        rw [ho,v.date]
        norm_num
      · rw [v.raw_other_a p hp] at hraw
        contradiction
    · have hj1 : j = 1 := by fin_cases j <;> simp_all
      subst j
      rw [v.b_raw_none p] at hraw
      contradiction
  · intro d hd
    rw [v.date]
    exact hfuture d hd

/-- Extend the same original-birth witness, including its actual dimension
change at160, by the constructed continuation and the true A176 delivery. -/
noncomputable def staged : StagedExecution θ fresh (fun _ _ => [])
    (reciprocalEntryRouter forward backward) born v.final :=
  { g.staged with after := g.staged.after.append v.execution }

theorem staged_complete : CompleteThrough v.staged.after 176 := v.complete

theorem staged_emissions : v.staged.after.ledger.emissions =
    [(0,r.fire.final.time),(0,w.fire.final.time),(1,f.final.time)] := by
  change (g.staged.after.append v.execution).ledger.emissions = _
  rw [Execution.emissions_append,g.staged_emissions,v.emissions,List.append_nil]

theorem staged_deliveries : v.staged.after.deliveries =
    [⟨0,0,160⟩,⟨1,1,r.final.time⟩,⟨0,0,168⟩,⟨1,1,w.final.time⟩,⟨0,0,176⟩] := by
  change (g.staged.after.append v.execution).deliveries = _
  rw [Execution.deliveries_append,g.staged_deliveries,v.deliveries]
  rfl

end FirstPostReceiverPair

/-- From the original A birth and the independently fresh B family, actual
flows, jumps, contact deliveries and the birth transition reach clock176.
No reaching execution, firing calendar or prescribed response is assumed. -/
theorem birth_protocol_first_post_receiver_pair_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ w : SecondWiredArrival s,
          ∃ f : FirstReceiverFire w, ∃ g : FirstReceiverFastEnd f, ∃ v : FirstPostReceiverPair g,
            CompleteThrough v.staged.after 176 ∧ v.final.pending.length = 45 := by
  obtain ⟨c,b,r,s,w,f,g,_,_⟩ := birth_protocol_first_receiver_fast_end_exists hborn hb ha hqueue
    newborn forward backward hdelay
  obtain ⟨v⟩ := first_post_receiver_pair_exists hb g hdelay
  exact ⟨c,b,r,s,w,f,g,v,v.staged_complete,v.pending_length⟩

end KernelR.Hybrid
