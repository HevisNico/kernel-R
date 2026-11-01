import KernelR.HybridThirdSenderFire
import KernelR.HybridLowRecoverySlowContinuation
import KernelR.HybridLearnedFastEnd

/-! The third genuine A contact is delivered to B's continuing SLOW state.
Its token is issued by the actual A FIRE, never preloaded into a global queue. -/
namespace KernelR.Hybrid

structure ThirdWiredArrival {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} (v : FirstPostReceiverPair g) where
  fire : ThirdSenderFire v
  fast : LearnedFastEnd fire.firelocal
  cutA : fast.execution.BeforeFlowCut (fire.final.time + forward fire.final.time)
  receiverSpan : LowRecoverySlowSpan g.fastB (fire.final.time + forward fire.final.time)
  receiverTail : Execution (fun _ : Fin 1 => fresh) (fun _ _ => []) fire.receiverSpan.final receiverSpan.final
  receiver_emissions : receiverTail.ledger.emissions = []
  receiver_deliveries : receiverTail.deliveries = []
  receiver_concat : receiverSpan.execution = fire.receiverSpan.execution.append receiverTail
  final : Snapshot 2
  span : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) fire.final final
  product_final : final = cutA.state.product
    (setRaw receiverSpan.final 0 1 (some (fire.final.time + forward fire.final.time))) firstPostReceiverPending
  date : final.time = fire.final.time + forward fire.final.time
  pending : final.pending = firstPostReceiverPending
  sender_values : final.x 0 = cutA.state.x 0
  sender_main : final.main 0 = cutA.state.main 0
  sender_aux : ∀ p, final.aux 0 p = cutA.state.aux 0 p
  sender_raw : ∀ p, final.raw 0 p = cutA.state.raw 0 p
  receiver_values : final.x 1 = receiverSpan.final.x 0
  receiver_main_slow : final.main 1 = .slow
  receiver_charge : 7 / 50 < final.x 1 .q ∧ final.x 1 .q < 4 / 25
  receiver_aux_rest : ∀ p, final.aux 1 p = .ready ∧ RestBand (final.x 1 (.m p))
  receiver_sensor_rest : final.x 1 (.m 1) = 1 / 40
  raw_active : final.raw 1 1 = some final.time
  raw_other_b : ∀ p, p ≠ 1 → final.raw 1 p = none
  gains : ∀ j p, final.x j (.z p) = fire.final.x j (.z p)
  recovery : ∀ j, final.x j .b = fire.final.x j .b
  span_emissions : span.ledger.emissions = []
  span_deliveries : span.deliveries = [⟨1,1,final.time⟩]
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final

/-- Extend both current local paths to the real token date, then consume its
last occurrence in Q++[wire]. The sender cut has discharged all coincident guards. -/
theorem third_wired_arrival_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (v : FirstPostReceiverPair g)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (ThirdWiredArrival v) := by
  obtain ⟨a⟩ := third_sender_fire_exists hb v hdelay
  have hclock : a.firelocal.final.time = a.final.time := a.clock.symm
  obtain ⟨fast⟩ := a.firelocal.learned_fast_end_exists hb.extend_old (v.localA_ready 0)
    (v.localA_gain hb.extend_old).2 v.localA_raw_other (by
      intro d hd
      rw [v.localA_pending] at hd
      contradiction)
  let H := a.final.time + forward a.final.time
  obtain ⟨cut⟩ := fast.execution.before_flow_cut_exists H
    (by rw [hclock]; dsimp [H]; linarith [(hdelay a.final.time).1])
    (by rw [fast.date,hclock]; dsimp [H]; linarith [(hdelay a.final.time).2])
  have heA : cut.cut.ledger.emissions = [] := by
    exact (List.append_eq_nil_iff.mp (cut.emissions.symm.trans fast.emissions)).1
  have hdA : cut.cut.deliveries = [] := by
    exact (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans fast.deliveries)).1
  have hgap : (79 / 10 : ℝ) ≤ H - w.final.time ∧ H - w.final.time ≤ 81 / 10 := a.received_gap hdelay
  have hBpending : a.receiverSpan.final.pending = [] := by
    rw [a.receiverSpan.pending,g.fastB.pending,f.firelocal.pending]
    simp only [List.append_nil]
    rfl
  obtain ⟨bspan,btail,heB,hdB,hconcat⟩ := a.receiverSpan.continuation_exists hb.extend_new H
    (by rw [← a.clock]; dsimp [H]; linarith [(hdelay a.final.time).1])
    (by change H ≤ w.final.time + 81 / 10; linarith [hgap.2])
    (by intro d hd; rw [hBpending] at hd; contradiction)
  have hnear : w.receiverFireLocal.time + 79 / 10 ≤ H := by
    change w.final.time + 79 / 10 ≤ H
    linarith [hgap.1]
  have hQ : ∀ d ∈ firstPostReceiverPending, cut.state.time < d.due := by
    intro d hd
    rw [cut.date]
    dsimp [H]
    linarith [FirstPostReceiverPair.queue_future d hd,a.deadline,(hdelay a.final.time).2]
  let Q := firstPostReceiverPending ++ [⟨1,1,H⟩]
  have hQall : ∀ d ∈ Q, cut.state.time ≤ d.due := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact (hQ d hd).le
    · have heq : d = (⟨1,1,H⟩ : Delivery 2) := List.mem_singleton.mp hd
      subst d
      exact cut.date.le
  have hstart : a.firelocal.final.time = a.receiverSpan.final.time := a.receiverSpan.date.symm
  have hfinish : cut.state.time = bspan.final.time := cut.date.trans bspan.date.symm
  obtain ⟨woven,heW,hdW⟩ := cut.cut.product_neutral btail hstart hfinish
    heA hdA heB hdB Q hQall (reciprocalEntryRouter forward backward)
  have hsource : a.firelocal.final.product a.receiverSpan.final Q = a.final := by
    have h := a.product_final
    rw [a.protocol_route] at h
    exact h.symm
  let before := cut.state.product bspan.final Q
  let final : Snapshot 2 := { (setRaw before 1 1 (some before.time)) with pending := firstPostReceiverPending }
  have hfree : before.raw 1 1 = none := bspan.raw_none 0 1
  have hqueue : before.pending = firstPostReceiverPending ++ (⟨1,1,H⟩ : Delivery 2) :: [] := rfl
  let arrival : Jump (reciprocalEntryRouter forward backward) before final :=
    .arrive before ⟨1,1,H⟩ firstPostReceiverPending [] hqueue cut.date.symm hfree
  let lifted := woven.cast_source hsource.symm
  let trace := lifted.append (.cons (.jump arrival) (.nil _))
  have hEm : trace.ledger.emissions = [] := by
    have hl : lifted.ledger.emissions = [] := by
      simpa only [lifted,Execution.cast_source_ledger] using heW
    have hj : arrival.ledger.emissions = [] := rfl
    simp only [trace,Execution.emissions_append,hl,Execution.ledger,Move.ledger,hj,Ledger.add,Ledger.zero,List.nil_append]
  have hDel : trace.deliveries = [⟨1,1,final.time⟩] := by
    have hl : lifted.deliveries = [] := by
      simpa only [lifted,Execution.cast_source_deliveries] using hdW
    have hj : arrival.deliveries = [⟨1,1,H⟩] := rfl
    simp only [trace,Execution.deliveries_append,hl,Execution.deliveries,Move.deliveries,hj,List.nil_append]
    change [(⟨1,1,H⟩ : Delivery 2)] = [(⟨1,1,cut.state.time⟩ : Delivery 2)]
    rw [cut.date]
  have hBraw : ∀ p, p ≠ 1 → final.raw 1 p = none := by
    intro p hp
    have h : before.raw 1 p = none := bspan.raw_none 0 p
    simpa [final,setRaw,Function.update_apply,hp] using h
  have hBmain : final.main 1 = .slow := bspan.main_slow
  have hBcharge : 7 / 50 < final.x 1 .q ∧ final.x 1 .q < 4 / 25 := bspan.near_charge hnear
  have hBaux : ∀ p, final.aux 1 p = .ready ∧ RestBand (final.x 1 (.m p)) :=
    fun p => ⟨bspan.auxiliary 0 p,bspan.rest p⟩
  refine ⟨{
    fire := a, fast := fast, cutA := cut, receiverSpan := bspan, receiverTail := btail
    receiver_emissions := heB, receiver_deliveries := hdB, receiver_concat := hconcat
    final := final, span := trace
    product_final := ?_
    date := cut.date
    pending := rfl
    sender_values := rfl
    sender_main := rfl
    sender_aux := fun _ => rfl
    sender_raw := ?_
    receiver_values := rfl
    receiver_main_slow := hBmain
    receiver_charge := hBcharge
    receiver_aux_rest := hBaux
    receiver_sensor_rest := bspan.trained_rest
    raw_active := ?_
    raw_other_b := hBraw
    gains := ?_
    recovery := ?_
    span_emissions := hEm
    span_deliveries := hDel
    physical := trace.physical_invariant hb a.physical
    raw_valid := trace.raw_valid a.raw_valid
  }⟩
  · have hrawdate : some cut.state.time = some H := congrArg some cut.date
    change { (setRaw (cut.state.product bspan.final Q) 1 1 (some cut.state.time)) with pending := firstPostReceiverPending } = _
    rw [← hrawdate,Snapshot.product_setRaw_right]
    rfl
  · intro p
    have h : before.raw 0 p = cut.state.raw 0 p := rfl
    simpa [final,setRaw,Function.update_apply] using h
  · simp [final,setRaw]
  · intro j p
    fin_cases j
    · have h1 := cut.cut.gain_nondecreasing hb.extend_old 0 p
      let tailA : Execution θ (fun _ _ => []) cut.state fast.final := .cons (.flow cut.flow) cut.rest
      have h2 := tailA.gain_nondecreasing hb.extend_old 0 p
      have h3 := fast.gains 0 p
      have hc : cut.state.x 0 (.z p) = a.firelocal.final.x 0 (.z p) := by linarith
      exact hc.trans (congrFun a.a_values (.z p)).symm
    · have hc : bspan.final.x 0 (.z p) = a.receiverSpan.final.x 0 (.z p) :=
        (bspan.gains 0 p).trans (a.receiverSpan.gains 0 p).symm
      exact hc.trans (congrFun a.b_values (.z p)).symm
  · intro j
    fin_cases j
    · have h1 := cut.cut.recovery_nondecreasing hb.extend_old 0
      let tailA : Execution θ (fun _ _ => []) cut.state fast.final := .cons (.flow cut.flow) cut.rest
      have h2 := tailA.recovery_nondecreasing hb.extend_old 0
      have h3 := fast.recovery 0
      have hc : cut.state.x 0 .b = a.firelocal.final.x 0 .b := by linarith
      exact hc.trans (congrFun a.a_values .b).symm
    · have hc : bspan.final.x 0 .b = a.receiverSpan.final.x 0 .b :=
        (bspan.recovery 0).trans (a.receiverSpan.recovery 0).symm
      exact hc.trans (congrFun a.b_values .b).symm

namespace ThirdWiredArrival
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
  {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} {v : FirstPostReceiverPair g} (t : ThirdWiredArrival v)

noncomputable def execution : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) v.final t.final :=
  t.fire.execution.append t.span

noncomputable def staged : StagedExecution θ fresh (fun _ _ => [])
    (reciprocalEntryRouter forward backward) born t.final :=
  { v.staged with after := v.staged.after.append t.execution }

theorem date_bounds (hdelay : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    (176 + 7 / 10 : ℝ) < t.final.time ∧ t.final.time < 176 + 13 / 10 := by
  rw [t.date]
  constructor <;> linarith [t.fire.early,t.fire.deadline,(hdelay t.fire.final.time).1,(hdelay t.fire.final.time).2]

theorem received_gap (hdelay : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    (79 / 10 : ℝ) ≤ t.final.time - w.final.time ∧ t.final.time - w.final.time ≤ 81 / 10 := by
  rw [t.date]
  exact t.fire.received_gap hdelay

theorem pending_length : t.final.pending.length = 45 := by
  rw [t.pending]
  simp [firstPostReceiverPending,constructedBBirthSources,sourceTrain]

theorem receiver_gain_target {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    t.final.x 1 (.z 1) = newborn.x (.z 1) + 3 / 5 := by
  rw [t.gains,t.fire.gains,v.b_gain_target hb hdelay]

theorem receiver_recovery : t.final.x 1 .b = newborn.x .b := by
  rw [t.recovery,t.fire.receiver_recovery]

noncomputable def receiverLocal : Snapshot 1 := t.final.cellProjection 1 []

theorem receiver_pending : t.receiverLocal.pending = [] := rfl

theorem receiver_physical : PhysicalInvariant (fun _ : Fin 1 => fresh) t.receiverLocal := by
  have hθ : extendParameters θ fresh (1 : Fin 2) = fresh := rfl
  refine ⟨fun j => t.physical.region 1,?_,fun j => t.physical.recovery_cap 1,fun j => t.physical.reserve 1⟩
  intro j p
  change t.final.x 1 (.z p) ≤ Real.log (fresh.cap p)
  have h := t.physical.gain_cap 1 p
  change t.final.x 1 (.z p) ≤ Real.log ((extendParameters θ fresh 1).cap p) at h
  rwa [hθ] at h

theorem receiver_raw_valid : RawValid t.receiverLocal := fun _ p origin hr => t.raw_valid 1 p origin hr

theorem receiver_rawfresh : t.receiverLocal.raw 0 1 = some t.receiverLocal.time := t.raw_active

theorem receiver_raw_other : ∀ p, p ≠ 1 → t.receiverLocal.raw 0 p = none := t.raw_other_b

theorem receiver_low_b : 7999 / 100000 ≤ t.receiverLocal.x 0 .b ∧ t.receiverLocal.x 0 .b ≤ 8001 / 100000 := by
  change 7999 / 100000 ≤ t.final.x 1 .b ∧ t.final.x 1 .b ≤ 8001 / 100000
  rw [t.receiver_recovery]
  constructor <;> linarith [newborn.recovery.1,newborn.recovery.2]

/-- The original current A cut and B's freshly delivered local projection
reproduce the exact global state, while the local projection queue stays empty. -/
theorem receiver_product_initial : t.cutA.state.product t.receiverLocal firstPostReceiverPending = t.final := by
  have extensionality {n} (a u : Snapshot n) (ht : a.time = u.time) (hx : a.x = u.x)
      (hm : a.main = u.main) (ha : a.aux = u.aux) (hr : a.raw = u.raw)
      (hp : a.pending = u.pending) : a = u := by
    cases a
    cases u
    simp_all only
  apply extensionality
  · exact t.cutA.date.trans t.date.symm
  · funext j; fin_cases j
    · exact t.sender_values.symm
    · rfl
  · funext j; fin_cases j
    · exact t.sender_main.symm
    · rfl
  · funext j; fin_cases j
    · funext p; exact (t.sender_aux p).symm
    · rfl
  · funext j; fin_cases j
    · funext p; exact (t.sender_raw p).symm
    · rfl
  · exact t.pending.symm

theorem emissions : t.execution.ledger.emissions = [(0,t.fire.final.time)] := by
  rw [execution,Execution.emissions_append,t.fire.emissions,t.span_emissions,List.append_nil]

theorem deliveries : t.execution.deliveries = [⟨1,1,t.final.time⟩] := by
  rw [execution,Execution.deliveries_append,t.fire.deliveries,t.span_deliveries,List.nil_append]

theorem complete : CompleteThrough t.execution t.final.time := by
  have hg := t.cutA.before_guards
  have hguard : BeforeGuards t.final t.final.x := by
    constructor
    · intro j
      rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
      · rw [t.sender_main,t.sender_values]; exact hg.1 0
      · rw [t.receiver_main_slow]; linarith [t.receiver_charge.1]
    · intro j p
      rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
      · rw [t.sender_aux,t.sender_values]; exact hg.2 0 p
      · rw [(t.receiver_aux_rest p).1]; linarith [(t.receiver_aux_rest p).2.2]
  have hfinalcut : t.final.time = t.cutA.state.time := t.date.trans t.cutA.date.symm
  have hmax : t.final.time < t.fire.final.time + 1 := by
    rw [t.fire.clock,← t.fast.date,hfinalcut]
    exact t.cutA.flow.positive.trans_le t.cutA.rest.time_monotone
  have hfuture : ∀ d ∈ t.final.pending, t.final.time < d.due := by
    intro d hd
    rw [t.pending] at hd
    linarith [FirstPostReceiverPair.queue_future d hd,t.fire.deadline]
  refine ⟨rfl,?_,hfuture⟩
  intro u
  apply hguard.no_jump
  · intro j p origin hr
    rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
    · rw [t.sender_raw] at hr
      rw [hfinalcut]
      exact t.cutA.flow.initial_raw_strict 0 p origin hr
    · by_cases hp : p = 1
      · subst p
        have he : origin = t.final.time := Option.some.inj (hr.symm.trans t.raw_active)
        rw [he]; linarith
      · rw [t.raw_other_b p hp] at hr; contradiction
  · exact hfuture

theorem staged_complete : CompleteThrough t.staged.after t.final.time := t.complete

end ThirdWiredArrival

/-- The third actual contact is reached from the original A birth and a fresh B
family, with no supplied execution, output calendar or pulse-case outcome. -/
theorem birth_protocol_third_wired_arrival_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hdelay : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ w : SecondWiredArrival s,
          ∃ f : FirstReceiverFire w, ∃ g : FirstReceiverFastEnd f, ∃ v : FirstPostReceiverPair g,
            ∃ t : ThirdWiredArrival v, CompleteThrough t.staged.after t.final.time ∧ t.final.pending.length = 45 := by
  obtain ⟨c,b,r,s,w,f,g,v,_,_⟩ := birth_protocol_first_post_receiver_pair_exists hborn hb ha hqueue newborn forward backward hdelay
  obtain ⟨t⟩ := third_wired_arrival_exists hb v hdelay
  exact ⟨c,b,r,s,w,f,g,v,t,t.staged_complete,t.pending_length⟩

end KernelR.Hybrid
