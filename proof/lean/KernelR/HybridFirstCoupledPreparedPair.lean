import KernelR.HybridThirdWiredArrival
import KernelR.HybridLearnedSenderReturnAtNext
import KernelR.HybridProtectedInputShortCycle

/-! Construct the common prepared section184 from the third actual contact.
Only the existing external A184 token is consumed at the final boundary. -/
namespace KernelR.Hybrid

noncomputable def firstCoupledPreparedPending : List (Delivery 2) :=
  sourceTrain 0 0 192 8 12 ++ constructedBBirthSources

theorem firstCoupledPreparedPending_future (d : Delivery 2)
    (hd : d ∈ firstCoupledPreparedPending) : (192 : ℝ) ≤ d.due := by
  simp only [firstCoupledPreparedPending,constructedBBirthSources,List.mem_append] at hd
  rcases hd with hd | hd | hd <;> obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd <;>
    change (192 : ℝ) ≤ _ + 8 * (k.val : ℝ) <;> nlinarith [Nat.cast_nonneg (α := ℝ) k.val]

structure FirstCoupledPreparedPair {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} {v : FirstPostReceiverPair g}
    (t : ThirdWiredArrival v) where
  sender : LearnedSenderReturnAtNext t.fire.firelocal t.fast t.cutA
  receiver : ProtectedInputShortCycle (fun _ : Fin 1 => fresh) (fun _ _ => []) t.receiverLocal 1
  receiverFinal : Snapshot 1
  receiver_final : receiverFinal = quietAt receiver.final 184
  receiverWait : Execution (fun _ : Fin 1 => fresh) (fun _ _ => []) receiver.final receiverFinal
  before : Snapshot 2
  final : Snapshot 2
  span : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) t.final before
  arrival : Jump (reciprocalEntryRouter forward backward) before final
  execution : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) t.final final
  reconstruct : execution = span.append (.cons (.jump arrival) (.nil _))
  product_before : before = sender.final.product receiverFinal firstPostReceiverPending
  product_final : final = (setRaw sender.final 0 0 (some (184 : ℝ))).product receiverFinal firstCoupledPreparedPending
  date : final.time = 184
  ready : ∀ j, ReadyCoordinates final j
  prepared : ∀ j, PreparedSection final j
  charge : ∀ j, final.x j .q = 1 / 10
  raw_active : final.raw 0 0 = some (184 : ℝ)
  raw_other : ∀ j p, j ≠ 0 ∨ p ≠ 0 → final.raw j p = none
  pending : final.pending = firstCoupledPreparedPending
  gains : ∀ j p, final.x j (.z p) = t.final.x j (.z p)
  a_gains : ∀ p, final.x 0 (.z p) = b.final.x 0 (.z p)
  a_recovery : final.x 0 .b = b.final.x 0 .b
  a_recovery_current : final.x 0 .b = t.final.x 0 .b
  b_recovery_gain : final.x 1 .b = t.final.x 1 .b + 1 / 10
  span_emissions : span.ledger.emissions = []
  span_deliveries : span.deliveries = []
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨0,0,184⟩]
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final

/-- Both continuations start at the real third-wire state. They are woven at
184 before A's already queued source is actually delivered. -/
theorem first_coupled_prepared_pair_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
    {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} {v : FirstPostReceiverPair g}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (t : ThirdWiredArrival v)
    (hdelay : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    Nonempty (FirstCoupledPreparedPair t) := by
  obtain ⟨a⟩ := learned_sender_return_at_next_exists hb.extend_old t.fire.firelocal t.fast t.cutA
    v.localA_prepared v.localA_pending
  have hAdate : a.final.time = 184 := by rw [a.date,v.localA_date]; norm_num
  obtain ⟨rc⟩ := protected_input_short_cycle_exists (route := fun _ _ => []) hb.extend_new t.receiverLocal 1
    t.receiver_physical t.receiver_raw_valid t.receiver_main_slow
    ⟨t.receiver_charge.1.le,t.receiver_charge.2.le⟩ t.receiver_low_b t.receiver_aux_rest
    t.receiver_rawfresh t.receiver_raw_other (by intro d hd; rw [t.receiver_pending] at hd; contradiction)
  have hBwait : rc.final.time < (184 : ℝ) := by
    rw [rc.date]
    change t.final.time + 13 / 2 < (184 : ℝ)
    linarith [(t.date_bounds hdelay).2]
  have hBpending : rc.final.pending = [] := rc.pending.trans t.receiver_pending
  let bflow : Flow (fun _ : Fin 1 => fresh) rc.final (quietAt rc.final 184) := quietFlow rc.final hBwait
    (fun j => (rc.ready j).ready) (fun j p => ((rc.ready j).auxiliary p).1) rc.raw_none
    (fun j => by linarith [(rc.ready j).charge.2])
    (fun j p => by linarith [((rc.ready j).auxiliary p).2.2])
    (by intro d hd; rw [hBpending] at hd; contradiction)
  let bwait : Execution (fun _ : Fin 1 => fresh) (fun _ _ => []) rc.final (quietAt rc.final 184) := .cons (.flow bflow) (.nil _)
  let bfinal := quietAt rc.final 184
  let be := rc.execution.append bwait
  have heB : be.ledger.emissions = [] := by rw [Execution.emissions_append,rc.emissions]; rfl
  have hdB : be.deliveries = [] := by rw [Execution.deliveries_append,rc.deliveries]; rfl
  have hBready : ∀ j, ReadyCoordinates bfinal j := fun j => quietAt_ready_coordinates rc.final j (rc.ready j) hBwait.le
  have hBprepared : ∀ j, PreparedSection bfinal j := fun j =>
    ⟨(hBready j).ready,(hBready j).charge,(rc.prepared j).recovery,(hBready j).auxiliary⟩
  have hBcharge : bfinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (rc.final.x 0 .q) rc.final.time 184 = 1 / 10
    rw [rc.charge]; simp [relax]
  have hstart : t.cutA.state.time = t.receiverLocal.time := by
    change t.cutA.state.time = t.final.time
    exact t.cutA.date.trans t.date.symm
  have hfinish : a.final.time = bfinal.time := hAdate
  have hQ : ∀ d ∈ firstPostReceiverPending, a.final.time ≤ d.due := by
    rw [hAdate]
    exact FirstPostReceiverPair.queue_future
  obtain ⟨woven,heW,hdW⟩ := a.execution.product_neutral be hstart hfinish
    a.emissions a.deliveries heB hdB firstPostReceiverPending hQ (reciprocalEntryRouter forward backward)
  let span := woven.cast_source t.receiver_product_initial.symm
  have heSpan : span.ledger.emissions = [] := by rw [Execution.cast_source_ledger]; exact heW
  have hdSpan : span.deliveries = [] := by rw [Execution.cast_source_deliveries]; exact hdW
  let before := a.final.product bfinal firstPostReceiverPending
  have hqueue : before.pending = [] ++ (⟨0,0,184⟩ : Delivery 2) :: firstCoupledPreparedPending := by
    change firstPostReceiverPending = _
    rw [firstPostReceiverPending,sourceTrain_succ]
    norm_num [firstCoupledPreparedPending]
  have hfree : before.raw 0 0 = none := a.raw_none 0 0
  let final : Snapshot 2 := { (setRaw before 0 0 (some before.time)) with pending := firstCoupledPreparedPending }
  let arrival : Jump (reciprocalEntryRouter forward backward) before final :=
    .arrive before ⟨0,0,184⟩ [] firstCoupledPreparedPending hqueue hAdate.symm hfree
  let e := span.append (.cons (.jump arrival) (.nil _))
  have hready : ∀ j, ReadyCoordinates final j := by
    intro j
    fin_cases j
    · exact ⟨(a.ready 0).ready,(a.ready 0).charge,(a.ready 0).auxiliary⟩
    · exact ⟨(hBready 0).ready,(hBready 0).charge,(hBready 0).auxiliary⟩
  have hprepared : ∀ j, PreparedSection final j := by
    intro j
    fin_cases j
    · exact ⟨(a.prepared 0).ready,(a.prepared 0).charge,(a.prepared 0).recovery,(a.prepared 0).auxiliary⟩
    · exact ⟨(hBprepared 0).ready,(hBprepared 0).charge,(hBprepared 0).recovery,(hBprepared 0).auxiliary⟩
  have hrawA : final.raw 0 0 = some (184 : ℝ) := by simp [final,setRaw,before,Snapshot.product,hAdate]
  have hrawOther : ∀ j p, j ≠ (0 : Fin 2) ∨ p ≠ 0 → final.raw j p = none := by
    intro j p h
    fin_cases j
    · have hp : p ≠ 0 := by simpa using h
      have hr : before.raw 0 p = none := a.raw_none 0 p
      simpa [final,setRaw,Function.update_apply,hp] using hr
    · have hr : before.raw 1 p = none := rc.raw_none 0 p
      simpa [final,setRaw,Function.update_apply] using hr
  have hem : e.ledger.emissions = [] := by
    have hj : arrival.ledger.emissions = [] := rfl
    simp only [e,Execution.emissions_append,heSpan,Execution.ledger,Move.ledger,hj,Ledger.add,Ledger.zero,List.nil_append]
  have hdel : e.deliveries = [⟨0,0,184⟩] := by
    have hj : arrival.deliveries = [⟨0,0,184⟩] := rfl
    simp only [e,Execution.deliveries_append,hdSpan,Execution.deliveries,Move.deliveries,hj,List.nil_append,List.append_nil]
  refine ⟨{
    sender := a, receiver := rc, receiverFinal := bfinal, receiver_final := rfl, receiverWait := bwait
    before := before, final := final, span := span, arrival := arrival, execution := e, reconstruct := rfl
    product_before := rfl
    product_final := ?_
    date := hAdate
    ready := hready
    prepared := hprepared
    charge := ?_
    raw_active := hrawA
    raw_other := hrawOther
    pending := rfl
    gains := ?_
    a_gains := ?_
    a_recovery := ?_
    a_recovery_current := ?_
    b_recovery_gain := rc.recovery_gain
    span_emissions := heSpan
    span_deliveries := hdSpan
    emissions := hem
    deliveries := hdel
    physical := e.physical_invariant hb t.physical
    raw_valid := e.raw_valid t.raw_valid
  }⟩
  · change { (setRaw (a.final.product bfinal firstPostReceiverPending) 0 0 (some a.final.time)) with pending := firstCoupledPreparedPending } = _
    rw [hAdate,← Snapshot.product_setRaw_left]
    rfl
  · intro j
    fin_cases j
    · exact a.charge
    · exact hBcharge
  · intro j p
    fin_cases j
    · exact (a.gains 0 p).trans (congrFun t.sender_values (.z p)).symm
    · exact rc.gains 0 p
  · intro p
    exact (a.gains_source 0 p).trans ((v.localA_gain_preserved p).trans (s.a_gains p))
  · have hvb : v.localA.x 0 .b = s.localA.x 0 .b := by
      change v.senderFinalA.x 0 .b = s.localA.x 0 .b
      rw [v.sender_final]
      change f.senderReturnA.final.x 0 .b = _
      rw [f.senderReturnA.recovery,w.fast.recovery,w.fire.firelocal.recovery_preserved]
    exact (a.recovery_source 0).trans (hvb.trans s.a_recovery)
  · exact (a.recovery 0).trans (congrFun t.sender_values .b).symm

namespace FirstCoupledPreparedPair
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} {s : FirstInterleavedPair r} {w : SecondWiredArrival s}
  {f : FirstReceiverFire w} {g : FirstReceiverFastEnd f} {v : FirstPostReceiverPair g}
  {t : ThirdWiredArrival v} (x : FirstCoupledPreparedPair t)

noncomputable def staged : StagedExecution θ fresh (fun _ _ => []) (reciprocalEntryRouter forward backward) born x.final :=
  { t.staged with after := t.staged.after.append x.execution }

theorem pending_length : x.final.pending.length = 44 := by
  rw [x.pending]
  simp [firstCoupledPreparedPending,constructedBBirthSources,sourceTrain]

theorem raw_receiver (p : Port) : x.final.raw 1 p = none := x.raw_other 1 p (Or.inl (by decide))

theorem raw_other_a (p : Port) (hp : p ≠ 0) : x.final.raw 0 p = none := x.raw_other 0 p (Or.inr hp)

theorem b_error_zero (p : Port) : x.execution.ledger.error 1 p = 0 := by
  have h := x.execution.gain_balance 1 p
  rw [x.gains] at h
  linarith

theorem b_mark_other (p : Port) (hp : p ≠ 1) : x.execution.ledger.mark 1 p = 0 := by
  have hquiet := x.execution.aux_ready_without_input_band 1 p (t.receiver_aux_rest p).1
    (t.receiver_aux_rest p).2.2 (t.raw_other_b p hp) (by simp [NoArrivalAt,x.deliveries])
  exact x.execution.mark_zero_aux 1 p .ready (by decide) (x.execution.allStates_aux_flows 1 p .ready hquiet)

theorem b_mark_dose : x.execution.ledger.mark 1 1 = 1 / 10 := by
  have h := x.execution.recovery_balance 1
  rw [x.b_recovery_gain,x.execution.recovery_sum_marks 1,
    Finset.sum_eq_single 1 (fun p _ hp => x.b_mark_other p hp) (by simp)] at h
  linarith

theorem b_gain_target {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    x.final.x 1 (.z 1) = newborn.x (.z 1) + 3 / 5 := by
  rw [x.gains,t.receiver_gain_target hb hdelay]

theorem b_recovery_own : x.final.x 1 .b = newborn.x .b + 1 / 10 := by
  rw [x.b_recovery_gain,t.receiver_recovery]

theorem a_gain_target {ε} (hb : PhysicalBox θ ε) :
    x.final.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5 := by
  obtain ⟨outcome⟩ := c.outcome hb
  rw [x.a_gains,b.a_gain_preserved,outcome.gain_target]

theorem a_gain_other {ε} (hb : PhysicalBox θ ε) (p : Port) (hp : p ≠ 0) :
    x.final.x 0 (.z p) = born.x 0 (.z p) := by
  obtain ⟨outcome⟩ := c.outcome hb
  rw [x.a_gains,b.a_gain_preserved,outcome.gain_other p hp]

theorem a_recovery_own {ε} (hb : PhysicalBox θ ε) :
    x.final.x 0 .b = born.x 0 .b + 1 / 10 := by
  obtain ⟨outcome⟩ := c.outcome hb
  rw [x.a_recovery,b.a_recovery,outcome.recovery_gain]

theorem complete : CompleteThrough x.execution 184 := by
  have hfuture : ∀ d ∈ x.final.pending, (184 : ℝ) < d.due := by
    intro d hd
    rw [x.pending] at hd
    linarith [firstCoupledPreparedPending_future d hd]
  refine ⟨x.date,?_,hfuture⟩
  intro u
  apply BeforeGuards.no_jump
  · constructor
    · intro j
      rw [(x.ready j).ready]
      linarith [(x.ready j).charge.2]
    · intro j p
      rw [((x.ready j).auxiliary p).1]
      linarith [((x.ready j).auxiliary p).2.2]
  · intro j p origin hr
    fin_cases j
    · change x.final.raw 0 p = some origin at hr
      by_cases hp : p = 0
      · subst p
        have he : origin = (184 : ℝ) := Option.some.inj (hr.symm.trans x.raw_active)
        rw [he,x.date]; norm_num
      · rw [x.raw_other_a p hp] at hr; contradiction
    · change x.final.raw 1 p = some origin at hr
      rw [x.raw_receiver p] at hr; contradiction
  · intro d hd
    rw [x.date]
    exact hfuture d hd

theorem staged_complete : CompleteThrough x.staged.after 184 := x.complete

theorem staged_emissions : x.staged.after.ledger.emissions =
    [(0,r.fire.final.time),(0,w.fire.final.time),(1,f.final.time),(0,t.fire.final.time)] := by
  change ((v.staged.after.append t.execution).append x.execution).ledger.emissions = _
  rw [Execution.emissions_append,Execution.emissions_append,v.staged_emissions,t.emissions,x.emissions]
  rfl

theorem staged_deliveries : x.staged.after.deliveries =
    [⟨0,0,160⟩,⟨1,1,r.final.time⟩,⟨0,0,168⟩,⟨1,1,w.final.time⟩,⟨0,0,176⟩,⟨1,1,t.final.time⟩,⟨0,0,184⟩] := by
  change ((v.staged.after.append t.execution).append x.execution).deliveries = _
  rw [Execution.deliveries_append,Execution.deliveries_append,v.staged_deliveries,t.deliveries,x.deliveries]
  rfl

theorem b_gain_other (p : Port) (hp : p ≠ 1) : x.final.x 1 (.z p) = newborn.x (.z p) := by
  have hno : NoArrivalAt x.staged.after 1 p := by
    simp [NoArrivalAt,x.staged_deliveries,Ne.symm hp]
  have h := x.staged.after.aux_no_input_rest_band 1 p ((b.birth.new_ready).auxiliary p).1
    ((b.birth.new_ready).auxiliary p).2 (b.birth.new_raw p) hno
  have hx : b.afterBirth.x 1 (.z p) = newborn.x (.z p) := by
    have he := congrFun b.birth.new_coordinates (.z p)
    rw [b.newborn_state] at he
    exact he
  exact h.2.trans hx

end FirstCoupledPreparedPair

/-- The original A birth and independent B birth physically reach the common
prepared section184. No reaching execution or desired output/input list is an input. -/
theorem birth_protocol_first_coupled_prepared_pair_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hdelay : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r, ∃ w : SecondWiredArrival s,
          ∃ f : FirstReceiverFire w, ∃ g : FirstReceiverFastEnd f, ∃ v : FirstPostReceiverPair g,
            ∃ t : ThirdWiredArrival v, ∃ x : FirstCoupledPreparedPair t,
              CompleteThrough x.staged.after 184 ∧ x.final.pending.length = 44 ∧
                x.staged.after.ledger.emissions = [(0,r.fire.final.time),(0,w.fire.final.time),(1,f.final.time),(0,t.fire.final.time)] ∧
                x.staged.after.deliveries = [⟨0,0,160⟩,⟨1,1,r.final.time⟩,⟨0,0,168⟩,⟨1,1,w.final.time⟩,⟨0,0,176⟩,⟨1,1,t.final.time⟩,⟨0,0,184⟩] := by
  obtain ⟨c,b,r,s,w,f,g,v,t,_,_⟩ := birth_protocol_third_wired_arrival_exists hborn hb ha hqueue newborn forward backward hdelay
  obtain ⟨x⟩ := first_coupled_prepared_pair_exists hb t hdelay
  exact ⟨c,b,r,s,w,f,g,v,t,x,x.staged_complete,x.pending_length,x.staged_emissions,x.staged_deliveries⟩

end KernelR.Hybrid
