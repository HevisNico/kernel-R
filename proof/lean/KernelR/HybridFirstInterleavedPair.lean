import KernelR.HybridNeutralExecutionProduct
import KernelR.HybridFirstReceiverWeak
import KernelR.HybridFirstSenderReturn

namespace KernelR.Hybrid

noncomputable def firstInterleavedPending : List (Delivery 2) :=
  sourceTrain 0 0 176 8 14 ++ constructedBBirthSources

structure FirstInterleavedPair {θ born fresh newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (r : FirstWiredArrival b) where
  sender : FirstSenderReturn r
  receiver : FirstReceiverWeak r
  final : Snapshot 2
  execution : Execution (extendParameters θ fresh) (reciprocalEntryRouter forward backward) r.final final
  date : final.time = 168
  a_prepared : PreparedSection final 0
  a_charge : final.x 0 .q = 1 / 10
  a_gains : ∀ p, final.x 0 (.z p) = b.final.x 0 (.z p)
  a_recovery : final.x 0 .b = b.final.x 0 .b
  b_values : final.x 1 = receiver.cut168.state.x 0
  b_main : final.main 1 = receiver.cut168.state.main 0
  b_aux : ∀ p, final.aux 1 p = receiver.cut168.state.aux 0 p
  b_raw : ∀ p, final.raw 1 p = receiver.cut168.state.raw 0 p
  raw_active : final.raw 0 0 = some (168 : ℝ)
  raw_other_a : ∀ p, p ≠ 0 → final.raw 0 p = none
  pending : final.pending = firstInterleavedPending
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨0,0,168⟩]
  physical : PhysicalInvariant (extendParameters θ fresh) final
  raw_valid : RawValid final

/-- Weave the actual A return and the actual learning prefix of B. The next
A token is consumed only after the common clock168 has genuinely been reached. -/
theorem first_interleaved_pair_exists {θ born fresh ε newborn forward backward}
    {c : ConstructedBirthPreparation θ born}
    {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
    (hb : @PhysicalBox 2 (extendParameters θ fresh) ε) (r : FirstWiredArrival b)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    Nonempty (FirstInterleavedPair r) := by
  obtain ⟨sender⟩ := r.first_sender_return_exists hb
  obtain ⟨receiver⟩ := first_receiver_weak_exists hb r hdelay
  have hstart : r.cut.state.time = r.receiverLocal.time := r.receipt.date.symm
  have hfinish : sender.final.time = receiver.cut168.state.time := sender.date.trans receiver.cut168.date.symm
  have hQ : ∀ d ∈ constructedBBirthQueue, sender.final.time ≤ d.due := by
    rw [sender.date]
    exact ConstructedBBirth.queue_future
  obtain ⟨woven,hem,hdel⟩ := sender.execution.product_neutral receiver.cut168.cut hstart hfinish
    sender.emissions sender.deliveries receiver.cut_emissions receiver.cut_deliveries
    constructedBBirthQueue hQ (reciprocalEntryRouter forward backward)
  let span := woven.cast_source r.receiver_product_initial.symm
  have hspan_em : span.ledger.emissions = [] := by
    rw [Execution.cast_source_ledger]
    exact hem
  have hspan_del : span.deliveries = [] := by
    rw [Execution.cast_source_deliveries]
    exact hdel
  let before := sender.final.product receiver.cut168.state constructedBBirthQueue
  have hqueue : before.pending = [] ++ (⟨0,0,168⟩ : Delivery 2) :: firstInterleavedPending := by
    change constructedBBirthQueue = _
    rw [constructedBBirthQueue,sourceTrain_succ]
    norm_num [firstInterleavedPending]
  have hfree : before.raw 0 0 = none := sender.raw_none 0 0
  have htime : (168 : ℝ) = before.time := sender.date.symm
  let final : Snapshot 2 := { (setRaw before 0 0 (some before.time)) with pending := [] ++ firstInterleavedPending }
  let arrival : Jump (reciprocalEntryRouter forward backward) before final :=
    .arrive before ⟨0,0,168⟩ [] firstInterleavedPending hqueue htime hfree
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨0,0,168⟩] := rfl
  let trace := span.append (.cons (.jump arrival) (.nil _))
  refine ⟨{
    sender := sender
    receiver := receiver
    final := final
    execution := trace
    date := sender.date
    a_prepared := ⟨(sender.prepared 0).ready,(sender.prepared 0).charge,
      (sender.prepared 0).recovery,(sender.prepared 0).auxiliary⟩
    a_charge := sender.charge
    a_gains := sender.gains_initial
    a_recovery := sender.recovery_initial
    b_values := rfl
    b_main := rfl
    b_aux := fun _ => rfl
    b_raw := ?_
    raw_active := ?_
    raw_other_a := ?_
    pending := rfl
    emissions := ?_
    deliveries := ?_
    physical := trace.physical_invariant hb r.receipt.physical
    raw_valid := trace.raw_valid r.receipt.raw_valid
  }⟩
  · intro p
    have h : before.raw 1 p = receiver.cut168.state.raw 0 p := rfl
    simpa [final,setRaw,Function.update_apply] using h
  · simp [final,setRaw,before,Snapshot.product,sender.date]
  · intro p hp
    have h : before.raw 0 p = none := sender.raw_none 0 p
    simpa [final,setRaw,Function.update_apply,hp] using h
  · simp only [trace,Execution.emissions_append,hspan_em,Execution.ledger,Move.ledger,
      Ledger.add,Ledger.zero,haEm,List.append_nil]
  · simp only [trace,Execution.deliveries_append,hspan_del,Execution.deliveries,
      Move.deliveries,haDel,List.nil_append,List.append_nil]

namespace FirstInterleavedPair
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} (s : FirstInterleavedPair r)

noncomputable def staged : StagedExecution θ fresh (fun _ _ => [])
    (reciprocalEntryRouter forward backward) born s.final :=
  { r.staged with after := r.staged.after.append s.execution }

theorem pending_length : s.final.pending.length = 46 := by
  rw [s.pending]
  simp [firstInterleavedPending,constructedBBirthSources,sourceTrain]

theorem b_main_ready : s.final.main 1 = .ready :=
  s.b_main.trans s.receiver.cut_main_ready

theorem b_recovery : s.final.x 1 .b = newborn.x .b := by
  rw [s.b_values,s.receiver.cut_recovery]
  change r.final.x 1 .b = newborn.x .b
  exact r.receiver_recovery

theorem b_gain_target {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    s.final.x 1 (.z 1) = newborn.x (.z 1) + 3 / 5 := by
  rw [s.b_values,s.receiver.cut_gain_target hb hdelay]
  change r.final.x 1 (.z 1) + 3 / 5 = newborn.x (.z 1) + 3 / 5
  rw [r.receiver_gain]

theorem b_error_dose {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    s.execution.ledger.error 1 1 = 3 / 5 := by
  have h := s.execution.gain_balance 1 1
  rw [s.b_gain_target hb hdelay,r.receiver_gain] at h
  linarith

theorem b_mark_zero (p : Port) : s.execution.ledger.mark 1 p = 0 := by
  have hm := s.execution.ready_states_of_no_emissions 1 r.receipt.receiver_ready.ready
    (by simp [Execution.emissionTimes,s.emissions])
  exact s.execution.mark_zero_ready 1 p (s.execution.allStates_main_flows 1 .ready hm)

theorem b_aux_rest {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) (p : Port) :
    s.final.aux 1 p = .ready ∧ RestBand (s.final.x 1 (.m p)) := by
  have h := s.receiver.cut_aux_rest hb hdelay p
  rw [s.b_aux,s.b_values]
  exact h

theorem b_raw_none (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5)
    (p : Port) : s.final.raw 1 p = none := by
  rw [s.b_raw]
  by_cases hp : p = 1
  · subst p
    have hs := s.receiver.cut168.cut.raw_allowed_states 0 1 r.receiverLocal.time
      (Or.inr r.receiver_local_raw) (s.receiver.cut_no_arrival 1)
    rcases s.receiver.cut168.cut.allStates_final hs with hn | ha
    · exact hn
    · have hv := (s.receiver.cut_raw_valid 0 1 r.receiverLocal.time ha).2
      rw [s.receiver.cut168.date] at hv
      change (168 : ℝ) ≤ r.final.time + 1 at hv
      linarith [(r.date_bounds hdelay).2]
  · exact (s.receiver.cut168.cut.raw_absent_of_no_arrival 0 p
      (r.receiver_local_raw_other 0 p (Or.inr hp)) (s.receiver.cut_no_arrival p)).1

theorem complete : CompleteThrough s.execution 168 := by
  have hgB := s.receiver.cut168.before_guards
  have hguard : BeforeGuards s.final s.final.x := by
    constructor
    · intro j
      rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
      · rw [s.a_prepared.ready]
        linarith [s.a_charge]
      · rw [s.b_main,s.b_values]
        exact hgB.1 0
    · intro j p
      rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
      · rw [(s.a_prepared.auxiliary p).1]
        linarith [(s.a_prepared.auxiliary p).2.2]
      · rw [s.b_aux,s.b_values]
        exact hgB.2 0 p
  have hfuture : ∀ d ∈ s.final.pending, (168 : ℝ) < d.due := by
    intro d hd
    rw [s.pending] at hd
    simp only [firstInterleavedPending,constructedBBirthSources,List.mem_append] at hd
    rcases hd with hd | hd | hd <;> obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd <;>
      dsimp <;> nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  refine ⟨s.date,?_,hfuture⟩
  intro u
  apply hguard.no_jump
  · intro j p origin hraw
    rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
    · by_cases hp : p = 0
      · subst p
        have he : origin = (168 : ℝ) := Option.some.inj (hraw.symm.trans s.raw_active)
        rw [s.date,he]
        norm_num
      · rw [s.raw_other_a p hp] at hraw
        contradiction
    · rw [s.b_raw] at hraw
      rw [s.date]
      exact s.receiver.cut168.raw_strict 0 p origin hraw
  · intro d hd
    rw [s.date]
    exact hfuture d hd

theorem staged_complete : CompleteThrough s.staged.after 168 := s.complete

end FirstInterleavedPair

theorem birth_protocol_first_interleaved_pair_exists {θ born fresh ε}
    (hborn : @BirthState 1 born) (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newborn : Newborn) (forward backward : ℝ → ℝ)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) :
    ∃ c : ConstructedBirthPreparation θ born,
      ∃ b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources,
        ∃ r : FirstWiredArrival b, ∃ s : FirstInterleavedPair r,
          CompleteThrough s.staged.after 168 ∧ s.final.pending.length = 46 := by
  obtain ⟨c,b,r,_,_⟩ := birth_protocol_first_wired_arrival_exists hborn hb ha hqueue newborn forward backward hdelay
  obtain ⟨s⟩ := first_interleaved_pair_exists hb r hdelay
  exact ⟨c,b,r,s,s.staged_complete,s.pending_length⟩

end KernelR.Hybrid
