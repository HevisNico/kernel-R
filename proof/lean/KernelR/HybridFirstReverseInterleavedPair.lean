import KernelR.HybridFirstReverseWiredArrival
import KernelR.HybridFeedbackSenderReturn
import KernelR.HybridWeakInputCycleExistence

/-! A's first real weak return-wire response runs alongside B's retained
return. The next external B source is consumed at352 without resetting A. -/
namespace KernelR.Hybrid

noncomputable def firstReverseInterleavedPending : List (Delivery 2) :=
  sourceTrain 1 2 360 8 11 ++ sourceTrain 1 2 480 8 16

namespace FirstReverseWiredArrival
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
  {f : FeedbackFirstFire w} (r : FirstReverseWiredArrival f)

noncomputable def receiverLocal : Snapshot 1 := r.final.cellProjection 0 []

theorem receiver_local_physical : PhysicalInvariant f.parametersA r.receiverLocal :=
  ⟨fun _ => r.physical.region 0,fun _ p => r.physical.gain_cap 0 p,
    fun _ => r.physical.recovery_cap 0,fun _ => r.physical.reserve 0⟩

theorem receiver_local_raw_valid : RawValid r.receiverLocal :=
  fun _ p origin h => r.raw_valid 0 p origin h

theorem receiver_local_prepared (j : Fin 1) : PreparedSection r.receiverLocal j :=
  ⟨r.a_prepared.ready,r.a_prepared.charge,r.a_prepared.recovery,r.a_prepared.auxiliary⟩

theorem receiver_local_charge (j : Fin 1) : r.receiverLocal.x j .q = 1 / 10 := r.a_charge

theorem receiver_local_raw : r.receiverLocal.raw 0 2 = some r.receiverLocal.time := r.raw_active

theorem receiver_local_other (j : Fin 1) (p : Port) (h : j ≠ 0 ∨ p ≠ 2) :
    r.receiverLocal.raw j p = none := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact r.raw_other_a p (by simpa using h)

theorem receiver_product_initial :
    r.receiverLocal.product r.cutH.state w.final.pending = r.final := by
  have extensionality {n} (s u : Snapshot n) (ht : s.time = u.time) (hx : s.x = u.x)
      (hm : s.main = u.main) (ha : s.aux = u.aux) (hr : s.raw = u.raw) (hp : s.pending = u.pending) : s = u := by
    cases s
    cases u
    simp_all only
  apply extensionality
  · rfl
  · funext i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · rfl
    · exact r.b_values.symm
  · funext i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · rfl
    · exact r.b_main.symm
  · funext i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · rfl
    · funext p; exact (r.b_aux p).symm
  · funext i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · rfl
    · funext p; exact (r.b_raw p).symm
  · exact r.pending.symm

end FirstReverseWiredArrival

structure FirstReverseReceiverWeak {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} (r : FirstReverseWiredArrival f) where
  weak : WeakInputCycle f.parametersA (fun _ _ => []) r.receiverLocal 0 2
  cut352 : weak.execution.BeforeFlowCut 352
  cut_emissions : cut352.cut.ledger.emissions = []
  cut_deliveries : cut352.cut.deliveries = []
  cut_physical : PhysicalInvariant f.parametersA cut352.state
  cut_raw_valid : RawValid cut352.state

/-- The local weak trace is constructed beyond352 and cut there with its
actual remaining path intact. The global B source is never put in its queue. -/
theorem first_reverse_receiver_weak_exists {θ ε forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} (r : FirstReverseWiredArrival f) (hb : PhysicalBox θ ε)
    (hz : r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000) :
    Nonempty (FirstReverseReceiverWeak r) := by
  have hlog : r.receiverLocal.x 0 (.z 2) ≤ Real.log (6 / 5) + 1 / 1000 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3 / 10) (by norm_num : (3 / 10 : ℝ) ≤ 6 / 5)
    change r.final.x 0 (.z 2) ≤ _
    linarith
  have hg : Real.exp (r.receiverLocal.x 0 (.z 2)) ≤ 7 / 6 :=
    low_gain_tail_upper (by change r.final.x 0 (.z 2) ≤ _; linarith)
  obtain ⟨weak⟩ := weak_input_cycle_exists (route := fun _ _ => []) r.receiverLocal (f.localA_box hb)
    r.receiver_local_physical r.receiver_local_raw_valid 0 2
    (fun j => (r.receiver_local_prepared j).ready_coordinates) hg hlog r.receiver_local_raw
    r.receiver_local_other (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  obtain ⟨cut⟩ := weak.execution.before_flow_cut_exists 352
    (by change r.final.time ≤ (352 : ℝ); linarith [r.window.2])
    (by rw [weak.date]; change (352 : ℝ) < r.final.time + 15 / 2; linarith [r.window.1])
  have he := (List.append_eq_nil_iff.mp (cut.emissions.symm.trans weak.emissions)).1
  have hd := (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans weak.deliveries)).1
  exact ⟨⟨weak,cut,he,hd,cut.cut.physical_invariant (f.localA_box hb) r.receiver_local_physical,
    cut.cut.raw_valid r.receiver_local_raw_valid⟩⟩

namespace FirstReverseReceiverWeak
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
  {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f} (a : FirstReverseReceiverWeak r)

noncomputable def continuation : Execution f.parametersA (fun _ _ => []) a.cut352.state a.weak.final :=
  .cons (.flow a.cut352.flow) a.cut352.rest

theorem continuation_emissions : a.continuation.ledger.emissions = [] := by
  have h := (List.append_eq_nil_iff.mp (a.cut352.emissions.symm.trans a.weak.emissions)).2
  exact h

theorem continuation_deliveries : a.continuation.deliveries = [] := by
  have h := (List.append_eq_nil_iff.mp (a.cut352.deliveries.symm.trans a.weak.deliveries)).2
  exact h

theorem cut_main_states : a.cut352.cut.AllStates (fun s => s.main 0 = .ready) :=
  a.cut352.cut.ready_states_of_no_emissions 0 (r.receiver_local_prepared 0).ready
    (by simp [Execution.emissionTimes,a.cut_emissions])

theorem cut_main_ready : a.cut352.state.main 0 = .ready := a.cut352.cut.allStates_final a.cut_main_states

theorem cut_no_arrival (p : Port) : NoArrivalAt a.cut352.cut 0 p := by simp [NoArrivalAt,a.cut_deliveries]

theorem cut_recovery : a.cut352.state.x 0 .b = r.receiverLocal.x 0 .b :=
  a.cut352.cut.recovery_constant_ready 0 (a.cut352.cut.allStates_main_flows 0 .ready a.cut_main_states)

theorem cut_charge_lower : 1 / 10 ≤ a.cut352.state.x 0 .q := by
  exact a.cut352.cut.ready_charge_ge_rest 0
    (a.cut352.cut.allStates_main_flows 0 .ready a.cut_main_states) (r.receiver_local_charge 0).ge

theorem cut_sensor_cycle {ε} (hb : PhysicalBox θ ε) : Nonempty (SensorCycle a.cut352.cut 0 2) := by
  apply a.cut352.cut.sensor_cycle (f.localA_box hb) r.receiver_local_physical.region 0 2
    ((r.receiver_local_prepared 0).auxiliary 2).1 r.receiver_local_raw
    ((r.receiver_local_prepared 0).auxiliary 2).2
  rw [a.cut352.date]
  change r.final.time + 419 / 300 ≤ (352 : ℝ)
  linarith [r.window.2]

theorem cut_error_and_gain {ε} (hb : PhysicalBox θ ε)
    (hz : r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000) :
    a.cut352.cut.ledger.error 0 2 = 3 / 5 ∧
      a.cut352.state.x 0 (.z 2) = r.receiverLocal.x 0 (.z 2) + 3 / 5 := by
  obtain ⟨cycle⟩ := a.cut_sensor_cycle hb
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3 / 10) (by norm_num : (3 / 10 : ℝ) ≤ 6 / 5)
  have hh : r.receiverLocal.x 0 (.z 2) + 3 / 5 < Real.log ((f.parametersA 0).cap 2) := by
    have h := (f.localA_box hb).fast_nominal_headroom 0 2
    change r.final.x 0 (.z 2) + 3 / 5 < _
    linarith
  exact cycle.total_error_of_invariant (f.localA_box hb) r.receiver_local_physical
    r.receiver_local_raw_valid a.cut_main_states hh r.receiver_local_raw (a.cut_no_arrival 2)

theorem cut_aux_rest {ε} (hb : PhysicalBox θ ε) (p : Port) :
    a.cut352.state.aux 0 p = .ready ∧ RestBand (a.cut352.state.x 0 (.m p)) := by
  by_cases hp : p = 2
  · subst p
    obtain ⟨cycle⟩ := a.cut_sensor_cycle hb
    obtain ⟨hm,hq⟩ := cycle.final_rest r.receiver_local_raw_valid r.receiver_local_raw (a.cut_no_arrival 2)
    exact ⟨hm,by rw [hq]; norm_num [RestBand]⟩
  · exact (a.cut352.cut.aux_no_input_rest_band 0 p ((r.receiver_local_prepared 0).auxiliary p).1
      ((r.receiver_local_prepared 0).auxiliary p).2 (r.receiver_local_other 0 p (Or.inr hp))
      (a.cut_no_arrival p)).1

theorem cut_raw_none (p : Port) : a.cut352.state.raw 0 p = none := by
  by_cases hp : p = 2
  · subst p
    have h := a.cut352.cut.raw_allowed_states 0 2 r.receiverLocal.time
      (Or.inr r.receiver_local_raw) (a.cut_no_arrival 2)
    rcases a.cut352.cut.allStates_final h with hn | ha
    · exact hn
    · have htime := a.cut352.raw_strict 0 2 r.receiverLocal.time ha
      change (352 : ℝ) < r.final.time + 1 at htime
      linarith [r.window.2]
  · exact (a.cut352.cut.raw_absent_of_no_arrival 0 p
      (r.receiver_local_other 0 p (Or.inr hp)) (a.cut_no_arrival p)).1

end FirstReverseReceiverWeak

structure FirstReverseInterleavedPair {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} (r : FirstReverseWiredArrival f) where
  sender : FeedbackSenderReturn f r.fast
  receiver : FirstReverseReceiverWeak r
  final : Snapshot 2
  execution : Execution θ (reciprocalEntryRouter forward backward) r.final final
  date : final.time = 352
  b_prepared : PreparedSection final 1
  b_charge : final.x 1 .q = 1 / 10
  b_gains : ∀ p, final.x 1 (.z p) = w.final.x 1 (.z p)
  b_recovery : final.x 1 .b = start.x 1 .b
  a_values : final.x 0 = receiver.cut352.state.x 0
  a_main : final.main 0 = receiver.cut352.state.main 0
  a_aux : ∀ p, final.aux 0 p = receiver.cut352.state.aux 0 p
  a_raw : ∀ p, final.raw 0 p = receiver.cut352.state.raw 0 p
  raw_active : final.raw 1 2 = some (352 : ℝ)
  raw_other_b : ∀ p, p ≠ 2 → final.raw 1 p = none
  pending : final.pending = firstReverseInterleavedPending
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨1,2,352⟩]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

/-- The retained sender suffix and receiver prefix meet at352 before the
actual next external occurrence is consumed. No A coordinate is reset. -/
theorem first_reverse_interleaved_pair_exists {θ ε forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} (r : FirstReverseWiredArrival f) (hb : PhysicalBox θ ε)
    (hz : r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000) :
    Nonempty (FirstReverseInterleavedPair r) := by
  obtain ⟨sender⟩ := f.sender_return_exists hb r.fast
  obtain ⟨receiver⟩ := first_reverse_receiver_weak_exists r hb hz
  let tailB : Execution f.parametersB (fun _ _ => []) r.cutH.state r.fast.final :=
    .cons (.flow r.cutH.flow) r.cutH.rest
  have heTail : tailB.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (r.cutH.emissions.symm.trans r.fast.emissions)).2
  have hdTail : tailB.deliveries = [] :=
    (List.append_eq_nil_iff.mp (r.cutH.deliveries.symm.trans r.fast.deliveries)).2
  let senderTrace := tailB.append sender.execution
  have heB : senderTrace.ledger.emissions = [] := by
    rw [Execution.emissions_append,heTail,sender.emissions]
    rfl
  have hdB : senderTrace.deliveries = [] := by
    rw [Execution.deliveries_append,hdTail,sender.deliveries]
    rfl
  have hstart : r.receiverLocal.time = r.cutH.state.time := r.date.trans r.cutH.date.symm
  have hfinish : receiver.cut352.state.time = sender.final.time := receiver.cut352.date.trans sender.date.symm
  have hQ : ∀ d ∈ w.final.pending, receiver.cut352.state.time ≤ d.due := by
    intro d hd
    rw [receiver.cut352.date,w.pending] at *
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨woven,hem,hdel⟩ := receiver.cut352.cut.product_neutral senderTrace hstart hfinish
    receiver.cut_emissions receiver.cut_deliveries heB hdB w.final.pending hQ
    (reciprocalEntryRouter forward backward)
  let translated := woven.cast_parameters f.parameters_product
  let span := translated.cast_source r.receiver_product_initial.symm
  have hspanEm : span.ledger.emissions = [] := by
    rw [Execution.cast_source_ledger,Execution.cast_parameters_ledger]
    exact hem
  have hspanDel : span.deliveries = [] := by
    rw [Execution.cast_source_deliveries,Execution.cast_parameters_deliveries]
    exact hdel
  let before := receiver.cut352.state.product sender.final w.final.pending
  have hqueue : before.pending = [] ++ (⟨1,2,352⟩ : Delivery 2) :: firstReverseInterleavedPending := by
    change w.final.pending = _
    rw [w.pending,sourceTrain_succ]
    norm_num [firstReverseInterleavedPending]
  have hfree : before.raw 1 2 = none := sender.raw_none 0 2
  have htime : (352 : ℝ) = before.time := receiver.cut352.date.symm
  let final : Snapshot 2 := {(setRaw before 1 2 (some before.time)) with pending := [] ++ firstReverseInterleavedPending}
  let arrival : Jump (reciprocalEntryRouter forward backward) before final :=
    .arrive before ⟨1,2,352⟩ [] firstReverseInterleavedPending hqueue htime hfree
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨1,2,352⟩] := rfl
  let trace := span.append (.cons (.jump arrival) (.nil _))
  refine ⟨{
    sender := sender, receiver := receiver, final := final, execution := trace
    date := receiver.cut352.date
    b_prepared := ⟨(sender.prepared 0).ready,(sender.prepared 0).charge,
      (sender.prepared 0).recovery,(sender.prepared 0).auxiliary⟩
    b_charge := sender.charge, b_gains := sender.gains_weak 0, b_recovery := sender.recovery_own 0
    a_values := rfl, a_main := rfl, a_aux := fun _ => rfl, a_raw := ?_
    raw_active := ?_, raw_other_b := ?_, pending := rfl, emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb r.physical
    raw_valid := trace.raw_valid r.raw_valid
  }⟩
  · intro p
    have h : before.raw 0 p = receiver.cut352.state.raw 0 p := rfl
    simpa [final,setRaw,Function.update_apply] using h
  · simp [final,setRaw,before,Snapshot.product,receiver.cut352.date]
  · intro p hp
    have h : before.raw 1 p = none := sender.raw_none 0 p
    simpa [final,setRaw,Function.update_apply,hp] using h
  · simp only [trace,Execution.emissions_append,hspanEm,Execution.ledger,Move.ledger,haEm,
      Ledger.add,Ledger.zero,List.append_nil]
  · simp only [trace,Execution.deliveries_append,hspanDel,Execution.deliveries,Move.deliveries,haDel,
      List.nil_append,List.append_nil]

namespace FirstReverseInterleavedPair
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
  {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f} (p : FirstReverseInterleavedPair r)

theorem pending_length : p.final.pending.length = 27 := by
  rw [p.pending]
  simp [firstReverseInterleavedPending,sourceTrain]

theorem a_main_ready : p.final.main 0 = .ready := p.a_main.trans p.receiver.cut_main_ready

theorem a_charge_lower : 1 / 10 ≤ p.final.x 0 .q := by rw [p.a_values]; exact p.receiver.cut_charge_lower

theorem a_recovery : p.final.x 0 .b = r.final.x 0 .b := by
  rw [p.a_values,p.receiver.cut_recovery]
  rfl

theorem a_gain_target {ε} (hb : PhysicalBox θ ε)
    (hz : r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000) :
    p.final.x 0 (.z 2) = r.final.x 0 (.z 2) + 3 / 5 := by
  rw [p.a_values,(p.receiver.cut_error_and_gain hb hz).2]
  rfl

theorem a_error_dose {ε} (hb : PhysicalBox θ ε)
    (hz : r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000) :
    p.execution.ledger.error 0 2 = 3 / 5 := by
  have h := p.execution.gain_balance 0 2
  rw [p.a_gain_target hb hz] at h
  linarith

theorem a_aux_rest {ε} (hb : PhysicalBox θ ε) (q : Port) :
    p.final.aux 0 q = .ready ∧ RestBand (p.final.x 0 (.m q)) := by
  rw [p.a_aux,p.a_values]
  exact p.receiver.cut_aux_rest hb q

theorem a_raw_none (q : Port) : p.final.raw 0 q = none := by
  rw [p.a_raw]
  exact p.receiver.cut_raw_none q

theorem complete : CompleteThrough p.execution 352 := by
  have hfuture : ∀ d ∈ p.final.pending, (352 : ℝ) < d.due := by
    intro d hd
    rw [p.pending] at hd
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  refine ⟨p.date,?_,hfuture⟩
  intro u
  apply BeforeGuards.no_jump
  · constructor
    · intro i
      rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
      · rw [p.a_main,p.a_values]
        exact p.receiver.cut352.before_guards.1 0
      · rw [p.b_prepared.ready,p.b_charge]
        norm_num
    · intro i q
      rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
      · rw [p.a_aux,p.a_values]
        exact p.receiver.cut352.before_guards.2 0 q
      · rw [(p.b_prepared.auxiliary q).1]
        linarith [(p.b_prepared.auxiliary q).2.2]
  · intro i q origin hr
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · rw [p.a_raw] at hr
      have h := p.receiver.cut352.raw_strict 0 q origin hr
      rw [p.date]
      exact h
    · by_cases hq : q = 2
      · subst q
        have ho : origin = 352 := Option.some.inj (hr.symm.trans p.raw_active)
        rw [ho,p.date]
        norm_num
      · rw [p.raw_other_b q hq] at hr
        contradiction
  · intro d hd
    rw [p.date]
    exact hfuture d hd

end FirstReverseInterleavedPair
end KernelR.Hybrid
