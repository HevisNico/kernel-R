import KernelR.HybridPortSourceWire
import KernelR.HybridReadyWeakCut

/-! A true right-cell weak response is woven with its left sender's retained
return before the next queued left source is consumed. Ports and routing
are arbitrary; the receiving recovery may still be a newborn's own value. -/
namespace KernelR.Hybrid

namespace PortSourceWire
variable {θS θR route source pS cycle pR delay}
  (r : @PortSourceWire θS θR route source pS cycle pR delay)

noncomputable def receiverLocal : Snapshot 1 := r.final.cellProjection 1 []

theorem receiver_local_physical : PhysicalInvariant θR r.receiverLocal := by
  refine ⟨fun _ => r.physical.region 1,?_,fun _ => r.physical.recovery_cap 1,
    fun _ => r.physical.reserve 1⟩
  intro j q
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact r.physical.gain_cap 1 q

theorem receiver_local_raw_valid : RawValid r.receiverLocal :=
  fun _ q origin h => r.raw_valid 1 q origin h

theorem product_receiver_projection :
    r.cutH.state.product r.receiverLocal source.pending = r.final := by
  have extensionality {n} (s u : Snapshot n) (ht : s.time = u.time) (hx : s.x = u.x)
      (hm : s.main = u.main) (ha : s.aux = u.aux) (hr : s.raw = u.raw) (hp : s.pending = u.pending) : s = u := by
    cases s
    cases u
    simp_all only
  apply extensionality
  · exact r.cutH.date.trans r.date.symm
  · funext i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact r.sender_values.symm
    · rfl
  · funext i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact r.sender_main.symm
    · rfl
  · funext i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · funext q; exact (r.sender_aux q).symm
    · rfl
  · funext i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · funext q; exact (r.sender_raw q).symm
    · rfl
  · exact r.pending.symm

end PortSourceWire

structure PortWeakStep {θS θR route source pS cycle pR delay}
    (r : @PortSourceWire θS θR route source pS cycle pR delay) (later : List (Delivery 2)) where
  receiver : ReadyWeakCut θR r.receiverLocal pR (source.time + 8)
  senderFinal : Snapshot 1
  senderExecution : Execution θS (fun _ _ => []) r.cutH.state senderFinal
  sender_date : senderFinal.time = source.time + 8
  sender_pending : senderFinal.pending = []
  sender_emissions : senderExecution.ledger.emissions = []
  sender_deliveries : senderExecution.deliveries = []
  final : Snapshot 2
  execution : Execution (extendParameters θS (θR 0)) route r.final final
  date : final.time = source.time + 8
  sender_prepared : PreparedSection final 0
  sender_charge : final.x 0 .q = 1 / 10
  sender_gains : ∀ q, final.x 0 (.z q) = r.final.x 0 (.z q)
  receiver_values : final.x 1 = receiver.cut.state.x 0
  receiver_main : final.main 1 = receiver.cut.state.main 0
  receiver_aux : ∀ q, final.aux 1 q = receiver.cut.state.aux 0 q
  receiver_raw : ∀ q, final.raw 1 q = receiver.cut.state.raw 0 q
  raw_active : final.raw 0 pS = some (source.time + 8)
  raw_other_sender : ∀ q, q ≠ pS → final.raw 0 q = none
  pending : final.pending = later
  receiver_gain_target : final.x 1 (.z pR) = r.final.x 1 (.z pR) + 3 / 5
  receiver_gain_other : ∀ q, q ≠ pR → final.x 1 (.z q) = r.final.x 1 (.z q)
  recovery : ∀ i, final.x i .b = r.final.x i .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨0,pS,source.time + 8⟩]
  physical : PhysicalInvariant (extendParameters θS (θR 0)) final
  raw_valid : RawValid final
  complete : CompleteThrough execution (source.time + 8)

/-- The actual received weak pulse learns on its own port, while the sender
resumes the original FAST path and its already constructed SLOW return.
No prepared recovery bound or charge reset is imposed on the receiver. -/
theorem port_weak_step_exists {θS θR ε route source pS cycle pR delay}
    (r : @PortSourceWire θS θR route source pS cycle pR delay)
    (hb : PhysicalBox (extendParameters θS (θR 0)) ε)
    (hs : ReadyCoordinates r.final 1)
    (hnarrow : r.final.x 1 .q ≤ 10001 / 100000)
    (hg : Real.exp (r.final.x 1 (.z pR)) ≤ 4 / 3)
    (hz : r.final.x 1 (.z pR) ≤ Real.log (6 / 5) + 1 / 1000)
    (later : List (Delivery 2))
    (hqueue : source.pending = ⟨0,pS,source.time + 8⟩ :: later)
    (hlater : ∀ d ∈ later, source.time + 8 < d.due) :
    Nonempty (PortWeakStep r later) := by
  have hbR : PhysicalBox θR ε := by
    refine ⟨hb.1,?_⟩
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hb.2 1 q
  have hR : ReadyCoordinates r.receiverLocal 0 := ⟨hs.ready,hs.charge,hs.auxiliary⟩
  obtain ⟨receiver⟩ := ready_weak_cut_exists hbR r.receiverLocal pR
    r.receiver_local_physical r.receiver_local_raw_valid hR hnarrow hg hz r.raw_active r.raw_other rfl
    (source.time + 8)
    (by change r.final.time + 419 / 300 ≤ source.time + 8; linarith [r.window.2])
    (by change source.time + 8 < r.final.time + 15 / 2; linarith [r.window.1])
  have hpendingS : cycle.returned.final.pending = [] := cycle.pending
  have hwait : cycle.returned.final.time < source.time + 8 := by
    rw [cycle.date]
    norm_num [portSourceSender,Snapshot.cellProjection]
  let waitFlow : Flow θS cycle.returned.final (quietAt cycle.returned.final (source.time + 8)) :=
    quietFlow cycle.returned.final hwait (fun j => (cycle.ready j).ready)
      (fun j q => ((cycle.ready j).auxiliary q).1) cycle.raw_none
      (fun j => by linarith [(cycle.ready j).charge.2])
      (fun j q => by linarith [((cycle.ready j).auxiliary q).2.2])
      (by intro d hd; rw [hpendingS] at hd; contradiction)
  let wait : Execution θS (fun _ _ => []) cycle.returned.final
      (quietAt cycle.returned.final (source.time + 8)) := .cons (.flow waitFlow) (.nil _)
  let senderFinal := quietAt cycle.returned.final (source.time + 8)
  let fastTail : Execution θS (fun _ _ => []) r.cutH.state cycle.fast.final :=
    .cons (.flow r.cutH.flow) r.cutH.rest
  let senderExecution := fastTail.append (cycle.returned.execution.append wait)
  have heFast : fastTail.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (r.cutH.emissions.symm.trans cycle.fast.emissions)).2
  have hdFast : fastTail.deliveries = [] :=
    (List.append_eq_nil_iff.mp (r.cutH.deliveries.symm.trans cycle.fast.deliveries)).2
  have heS : senderExecution.ledger.emissions = [] := by
    change (fastTail.append (cycle.returned.execution.append wait)).ledger.emissions = []
    rw [Execution.emissions_append fastTail (cycle.returned.execution.append wait),heFast,
      Execution.emissions_append cycle.returned.execution wait,cycle.returned.emissions]
    rfl
  have hdS : senderExecution.deliveries = [] := by
    change (fastTail.append (cycle.returned.execution.append wait)).deliveries = []
    rw [Execution.deliveries_append fastTail (cycle.returned.execution.append wait),hdFast,
      Execution.deliveries_append cycle.returned.execution wait,cycle.returned.deliveries]
    rfl
  have hSready : ∀ j, ReadyCoordinates senderFinal j :=
    fun j => quietAt_ready_coordinates cycle.returned.final j (cycle.ready j) hwait.le
  have hSprepared : PreparedSection senderFinal 0 :=
    ⟨(hSready 0).ready,(hSready 0).charge,(cycle.prepared 0).recovery,(hSready 0).auxiliary⟩
  have hScharge : senderFinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (cycle.returned.final.x 0 .q) cycle.returned.final.time (source.time + 8) = _
    rw [cycle.charge]
    simp [relax]
  have hSgain : ∀ q, senderFinal.x 0 (.z q) = r.final.x 0 (.z q) := by
    intro q
    change cycle.returned.final.x 0 (.z q) = _
    rw [cycle.gains,r.gains]
    rfl
  have hSrec : senderFinal.x 0 .b = r.final.x 0 .b := by
    change cycle.returned.final.x 0 .b = _
    rw [cycle.recovery,r.recovery]
    rfl
  have hstart : r.cutH.state.time = r.receiverLocal.time := r.cutH.date.trans r.date.symm
  have hfinish : senderFinal.time = receiver.cut.state.time := receiver.cut.date.symm
  have hQ : ∀ d ∈ source.pending, senderFinal.time ≤ d.due := by
    intro d hd
    rw [hqueue] at hd
    change source.time + 8 ≤ d.due
    rcases List.mem_cons.mp hd with rfl | hd
    · exact le_rfl
    · exact (hlater d hd).le
  obtain ⟨woven,heW,hdW⟩ := senderExecution.product_neutral receiver.cut.cut hstart hfinish
    heS hdS receiver.cut_emissions receiver.cut_deliveries source.pending hQ route
  let span := woven.cast_source r.product_receiver_projection.symm
  have heSpan : span.ledger.emissions = [] := by rw [Execution.cast_source_ledger]; exact heW
  have hdSpan : span.deliveries = [] := by rw [Execution.cast_source_deliveries]; exact hdW
  let before := senderFinal.product receiver.cut.state source.pending
  let final : Snapshot 2 := {(setRaw before 0 pS (some before.time)) with pending := [] ++ later}
  have hqueueBefore : before.pending = [] ++ (⟨0,pS,source.time + 8⟩ : Delivery 2) :: later := hqueue
  have hfree : before.raw 0 pS = none := cycle.raw_none 0 pS
  let arrival : Jump route before final := .arrive before ⟨0,pS,source.time + 8⟩ [] later hqueueBefore rfl hfree
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨0,pS,source.time + 8⟩] := rfl
  let trace := span.append (.cons (.jump arrival) (.nil _))
  have hrawS : final.raw 0 pS = some (source.time + 8) := by
    simp [final,setRaw,before,Snapshot.product,senderFinal,quietAt]
  have hrawOther : ∀ q, q ≠ pS → final.raw 0 q = none := by
    intro q hq
    have h : before.raw 0 q = none := cycle.raw_none 0 q
    simpa [final,setRaw,Function.update_apply,hq] using h
  have hrawR : ∀ q, final.raw 1 q = receiver.cut.state.raw 0 q := by
    intro q
    have h : before.raw 1 q = receiver.cut.state.raw 0 q := rfl
    simpa [final,setRaw,Function.update_apply] using h
  have hfuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    change d ∈ [] ++ later at hd
    simp only [List.nil_append] at hd
    exact hlater d hd
  have hcomplete : CompleteThrough trace (source.time + 8) := by
    refine ⟨rfl,?_,hfuture⟩
    intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro i
        rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
        · have hm : final.main 0 = .ready := hSprepared.ready
          have hx : final.x 0 .q = 1 / 10 := hScharge
          rw [hm,hx]; norm_num
        · have hm : final.main 1 = receiver.cut.state.main 0 := rfl
          have hx : final.x 1 = receiver.cut.state.x 0 := rfl
          rw [hm,hx]; exact receiver.cut.before_guards.1 0
      · intro i q
        rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
        · have hm : final.aux 0 q = .ready := (hSprepared.auxiliary q).1
          have hx : RestBand (final.x 0 (.m q)) := (hSprepared.auxiliary q).2
          rw [hm]; linarith [hx.2]
        · have hm : final.aux 1 q = receiver.cut.state.aux 0 q := rfl
          have hx : final.x 1 = receiver.cut.state.x 0 := rfl
          rw [hm,hx]; exact receiver.cut.before_guards.2 0 q
    · intro i q origin hr
      rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
      · by_cases hq : q = pS
        · subst q
          have ho : origin = source.time + 8 := Option.some.inj (hr.symm.trans hrawS)
          rw [ho]; change source.time + 8 < source.time + 8 + 1; linarith
        · rw [hrawOther q hq] at hr; contradiction
      · rw [hrawR] at hr
        have h := receiver.cut.raw_strict 0 q origin hr
        change source.time + 8 < origin + 1
        exact h
    · exact hfuture
  refine ⟨{
    receiver := receiver, senderFinal := senderFinal, senderExecution := senderExecution
    sender_date := rfl, sender_pending := hpendingS, sender_emissions := heS, sender_deliveries := hdS
    final := final, execution := trace, date := rfl
    sender_prepared := ⟨hSprepared.ready,hSprepared.charge,hSprepared.recovery,hSprepared.auxiliary⟩
    sender_charge := hScharge, sender_gains := hSgain
    receiver_values := rfl, receiver_main := rfl, receiver_aux := fun _ => rfl, receiver_raw := hrawR
    raw_active := hrawS, raw_other_sender := hrawOther, pending := rfl
    receiver_gain_target := receiver.cut_gain_target, receiver_gain_other := receiver.cut_gain_other
    recovery := ?_, emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb r.physical
    raw_valid := trace.raw_valid r.raw_valid, complete := hcomplete
  }⟩
  · intro i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact hSrec
    · exact receiver.cut_recovery
  · simp only [trace,Execution.emissions_append,heSpan,Execution.ledger,Move.ledger,haEm,
      Ledger.add,Ledger.zero,List.append_nil]
  · simp only [trace,Execution.deliveries_append,hdSpan,Execution.deliveries,Move.deliveries,haDel,
      List.nil_append,List.append_nil]

namespace PortWeakStep
variable {θS θR route source pS cycle pR delay}
  {r : @PortSourceWire θS θR route source pS cycle pR delay} {later} (s : PortWeakStep r later)

/-- The next global source retains the whole actual receiving cut. -/
theorem receiver_local : portSourceReceiver s.final = s.receiver.cut.state := by
  have extensionality {n} (v u : Snapshot n) (ht : v.time = u.time) (hx : v.x = u.x)
      (hm : v.main = u.main) (ha : v.aux = u.aux) (hr : v.raw = u.raw) (hp : v.pending = u.pending) : v = u := by
    cases v
    cases u
    simp_all only
  apply extensionality
  · exact s.date.trans s.receiver.cut.date.symm
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.receiver_values
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.receiver_main
  · funext j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.receiver_aux q
  · funext j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.receiver_raw q
  · exact s.receiver.cut_pending.symm

theorem sender_local_time : (portSourceSender s.final).time = source.time + 8 := s.date

theorem sender_local_prepared : PreparedSection (portSourceSender s.final) 0 :=
  ⟨s.sender_prepared.ready,s.sender_prepared.charge,s.sender_prepared.recovery,s.sender_prepared.auxiliary⟩

theorem sender_local_charge : (portSourceSender s.final).x 0 .q = 1 / 10 := s.sender_charge

theorem sender_local_raw_active : (portSourceSender s.final).raw 0 pS =
    some (portSourceSender s.final).time := by rw [s.sender_local_time]; exact s.raw_active

theorem receiver_main_ready : s.final.main 1 = .ready := s.receiver_main.trans s.receiver.cut_main_ready

theorem receiver_charge_lower : 1 / 10 - 1 / 100000 ≤ s.final.x 1 .q := by
  rw [s.receiver_values]
  exact s.receiver.cut_charge_lower

theorem receiver_aux_rest (q : Port) : s.final.aux 1 q = .ready ∧ RestBand (s.final.x 1 (.m q)) := by
  rw [s.receiver_aux,s.receiver_values]
  exact s.receiver.cut_aux_rest q

theorem receiver_raw_none (q : Port) : s.final.raw 1 q = none := by
  rw [s.receiver_raw]
  exact s.receiver.cut_raw_none q

theorem raw_other (i : Fin 2) (q : Port) (h : i ≠ 0 ∨ q ≠ pS) : s.final.raw i q = none := by
  rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
  · exact s.raw_other_sender q (by simpa using h)
  · exact s.receiver_raw_none q

theorem receiver_error_dose : s.execution.ledger.error 1 pR = 3 / 5 := by
  have h := s.execution.gain_balance 1 pR
  rw [s.receiver_gain_target] at h
  linarith

theorem error_other (i : Fin 2) (q : Port) (h : i ≠ 1 ∨ q ≠ pR) :
    s.execution.ledger.error i q = 0 := by
  have hbalance := s.execution.gain_balance i q
  rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
  · rw [s.sender_gains] at hbalance
    linarith
  · rw [s.receiver_gain_other q (by simpa using h)] at hbalance
    linarith

theorem recovery_zero (i : Fin 2) : s.execution.ledger.recovery i = 0 := by
  have h := s.execution.recovery_balance i
  rw [s.recovery] at h
  linarith

end PortWeakStep
end KernelR.Hybrid
