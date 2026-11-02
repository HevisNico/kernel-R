import KernelR.HybridPortSlowWire
import KernelR.HybridProtectedInputShortCycle

/-! The actual SLOW receiver learns a full protected MARK, reopens at its
own root and meets the sender's true return before the next left source.
No receiver charge, recovery or energy is reset at either handoff. -/
namespace KernelR.Hybrid

structure PortProtectedReturn {θS θR route source pS cycle pR delay}
    {r : @PortSourceWire θS θR route source pS cycle pR delay} {later}
    {p : PortFirstLearnedCut r later} (w : PortSlowWire p) (laterNext : List (Delivery 2)) where
  protectedCycle : ProtectedInputShortCycle θR (fun _ _ => []) w.receiverLocal pR
  senderFinal : Snapshot 1
  senderExecution : Execution θS (fun _ _ => []) w.senderCut.state senderFinal
  receiverFinal : Snapshot 1
  receiverExecution : Execution θR (fun _ _ => []) w.receiverLocal receiverFinal
  sender_date : senderFinal.time = p.final.time + 8
  receiver_date : receiverFinal.time = p.final.time + 8
  final : Snapshot 2
  execution : Execution (extendParameters θS (θR 0)) route w.final final
  date : final.time = p.final.time + 8
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_active : final.raw 0 pS = some (p.final.time + 8)
  raw_other : ∀ i q, i ≠ 0 ∨ q ≠ pS → final.raw i q = none
  pending : final.pending = laterNext
  gains : ∀ i q, final.x i (.z q) = w.final.x i (.z q)
  sender_recovery : final.x 0 .b = w.final.x 0 .b
  receiver_recovery : final.x 1 .b = w.final.x 1 .b + 1 / 10
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨0,pS,p.final.time + 8⟩]
  physical : PhysicalInvariant (extendParameters θS (θR 0)) final
  raw_valid : RawValid final
  complete : CompleteThrough execution (p.final.time + 8)

/-- The low recovery is the receiver's own retained newborn recovery. The
protected phase, return and next source delivery are all constructed. -/
theorem port_protected_return_exists {θS θR ε route source pS cycle pR delay}
    {r : @PortSourceWire θS θR route source pS cycle pR delay} {later}
    {p : PortFirstLearnedCut r later} (w : PortSlowWire p)
    (hb : PhysicalBox (extendParameters θS (θR 0)) ε)
    (laterNext : List (Delivery 2))
    (hqueue : later = ⟨0,pS,p.final.time + 8⟩ :: laterNext)
    (hlater : ∀ d ∈ laterNext, p.final.time + 8 < d.due) :
    Nonempty (PortProtectedReturn w laterNext) := by
  have hbR : PhysicalBox θR ε := by
    refine ⟨hb.1,?_⟩
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hb.2 1 q
  have hLow : 7999 / 100000 ≤ w.receiverLocal.x 0 .b ∧ w.receiverLocal.x 0 .b ≤ 8001 / 100000 := by
    change 7999 / 100000 ≤ w.final.x 1 .b ∧ w.final.x 1 .b ≤ 8001 / 100000
    rw [w.recovery,p.recovery]
    exact p.lowSpan.initial_low_b
  obtain ⟨protectedCycle⟩ := protected_input_short_cycle_exists (route := fun _ _ => [])
    hbR w.receiverLocal pR w.receiver_local_physical w.receiver_local_raw_valid
    w.receiver_main_slow ⟨w.receiver_charge.1.le,w.receiver_charge.2.le⟩ hLow
    w.receiver_aux_rest w.raw_active w.raw_other_receiver
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let receiverBase := protectedCycle.final
  have hReceiverBaseDate : receiverBase.time = w.final.time + 13 / 2 := protectedCycle.date
  have hReceiverWait : receiverBase.time < p.final.time + 8 := by
    rw [hReceiverBaseDate,p.date]
    linarith [w.receiving_gap.2,r.window.2]
  have hReceiverPending : receiverBase.pending = [] := protectedCycle.pending
  let receiverWaitFlow : Flow θR receiverBase (quietAt receiverBase (p.final.time + 8)) :=
    quietFlow receiverBase hReceiverWait (fun j => (protectedCycle.ready j).ready)
      (fun j q => ((protectedCycle.ready j).auxiliary q).1) protectedCycle.raw_none
      (fun j => by linarith [(protectedCycle.ready j).charge.2])
      (fun j q => by linarith [((protectedCycle.ready j).auxiliary q).2.2])
      (by intro d hd; rw [hReceiverPending] at hd; contradiction)
  let receiverWait : Execution θR (fun _ _ => []) receiverBase (quietAt receiverBase (p.final.time + 8)) :=
    .cons (.flow receiverWaitFlow) (.nil _)
  let receiverFinal := quietAt receiverBase (p.final.time + 8)
  let receiverExecution := protectedCycle.execution.append receiverWait
  have heR : receiverExecution.ledger.emissions = [] := by
    change (protectedCycle.execution.append receiverWait).ledger.emissions = []
    rw [Execution.emissions_append,protectedCycle.emissions]
    rfl
  have hdR : receiverExecution.deliveries = [] := by
    change (protectedCycle.execution.append receiverWait).deliveries = []
    rw [Execution.deliveries_append,protectedCycle.deliveries]
    rfl
  have hRready : ∀ j, ReadyCoordinates receiverFinal j :=
    fun j => quietAt_ready_coordinates receiverBase j (protectedCycle.ready j) hReceiverWait.le
  have hRprepared : PreparedSection receiverFinal 0 :=
    ⟨(hRready 0).ready,(hRready 0).charge,(protectedCycle.prepared 0).recovery,(hRready 0).auxiliary⟩
  have hRcharge : receiverFinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (receiverBase.x 0 .q) receiverBase.time (p.final.time + 8) = _
    have hq : receiverBase.x 0 .q = 1 / 10 := protectedCycle.charge
    rw [hq]
    simp [relax]
  have hRgain : ∀ q, receiverFinal.x 0 (.z q) = w.final.x 1 (.z q) := protectedCycle.gains 0
  have hRrec : receiverFinal.x 0 .b = w.final.x 1 .b + 1 / 10 := protectedCycle.recovery_gain
  have hRraw : ∀ j q, receiverFinal.raw j q = none := protectedCycle.raw_none
  let senderBase := w.nextCycle.returned.final
  have hSenderWait : senderBase.time < p.final.time + 8 := by
    change w.nextCycle.returned.final.time < _
    rw [w.nextCycle.date]
    norm_num [portSourceSender,Snapshot.cellProjection]
  have hSenderPending : senderBase.pending = [] := w.nextCycle.pending
  let senderWaitFlow : Flow θS senderBase (quietAt senderBase (p.final.time + 8)) :=
    quietFlow senderBase hSenderWait (fun j => (w.nextCycle.ready j).ready)
      (fun j q => ((w.nextCycle.ready j).auxiliary q).1) w.nextCycle.raw_none
      (fun j => by linarith [(w.nextCycle.ready j).charge.2])
      (fun j q => by linarith [((w.nextCycle.ready j).auxiliary q).2.2])
      (by intro d hd; rw [hSenderPending] at hd; contradiction)
  let senderWait : Execution θS (fun _ _ => []) senderBase (quietAt senderBase (p.final.time + 8)) :=
    .cons (.flow senderWaitFlow) (.nil _)
  let senderFinal := quietAt senderBase (p.final.time + 8)
  let fastTail : Execution θS (fun _ _ => []) w.senderCut.state w.nextCycle.fast.final :=
    .cons (.flow w.senderCut.flow) w.senderCut.rest
  let senderExecution := fastTail.append (w.nextCycle.returned.execution.append senderWait)
  have heFast : fastTail.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (w.senderCut.emissions.symm.trans w.nextCycle.fast.emissions)).2
  have hdFast : fastTail.deliveries = [] :=
    (List.append_eq_nil_iff.mp (w.senderCut.deliveries.symm.trans w.nextCycle.fast.deliveries)).2
  have heS : senderExecution.ledger.emissions = [] := by
    change (fastTail.append (w.nextCycle.returned.execution.append senderWait)).ledger.emissions = []
    rw [Execution.emissions_append fastTail (w.nextCycle.returned.execution.append senderWait),heFast,
      Execution.emissions_append w.nextCycle.returned.execution senderWait,w.nextCycle.returned.emissions]
    rfl
  have hdS : senderExecution.deliveries = [] := by
    change (fastTail.append (w.nextCycle.returned.execution.append senderWait)).deliveries = []
    rw [Execution.deliveries_append fastTail (w.nextCycle.returned.execution.append senderWait),hdFast,
      Execution.deliveries_append w.nextCycle.returned.execution senderWait,w.nextCycle.returned.deliveries]
    rfl
  have hSready : ∀ j, ReadyCoordinates senderFinal j :=
    fun j => quietAt_ready_coordinates senderBase j (w.nextCycle.ready j) hSenderWait.le
  have hSprepared : PreparedSection senderFinal 0 :=
    ⟨(hSready 0).ready,(hSready 0).charge,(w.nextCycle.prepared 0).recovery,(hSready 0).auxiliary⟩
  have hScharge : senderFinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (senderBase.x 0 .q) senderBase.time (p.final.time + 8) = _
    have hq : senderBase.x 0 .q = 1 / 10 := w.nextCycle.charge
    rw [hq]
    simp [relax]
  have hSgain : ∀ q, senderFinal.x 0 (.z q) = w.final.x 0 (.z q) := by
    intro q
    change w.nextCycle.returned.final.x 0 (.z q) = _
    rw [w.nextCycle.gains,w.gains]
    rfl
  have hSrec : senderFinal.x 0 .b = w.final.x 0 .b := by
    change w.nextCycle.returned.final.x 0 .b = _
    rw [w.nextCycle.recovery,w.recovery]
    rfl
  have hSraw : ∀ j q, senderFinal.raw j q = none := w.nextCycle.raw_none
  have hstart : w.senderCut.state.time = w.receiverLocal.time := w.senderCut.date.trans w.date.symm
  have hQ : ∀ d ∈ later, senderFinal.time ≤ d.due := by
    intro d hd
    rw [hqueue] at hd
    change p.final.time + 8 ≤ d.due
    rcases List.mem_cons.mp hd with rfl | hd
    · exact le_rfl
    · exact (hlater d hd).le
  obtain ⟨woven,heW,hdW⟩ := senderExecution.product_neutral receiverExecution hstart rfl
    heS hdS heR hdR later hQ route
  let span := woven.cast_source w.product_receiver_projection.symm
  have heSpan : span.ledger.emissions = [] := by rw [Execution.cast_source_ledger]; exact heW
  have hdSpan : span.deliveries = [] := by rw [Execution.cast_source_deliveries]; exact hdW
  let before := senderFinal.product receiverFinal later
  let final : Snapshot 2 := {(setRaw before 0 pS (some before.time)) with pending := [] ++ laterNext}
  have hqueueBefore : before.pending = [] ++ (⟨0,pS,p.final.time + 8⟩ : Delivery 2) :: laterNext := hqueue
  let arrival : Jump route before final := .arrive before ⟨0,pS,p.final.time + 8⟩ [] laterNext hqueueBefore rfl (hSraw 0 pS)
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨0,pS,p.final.time + 8⟩] := rfl
  let trace := span.append (.cons (.jump arrival) (.nil _))
  have hRawActive : final.raw 0 pS = some (p.final.time + 8) := by
    simp [final,setRaw,before,Snapshot.product,senderFinal,quietAt]
  have hRawOther : ∀ i q, i ≠ 0 ∨ q ≠ pS → final.raw i q = none := by
    intro i q h
    change (setRaw before 0 pS (some before.time)).raw i q = none
    rw [raw_update_other _ _ _ _ _ _ h]
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact hSraw 0 q
    · exact hRraw 0 q
  have hprepared : ∀ i, PreparedSection final i := by
    intro i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact ⟨hSprepared.ready,hSprepared.charge,hSprepared.recovery,hSprepared.auxiliary⟩
    · exact ⟨hRprepared.ready,hRprepared.charge,hRprepared.recovery,hRprepared.auxiliary⟩
  have hcharge : ∀ i, final.x i .q = 1 / 10 := by
    intro i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact hScharge
    · exact hRcharge
  have hfuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    change d ∈ [] ++ laterNext at hd
    simp only [List.nil_append] at hd
    exact hlater d hd
  have hcomplete : CompleteThrough trace (p.final.time + 8) := by
    refine ⟨rfl,?_,hfuture⟩
    intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro i
        rw [(hprepared i).ready,hcharge i]; norm_num
      · intro i q
        rw [((hprepared i).auxiliary q).1]
        linarith [((hprepared i).auxiliary q).2.2]
    · intro i q origin hr
      by_cases h : i = 0 ∧ q = pS
      · obtain ⟨rfl,rfl⟩ := h
        have ho : origin = p.final.time + 8 := Option.some.inj (hr.symm.trans hRawActive)
        rw [ho]; change p.final.time + 8 < p.final.time + 8 + 1; linarith
      · rw [hRawOther i q (by tauto)] at hr; contradiction
    · exact hfuture
  refine ⟨{
    protectedCycle := protectedCycle, senderFinal := senderFinal, senderExecution := senderExecution
    receiverFinal := receiverFinal, receiverExecution := receiverExecution
    sender_date := rfl, receiver_date := rfl, final := final, execution := trace, date := rfl
    prepared := hprepared, charge := hcharge, raw_active := hRawActive, raw_other := hRawOther, pending := rfl
    gains := ?_, sender_recovery := hSrec, receiver_recovery := hRrec, emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb w.physical
    raw_valid := trace.raw_valid w.raw_valid, complete := hcomplete
  }⟩
  · intro i q
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact hSgain q
    · exact hRgain q
  · simp only [trace,Execution.emissions_append,heSpan,Execution.ledger,Move.ledger,haEm,
      Ledger.add,Ledger.zero,List.append_nil]
  · simp only [trace,Execution.deliveries_append,hdSpan,Execution.deliveries,Move.deliveries,haDel,
      List.nil_append,List.append_nil]

namespace PortProtectedReturn
variable {θS θR route source pS cycle pR delay}
  {r : @PortSourceWire θS θR route source pS cycle pR delay} {later}
  {p : PortFirstLearnedCut r later} {w : PortSlowWire p} {laterNext}
  (t : PortProtectedReturn w laterNext)

theorem ready (i : Fin 2) : ReadyCoordinates t.final i := (t.prepared i).ready_coordinates

theorem error_zero (i : Fin 2) (q : Port) : t.execution.ledger.error i q = 0 := by
  have h := t.execution.gain_balance i q
  rw [t.gains] at h
  linarith

theorem sender_recovery_zero : t.execution.ledger.recovery 0 = 0 := by
  have h := t.execution.recovery_balance 0
  rw [t.sender_recovery] at h
  linarith

theorem receiver_recovery_dose : t.execution.ledger.recovery 1 = 1 / 10 := by
  have h := t.execution.recovery_balance 1
  rw [t.receiver_recovery] at h
  linarith

theorem mark_other (q : Port) (hq : q ≠ pR) : t.execution.ledger.mark 1 q = 0 := by
  have hno : NoArrivalAt t.execution 1 q := by simp [NoArrivalAt,t.deliveries]
  have hquiet := t.execution.aux_ready_without_input_band 1 q (w.receiver_aux_rest q).1
    (w.receiver_aux_rest q).2.2 (w.raw_other_receiver q hq) hno
  exact t.execution.mark_zero_aux 1 q .ready (by decide)
    (t.execution.allStates_aux_flows 1 q .ready hquiet)

theorem mark_dose : t.execution.ledger.mark 1 pR = 1 / 10 := by
  have h := t.execution.recovery_sum_marks 1
  rw [t.receiver_recovery_dose,
    Finset.sum_eq_single pR (fun q _ hq => t.mark_other q hq) (by simp)] at h
  exact h.symm

end PortProtectedReturn
end KernelR.Hybrid
