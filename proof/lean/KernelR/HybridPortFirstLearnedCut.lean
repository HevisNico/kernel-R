import KernelR.HybridPortWeakStep
import KernelR.HybridLowRecoverySlowSpanExtension
import KernelR.HybridIntervalClosedExecutionProduct

/-! The receiver's first real learned FIRE and low-recovery SLOW cut at the
next sender source. The original SLOW path continues past the common clock. -/
namespace KernelR.Hybrid

private theorem execution_prefix_append {n θ route s v u}
    (e : @Execution n θ route s v) (tail : Execution θ route v u) :
    (e.append tail).IsPrefix e := by
  induction e with
  | nil => exact .nil _
  | cons move rest ih => exact .step move _ rest (ih tail)

structure PortFirstLearnedCut {θS θR route source pS cycle pR delay}
    (r : @PortSourceWire θS θR route source pS cycle pR delay) (later : List (Delivery 2)) where
  fire : FirstLearnedFire θR (fun _ _ => []) r.receiverLocal 0 pR
  fast : MidLearnedFastEnd fire
  lowSpan : LowRecoverySlowSpan fast (source.time + 8)
  fullLowSpan : LowRecoverySlowSpan fast (r.final.time + 81 / 10)
  heldFlow : Flow θR lowSpan.final fullLowSpan.final
  full_reconstruct : fullLowSpan.execution = lowSpan.execution.append (.cons (.flow heldFlow) (.nil _))
  lowCut : fullLowSpan.execution.BeforeFlowCut (source.time + 8)
  lowCut_state : lowCut.state = lowSpan.final
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
  receiver_values : final.x 1 = lowSpan.final.x 0
  receiver_main : final.main 1 = .slow
  receiver_aux_rest : ∀ q, final.aux 1 q = .ready ∧ RestBand (final.x 1 (.m q))
  receiver_charge : 1 / 10 < final.x 1 .q ∧ final.x 1 .q ≤ 1 / 4
  receiver_raw_none : ∀ q, final.raw 1 q = none
  receiver_pending : lowSpan.final.pending = []
  raw_active : final.raw 0 pS = some (source.time + 8)
  raw_other_sender : ∀ q, q ≠ pS → final.raw 0 q = none
  pending : final.pending = later
  gains : ∀ i q, final.x i (.z q) = r.final.x i (.z q)
  recovery : ∀ i, final.x i .b = r.final.x i .b
  emissions : execution.ledger.emissions = [(1,fire.final.time)]
  deliveries : execution.deliveries = [⟨0,pS,source.time + 8⟩]
  physical : PhysicalInvariant (extendParameters θS (θR 0)) final
  raw_valid : RawValid final
  complete : CompleteThrough execution (source.time + 8)

/-- READY charge and the receiver's own low recovery are retained throughout
its actual threshold, FAST completion, and SLOW path. The next queued sender
source is consumed only after both genuine paths reach the common clock. -/
theorem port_first_learned_cut_exists {θS θR ε route source pS cycle pR delay}
    (r : @PortSourceWire θS θR route source pS cycle pR delay)
    (hb : PhysicalBox (extendParameters θS (θR 0)) ε)
    (hs : ReadyCoordinates r.final 1)
    (hg : 9 / 5 ≤ Real.exp (r.final.x 1 (.z pR)) ∧ Real.exp (r.final.x 1 (.z pR)) ≤ 11 / 5)
    (hLow : 7999 / 100000 ≤ r.final.x 1 .b ∧ r.final.x 1 .b ≤ 8001 / 100000)
    (hclosed : ∀ t, r.final.time ≤ t → t ≤ source.time + 8 → route 1 t = [])
    (later : List (Delivery 2))
    (hqueue : source.pending = ⟨0,pS,source.time + 8⟩ :: later)
    (hlater : ∀ d ∈ later, source.time + 8 < d.due) :
    Nonempty (PortFirstLearnedCut r later) := by
  have hbR : PhysicalBox θR ε := by
    refine ⟨hb.1,?_⟩
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hb.2 1 q
  have hR : ReadyCoordinates r.receiverLocal 0 := ⟨hs.ready,hs.charge,hs.auxiliary⟩
  have hready : ∀ j, ReadyCoordinates r.receiverLocal j := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hR
  have hother : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ pR → r.receiverLocal.raw j q = none := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact r.raw_other q (by simpa using h)
  have hEmpty : r.receiverLocal.pending = [] := rfl
  have hfuture : ∀ d ∈ r.receiverLocal.pending, r.receiverLocal.time + 31 / 4 ≤ d.due := by
    intro d hd
    rw [hEmpty] at hd
    contradiction
  obtain ⟨fire⟩ := first_mid_learned_fire_exists (route := fun _ _ => []) r.receiverLocal hbR
    r.receiver_local_physical r.receiver_local_raw_valid 0 pR hready hg r.raw_active hother hfuture
  obtain ⟨fast⟩ := fire.mid_learned_fast_end_exists hbR hR hg.2 r.raw_other hfuture
  have hfastTime : fast.final.time = r.final.time + fire.latency + 1 := by
    rw [fast.date,fire.date]
    rfl
  have hfastEmpty : fast.final.pending = [] := by
    rw [fast.pending,fire.pending]
    simp only [List.append_nil]
    exact hEmpty
  obtain ⟨low⟩ := fire.low_recovery_slow_span_exists hbR fast hR hg.2 hLow (source.time + 8)
    (by rw [hfastTime]; linarith [r.window.2,fire.deadline])
    (by change source.time + 8 ≤ r.final.time + 81 / 10; linarith [r.window.1])
    (by intro d hd; rw [hfastEmpty] at hd; contradiction)
  have hlowEmpty : low.final.pending = [] := low.pending.trans hfastEmpty
  obtain ⟨full,held,heFull⟩ := low.flow_continuation_exists hbR (r.final.time + 81 / 10)
    (by linarith [r.window.1]) (by rfl)
    (by intro d hd; rw [hlowEmpty] at hd; contradiction)
  let lowCut : full.execution.BeforeFlowCut (source.time + 8) := {
    state := low.final, cut := low.execution
    isPrefix := by rw [heFull]; exact execution_prefix_append _ _
    date := low.date, nextState := full.final, flow := held, rest := .nil _
    rest_contacts_transversal := fun _ => True.intro
    deliveries := by rw [full.deliveries,low.deliveries]; rfl
    emissions := by rw [full.emissions,low.emissions]; rfl
  }
  let receiverExecution := (fire.execution.append fast.execution).append low.execution
  have heR : receiverExecution.ledger.emissions = [(0,fire.final.time)] := by
    simp only [receiverExecution,Execution.emissions_append,fire.emissions,fast.emissions,
      low.emissions,List.append_nil]
    rw [fire.date]
  have hdR : receiverExecution.deliveries = [] := by
    simp only [receiverExecution,Execution.deliveries_append,fire.deliveries,fast.deliveries,
      low.deliveries,List.append_nil]
  have hRgain : ∀ q, low.final.x 0 (.z q) = r.final.x 1 (.z q) := by
    intro q
    exact (low.gains 0 q).trans ((fast.gains 0 q).trans (fire.gain_preserved 0 q))
  have hRrec : low.final.x 0 .b = r.final.x 1 .b :=
    (low.recovery 0).trans ((fast.recovery 0).trans (fire.recovery_preserved 0))
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
  have hfinish : senderFinal.time = low.final.time := low.date.symm
  have hQ : ∀ d ∈ source.pending, senderFinal.time ≤ d.due := by
    intro d hd
    rw [hqueue] at hd
    change source.time + 8 ≤ d.due
    rcases List.mem_cons.mp hd with rfl | hd
    · exact le_rfl
    · exact (hlater d hd).le
  obtain ⟨woven,heW,hdW⟩ := senderExecution.product_right_closed_on receiverExecution hstart hfinish
    heS hdS hdR source.pending hQ route
    (fun t ht hl => hclosed t ht (by rw [low.date] at hl; exact hl))
  let span := woven.cast_source r.product_receiver_projection.symm
  have heSpan : span.ledger.emissions = [(1,fire.final.time)] := by
    rw [Execution.cast_source_ledger,heW,heR]
    rfl
  have hdSpan : span.deliveries = [] := by rw [Execution.cast_source_deliveries]; exact hdW
  let before := senderFinal.product low.final source.pending
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
  have hrawR : ∀ q, final.raw 1 q = none := by
    intro q
    have h : before.raw 1 q = none := low.raw_none 0 q
    simpa [final,setRaw,Function.update_apply] using h
  have hfutureFinal : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    change d ∈ [] ++ later at hd
    simp only [List.nil_append] at hd
    exact hlater d hd
  have hcomplete : CompleteThrough trace (source.time + 8) := by
    refine ⟨rfl,?_,hfutureFinal⟩
    intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro i
        rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
        · have hm : final.main 0 = .ready := hSprepared.ready
          have hx : final.x 0 .q = 1 / 10 := hScharge
          rw [hm,hx]; norm_num
        · have hm : final.main 1 = .slow := low.main_slow
          have hx : final.x 1 = low.final.x 0 := rfl
          rw [hm,hx]; exact low.charge.1
      · intro i q
        rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
        · have hm : final.aux 0 q = .ready := (hSprepared.auxiliary q).1
          have hx : RestBand (final.x 0 (.m q)) := (hSprepared.auxiliary q).2
          rw [hm]; linarith [hx.2]
        · have hm : final.aux 1 q = .ready := low.auxiliary 0 q
          have hx : RestBand (final.x 1 (.m q)) := low.rest q
          rw [hm]; linarith [hx.2]
    · intro i q origin hr
      rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
      · by_cases hq : q = pS
        · subst q
          have ho : origin = source.time + 8 := Option.some.inj (hr.symm.trans hrawS)
          rw [ho]; change source.time + 8 < source.time + 8 + 1; linarith
        · rw [hrawOther q hq] at hr; contradiction
      · rw [hrawR] at hr; contradiction
    · exact hfutureFinal
  refine ⟨{
    fire := fire, fast := fast, lowSpan := low, fullLowSpan := full, heldFlow := held
    full_reconstruct := heFull, lowCut := lowCut, lowCut_state := rfl
    senderFinal := senderFinal, senderExecution := senderExecution
    sender_date := rfl, sender_pending := hpendingS, sender_emissions := heS, sender_deliveries := hdS
    final := final, execution := trace, date := rfl
    sender_prepared := ⟨hSprepared.ready,hSprepared.charge,hSprepared.recovery,hSprepared.auxiliary⟩
    sender_charge := hScharge, sender_gains := hSgain
    receiver_values := rfl, receiver_main := low.main_slow
    receiver_aux_rest := fun q => ⟨low.auxiliary 0 q,low.rest q⟩
    receiver_charge := low.charge, receiver_raw_none := hrawR, receiver_pending := hlowEmpty
    raw_active := hrawS, raw_other_sender := hrawOther, pending := rfl
    gains := ?_, recovery := ?_, emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb r.physical
    raw_valid := trace.raw_valid r.raw_valid, complete := hcomplete
  }⟩
  · intro i q
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact hSgain q
    · exact hRgain q
  · intro i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact hSrec
    · exact hRrec
  · simp only [trace,Execution.emissions_append,heSpan,Execution.ledger,Move.ledger,haEm,
      Ledger.add,Ledger.zero,List.append_nil]
  · simp only [trace,Execution.deliveries_append,hdSpan,Execution.deliveries,Move.deliveries,haDel,
      List.nil_append,List.append_nil]

namespace PortFirstLearnedCut
variable {θS θR route source pS cycle pR delay}
  {r : @PortSourceWire θS θR route source pS cycle pR delay} {later} (s : PortFirstLearnedCut r later)

/-- The projected receiver is the very endpoint of the retained SLOW path. -/
theorem receiver_local : portSourceReceiver s.final = s.lowSpan.final := by
  have extensionality {n} (v u : Snapshot n) (ht : v.time = u.time) (hx : v.x = u.x)
      (hm : v.main = u.main) (ha : v.aux = u.aux) (hr : v.raw = u.raw) (hp : v.pending = u.pending) : v = u := by
    cases v
    cases u
    simp_all only
  apply extensionality
  · exact s.date.trans s.lowSpan.date.symm
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.receiver_values
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.receiver_main.trans s.lowSpan.main_slow.symm
  · funext j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (s.receiver_aux_rest q).1.trans (s.lowSpan.auxiliary 0 q).symm
  · funext j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (s.receiver_raw_none q).trans (s.lowSpan.raw_none 0 q).symm
  · exact s.receiver_pending.symm

theorem error_zero (i : Fin 2) (q : Port) : s.execution.ledger.error i q = 0 := by
  have h := s.execution.gain_balance i q
  rw [s.gains] at h
  linarith

theorem recovery_zero (i : Fin 2) : s.execution.ledger.recovery i = 0 := by
  have h := s.execution.recovery_balance i
  rw [s.recovery] at h
  linarith

end PortFirstLearnedCut
end KernelR.Hybrid
