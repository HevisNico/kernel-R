import KernelR.HybridConstructedCadenceLeafPacket
import KernelR.HybridLocalCadenceReceiverPacket
import KernelR.HybridCausalHeadSignals

/-! The actual autonomous C trace issues the contacts consumed by a fully
constructed B response. Only C's external sources inhabit the initial shared
queue. B's analysis queue is derived from C's real emission ledger; every
wire enters the operational queue at its genuine C FIRE. -/
namespace KernelR.Hybrid

abbrev cadenceBCParameters (freshB freshC : Parameters) : Fin 2 → Parameters :=
  prependParameters (fun _ : Fin 1 => freshB) (fun _ : Fin 1 => freshC)

noncomputable def cadenceBCContacts (wireDelay : ℝ → ℝ) : HeadRoutes 1 :=
  fun _ time => if (640:ℝ)≤time ∧ time<780 then [⟨0,2,time+wireDelay time⟩] else []

noncomputable def cadenceBCRouter (wireDelay : ℝ → ℝ) : Router 2 :=
  prependRouted (fun _ _ => []) (cadenceBCContacts wireDelay)

def cadenceBCContact (wireDelay : ℝ → ℝ) : Contact 2 := ⟨1,0,2,640,780,wireDelay⟩

noncomputable def cadenceBReceiverSource {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward)
    (packet : KernelR.Chain.Packet 3 17 (1/20)) : Snapshot 1 :=
  {(c.wave.cadence.teaching.final.autonomousView 1) with
    pending:=List.ofFn (fun i : Fin 20 => (⟨0,2,packet.actual i.val⟩ : Delivery 1))}

theorem cadence_bc_contacts_strict (wireDelay : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤wireDelay time ∧ wireDelay time≤2/5) :
    StrictHeadRoutes (cadenceBCContacts wireDelay) := by
  intro i time d h
  simp only [cadenceBCContacts] at h
  split_ifs at h with hg
  · have he : d=(⟨0,2,time+wireDelay time⟩ : Delivery 1) := List.mem_singleton.mp h
    subst d
    change time<time+wireDelay time
    linarith [(hd time).1]
  · contradiction

private theorem bc_head_input_queue {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward} (full : ConstructedCadenceLocalC c)
    (hd : ∀ time, (3/10:ℝ)≤cascadeForward time ∧ cascadeForward time≤2/5) :
    full.execution.headInputQueue (cadenceBCContacts cascadeForward)=
      List.ofFn (fun i : Fin 20 => (⟨0,2,(full.receivedLeafPacket cascadeForward hd).actual i.val⟩ : Delivery 1)) := by
  have hTimes : full.execution.emissionTimes 0=full.execution.ledger.emissions.map Prod.snd := by
    rw [Execution.emissionTimes,List.filter_eq_self.mpr]
    intro ev _
    simp only [decide_eq_true_eq]
    exact Subsingleton.elim _ _
  have hGate : ∀ ev∈full.execution.ledger.emissions, (640:ℝ)≤ev.2 ∧ ev.2<780 := by
    intro ev hev
    have ht : ev.2∈full.execution.emissionTimes 0 := by
      rw [hTimes]
      exact List.mem_map.mpr ⟨ev,hev,rfl⟩
    rw [full.leaf_packet_calendar] at ht
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp ht
    rw [←hi]
    exact ⟨(full.leaf_packet_dates_in_contact i).1,by linarith [(full.leaf_packet_dates_in_contact i).2]⟩
  have aux : ∀ events : List (Fin 1×ℝ),
      (∀ ev∈events, (640:ℝ)≤ev.2 ∧ ev.2<780) →
      events.flatMap (fun ev => cadenceBCContacts cascadeForward ev.1 ev.2)=
        (events.map Prod.snd).map (fun time => (⟨0,2,time+cascadeForward time⟩ : Delivery 1)) := by
    intro events
    induction events with
    | nil => intro _; rfl
    | cons ev events ih =>
      intro h
      rw [List.flatMap_cons,List.map_cons,List.map_cons,ih (fun x hx => h x (by simp [hx]))]
      have he : cadenceBCContacts cascadeForward ev.1 ev.2=
          [⟨0,2,ev.2+cascadeForward ev.2⟩] := ite_eq_left (h ev (by simp))
      rw [he]
      rfl
  change full.execution.ledger.emissions.flatMap _=_
  rw [aux _ hGate,←hTimes,full.leaf_packet_calendar,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [full.received_leaf_actual cascadeForward hd]
  rfl

private theorem bc_initial_physical {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward)
    (packet : KernelR.Chain.Packet 3 17 (1/20)) :
    PhysicalInvariant (cadenceBCParameters freshB freshC)
      ((c.wave.cadence.teaching.final.autonomousView 2).prependQueued (cadenceBReceiverSource c packet)
        ((c.wave.cadence.teaching.final.autonomousView 2).pending.map Delivery.succ)) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact c.wave.cadence.teaching.physical.region 1
    · exact c.wave.cadence.teaching.physical.region 2
  · intro i q
    fin_cases i
    · exact c.wave.cadence.teaching.physical.gain_cap 1 q
    · exact c.wave.cadence.teaching.physical.gain_cap 2 q
  · intro i
    fin_cases i
    · exact c.wave.cadence.teaching.physical.recovery_cap 1
    · exact c.wave.cadence.teaching.physical.recovery_cap 2
  · intro i
    fin_cases i
    · exact c.wave.cadence.teaching.physical.reserve 1
    · exact c.wave.cadence.teaching.physical.reserve 2

private theorem bc_initial_raw_valid {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward)
    (packet : KernelR.Chain.Packet 3 17 (1/20)) :
    RawValid ((c.wave.cadence.teaching.final.autonomousView 2).prependQueued (cadenceBReceiverSource c packet)
      ((c.wave.cadence.teaching.final.autonomousView 2).pending.map Delivery.succ)) := by
  intro i q origin hr
  fin_cases i
  · exact c.wave.cadence.teaching.raw_valid 1 q origin hr
  · exact c.wave.cadence.teaching.raw_valid 2 q origin hr

structure ConstructedBCadence {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward) where
  wire_bound : ∀ time, (3/10:ℝ)≤cascadeForward time ∧ cascadeForward time≤2/5
  fullC : ConstructedCadenceLocalC c
  bPacket : KernelR.Chain.Packet 3 17 (1/20)
  b_packet_eq : bPacket=fullC.receivedLeafPacket cascadeForward wire_bound
  bSource : Snapshot 1
  b_source_state : bSource=cadenceBReceiverSource c bPacket
  b_head_queue : bSource.pending=fullC.execution.headInputQueue (cadenceBCContacts cascadeForward)
  bRun : LocalCadenceReceiver (fun _ : Fin 1 => freshB) bSource 2 bPacket (7899/10)
  weave : CausalHeadWeave fullC.execution bRun.execution
    ((c.wave.cadence.teaching.final.autonomousView 2).pending.map Delivery.succ) (cadenceBCContacts cascadeForward)
  source : Snapshot 2
  source_state : source=(c.wave.cadence.teaching.final.autonomousView 2).prependQueued bSource
    ((c.wave.cadence.teaching.final.autonomousView 2).pending.map Delivery.succ)
  final : Snapshot 2
  final_state : final=fullC.final.prependQueued bRun.final weave.pending
  execution : Execution (cadenceBCParameters freshB freshC) (cadenceBCRouter cascadeForward) source final
  execution_eq : HEq execution weave.execution
  date : final.time=7899/10
  pending : final.pending=[]
  ready : ∀ i, ReadyCoordinates final i
  charge : ∀ i, final.x i .q=1/10
  raw_none : ∀ i q, final.raw i q=none
  b_emission_times : execution.emissionTimes 0=bRun.execution.emissionTimes 0
  c_emission_times : execution.emissionTimes 1=fullC.execution.emissionTimes 0
  b_emission_count : (execution.emissionTimes 0).length=18
  c_emission_count : (execution.emissionTimes 1).length=20
  b_gain_target : final.x 0 (.z 2)=newbornB.x (.z 2)+12/5
  c_gain_target : final.x 1 (.z 0)=newbornC.x (.z 0)+12/5
  b_recovery : final.x 0 .b=newbornB.x .b+3/10
  c_recovery : final.x 1 .b=newbornC.x .b+3/10
  physical : PhysicalInvariant (cadenceBCParameters freshB freshC) final
  raw_valid : RawValid final
  complete : CompleteThrough execution (7899/10)

/-- Construct B from the true C emission packet, then weave both physical
paths. The shared initial queue contains only already-present external C
sources; the twenty B contacts are issued by the actual C FIREs. -/
theorem constructed_b_cadence_exists {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward ε}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hd : ∀ time, (3/10:ℝ)≤cascadeForward time ∧ cascadeForward time≤2/5) :
    Nonempty (ConstructedBCadence c) := by
  obtain ⟨full⟩ := c.local_c_full_exists hb
  let packet := full.receivedLeafPacket cascadeForward hd
  let bSource := cadenceBReceiverSource c packet
  have hfB : PhysicalInvariant (fun _ : Fin 1 => freshB) bSource :=
    ⟨fun _ => c.wave.cadence.teaching.physical.region 1,
      fun _ q => c.wave.cadence.teaching.physical.gain_cap 1 q,
      fun _ => c.wave.cadence.teaching.physical.recovery_cap 1,
      fun _ => c.wave.cadence.teaching.physical.reserve 1⟩
  have hvB : RawValid bSource := fun _ q origin h => c.wave.cadence.teaching.raw_valid 1 q origin h
  have hsB : PreparedSection bSource 0 :=
    ⟨(c.wave.cadence.teaching.prepared 1).ready,(c.wave.cadence.teaching.prepared 1).charge,
      (c.wave.cadence.teaching.prepared 1).recovery,(c.wave.cadence.teaching.prepared 1).auxiliary⟩
  have hqB : bSource.x 0 .q=1/10 := c.wave.cadence.teaching.charge 1
  have hrB : ∀ q, bSource.raw 0 q=none := c.wave.cadence.teaching.raw_none 1
  have hzB : Real.log (3/10)+9/5-1/100000≤bSource.x 0 (.z 2) ∧
      bSource.x 0 (.z 2)≤Real.log (3/10)+9/5+1/100000 := by
    have hOwn : bSource.x 0 (.z 2)=newbornB.x (.z 2)+9/5 := c.wave.cadence.teaching.b_gain_target
    rw [hOwn]
    have h := newbornB.gain 2
    simp only [nominalGain,show (2:Port)≠1 by decide,ite_false] at h
    constructor <;> linarith [h.1,h.2]
  have hfirst : bSource.time<packet.actual 0 := by
    change c.wave.cadence.teaching.final.time<(full.receivedLeafPacket cascadeForward hd).actual 0
    rw [c.wave.cadence.teaching.date,full.received_leaf_actual,full.leaf_packet_actual_zero]
    linarith [full.leaf_first_window.1,(hd c.wave.cadence.wire.fire.final.time).1]
  have hterminal : packet.actual (3+17-1)+19/5≤(7899/10:ℝ) := by
    change (full.receivedLeafPacket cascadeForward hd).actual 19+19/5≤(7899/10:ℝ)
    rw [full.received_leaf_actual]
    have hg := (full.leaf_packet_dates_in_contact (19:Fin 20)).2
    norm_num at hg
    linarith [(hd (full.leafPacket.actual 19)).2]
  obtain ⟨bRun⟩ := local_cadence_receiver_exists hb.extend_old.extend_new bSource 2 packet (7899/10)
    (by norm_num) (by norm_num) hfB hvB hsB hqB hrB hzB rfl hfirst hterminal
  have hQueue : bSource.pending=full.execution.headInputQueue (cadenceBCContacts cascadeForward) :=
    (bc_head_input_queue full hd).symm
  have hStart : (c.wave.cadence.teaching.final.autonomousView 2).time=bSource.time := rfl
  have hBalance := HeadQueueBalance.initial full.execution bSource (cadenceBCContacts cascadeForward) hQueue
  obtain ⟨weave⟩ := full.execution.prepend_causal_result bRun.execution
    hStart (full.complete.1.trans bRun.complete.1.symm)
    (cadenceBCContacts cascadeForward) (cadence_bc_contacts_strict cascadeForward hd)
    ((c.wave.cadence.teaching.final.autonomousView 2).pending.map Delivery.succ) hBalance
  let Qend := weave.pending
  let global := weave.execution
  have hComplete := weave.complete full.complete bRun.complete
  have hEmpty : Qend=[] := weave.pending_empty full.pending bRun.pending
  let source := (c.wave.cadence.teaching.final.autonomousView 2).prependQueued bSource
    ((c.wave.cadence.teaching.final.autonomousView 2).pending.map Delivery.succ)
  let final := full.final.prependQueued bRun.final Qend
  have hReady : ∀ i, ReadyCoordinates final i := by
    intro i
    fin_cases i
    · exact ⟨(bRun.ready 0).ready,(bRun.ready 0).charge,(bRun.ready 0).auxiliary⟩
    · exact ⟨(full.ready 0).ready,(full.ready 0).charge,(full.ready 0).auxiliary⟩
  have hCharge : ∀ i, final.x i .q=1/10 := by
    intro i
    fin_cases i
    · exact bRun.charge
    · exact full.charge
  have hRaw : ∀ i q, final.raw i q=none := by
    intro i q
    fin_cases i
    · exact bRun.raw_none 0 q
    · exact full.raw_none 0 q
  have hBCBox : PhysicalBox (cadenceBCParameters freshB freshC) ε := by
    refine ⟨hb.1,?_⟩
    intro i q
    fin_cases i
    · exact hb.2 1 q
    · exact hb.2 2 q
  have hBTarget : final.x 0 (.z 2)=newbornB.x (.z 2)+12/5 := by
    change bRun.final.x 0 (.z 2)=_
    rw [bRun.gain_target]
    change c.wave.cadence.teaching.final.x 1 (.z 2)+3/5=_
    rw [c.wave.cadence.teaching.b_gain_target]
    ring
  have hBRecovery : final.x 0 .b=newbornB.x .b+3/10 := by
    change bRun.final.x 0 .b=_
    rw [bRun.recovery_gain]
    change c.wave.cadence.teaching.final.x 1 .b+1/5=_
    rw [c.wave.cadence.teaching.b_recovery]
    ring
  refine ⟨{
    wire_bound:=hd,fullC:=full,bPacket:=packet,b_packet_eq:=rfl,bSource:=bSource,b_source_state:=rfl
    b_head_queue:=hQueue,bRun:=bRun,weave:=weave,source:=source,source_state:=rfl
    final:=final,final_state:=rfl,execution:=global,execution_eq:=HEq.rfl,date:=full.date
    pending:=hEmpty,ready:=hReady,charge:=hCharge,raw_none:=hRaw
    b_emission_times:=weave.head_emission_times,c_emission_times:=weave.tail_emission_times 0
    b_emission_count:=?_,c_emission_count:=?_,b_gain_target:=hBTarget,c_gain_target:=full.c_gain_own
    b_recovery:=hBRecovery,c_recovery:=full.c_recovery_own
    physical:=global.physical_invariant hBCBox (bc_initial_physical c packet)
    raw_valid:=global.raw_valid (bc_initial_raw_valid c packet),complete:=hComplete
  }⟩
  · exact (congrArg List.length weave.head_emission_times).trans bRun.emission_count
  · exact (congrArg List.length (weave.tail_emission_times 0)).trans full.emission_count

namespace ConstructedBCadence
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward} (bc : ConstructedBCadence c)

/-- The initial physical coordinates are exactly B and C at the already
constructed teaching boundary; only their analysis queues differ locally. -/
theorem source_x (i : Fin 2) : bc.source.x i=c.wave.cadence.teaching.final.x i.succ := by
  rw [bc.source_state,bc.b_source_state]
  fin_cases i <;> rfl

theorem source_main (i : Fin 2) : bc.source.main i=c.wave.cadence.teaching.final.main i.succ := by
  rw [bc.source_state,bc.b_source_state]
  fin_cases i <;> rfl

theorem source_aux (i : Fin 2) (q : Port) :
    bc.source.aux i q=c.wave.cadence.teaching.final.aux i.succ q := by
  rw [bc.source_state,bc.b_source_state]
  fin_cases i <;> rfl

theorem source_raw (i : Fin 2) (q : Port) :
    bc.source.raw i q=c.wave.cadence.teaching.final.raw i.succ q := by
  rw [bc.source_state,bc.b_source_state]
  fin_cases i <;> rfl

theorem source_date : bc.source.time=6399/10 := by
  rw [bc.source_state]
  exact c.wave.cadence.teaching.date

/-- No future B wire has been inserted into the shared initial queue. -/
theorem source_pending : bc.source.pending=sourceTrain 1 0 640 4 25 := by
  rw [bc.source_state]
  change ((c.wave.cadence.teaching.final.autonomousView 2).pending.map Delivery.succ)=_
  rw [ConstructedCadenceLocalC.source_pending (c:=c)]
  simp only [sourceTrain,List.map_ofFn]
  rfl

theorem source_ready (i : Fin 2) : ReadyCoordinates bc.source i := by
  rw [bc.source_state,bc.b_source_state]
  fin_cases i
  · exact ⟨(c.wave.cadence.teaching.prepared 1).ready,
      (c.wave.cadence.teaching.prepared 1).charge,(c.wave.cadence.teaching.prepared 1).auxiliary⟩
  · exact ⟨(c.wave.cadence.teaching.prepared 2).ready,
      (c.wave.cadence.teaching.prepared 2).charge,(c.wave.cadence.teaching.prepared 2).auxiliary⟩

theorem b_values : bc.final.x 0=bc.bRun.final.x 0 := by rw [bc.final_state]; rfl

theorem c_values : bc.final.x 1=bc.fullC.final.x 0 := by rw [bc.final_state]; rfl

theorem b_gain_other (q : Port) (hq : q≠2) :
    bc.final.x 0 (.z q)=c.wave.cadence.teaching.final.x 1 (.z q) := by
  rw [bc.b_values,bc.bRun.gain_other q hq,bc.b_source_state]
  rfl

theorem c_gain_other (q : Port) (hq : q≠0) :
    bc.final.x 1 (.z q)=c.wave.cadence.teaching.final.x 2 (.z q) := by
  rw [bc.c_values,bc.fullC.tail.gain_other q hq]
  change c.mark.localSource.final.x 0 (.z q)=_
  rw [←congrFun c.mark.c_values (.z q),c.gains,c.wave.gains,
    c.wave.cadence.gain_other 2 q (Or.inr hq)]

/-- B's actual output remains a packet of five prefix FIREs and thirteen
exact-rest tail FIREs, ready to be routed to a further receiving cell. -/
noncomputable def outputPacket : KernelR.Chain.Packet 5 13 (1/20) := bc.bRun.outputPacket

theorem output_packet_calendar : bc.execution.emissionTimes 0=
    List.ofFn (fun i : Fin 18 => bc.outputPacket.actual i.val) := by
  rw [bc.b_emission_times]
  exact bc.bRun.output_packet_calendar

/-- Exact work values from each retained local physical execution. -/
theorem b_energy_actual : bc.final.x 0 .energy=bc.bRun.final.x 0 .energy :=
  congrFun bc.b_values .energy

theorem c_energy_actual : bc.final.x 1 .energy=bc.fullC.final.x 0 .energy :=
  congrFun bc.c_values .energy

end ConstructedBCadence

theorem cadenceBCRouter_eq_contact (wireDelay : ℝ → ℝ) :
    cadenceBCRouter wireDelay=(cadenceBCContact wireDelay).route := by
  funext i time
  fin_cases i
  · simp [cadenceBCRouter,prependRouted,cadenceBCContact,Contact.route]
  · change ((if (640:ℝ)≤time ∧ time<780 then
        [(⟨0,2,time+wireDelay time⟩ : Delivery 1)] else []).map (Delivery.head (n:=1)))=
      (if (1:Fin 2)=1 ∧ 640≤time ∧ time<780 then
        [(⟨0,2,time+wireDelay time⟩ : Delivery 2)] else [])
    by_cases hg : (640:ℝ)≤time ∧ time<780 <;> simp [hg,Delivery.head]

namespace ConstructedBCadence
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward} (bc : ConstructedBCadence c)

/-- These tokens are extracted from the actual global FIRE ledger. Their
identity with the receiver's input packet is a conclusion of construction. -/
theorem issued_b_tokens : bc.execution.issuedTo 0=
    List.ofFn (fun i : Fin 20 => (⟨0,2,bc.bPacket.actual i.val⟩ : Delivery 2)) := by
  have hwire : ∀ event∈bc.execution.ledger.emissions,
      ((cadenceBCRouter cascadeForward) event.1 event.2).filter
        (fun d => d.cell=(cadenceBCContact cascadeForward).target)=
      (cadenceBCContact cascadeForward).route event.1 event.2 := by
    intro event _
    rw [cadenceBCRouter_eq_contact]
    unfold Contact.route
    split_ifs <;> simp [Contact.token,cadenceBCContact]
  have hGate : ∀ time∈bc.fullC.execution.emissionTimes 0, (640:ℝ)≤time ∧ time<780 := by
    intro time ht
    rw [bc.fullC.leaf_packet_calendar] at ht
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨(bc.fullC.leaf_packet_dates_in_contact i).1,
      by linarith [(bc.fullC.leaf_packet_dates_in_contact i).2]⟩
  have h := bc.execution.issuedTo_contact (cadenceBCContact cascadeForward) hwire
  change bc.execution.issuedTo 0=((bc.execution.emissionTimes 1).filter
    (fun t => (640:ℝ)≤t ∧ t<780)).map (cadenceBCContact cascadeForward).token at h
  rw [h,bc.c_emission_times,List.filter_eq_self.mpr (fun t ht => by
    simp only [decide_eq_true_eq]; exact hGate t ht),bc.fullC.leaf_packet_calendar,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [bc.b_packet_eq,bc.fullC.received_leaf_actual]
  rfl

theorem issued_b_count : (bc.execution.issuedTo 0).length=20 := by
  rw [bc.issued_b_tokens,List.length_ofFn]

/-- Each actual B output retains an actual C input and its physical response
latency; the contact gate covers all eighteen outputs. -/
theorem b_packet_dates_in_contact (i : Fin 18) :
    (640:ℝ)≤bc.outputPacket.actual i.val ∧ bc.outputPacket.actual i.val<742 := by
  obtain ⟨k,latency,hlo,hhi,he⟩ := KernelR.Chain.relay_cadence_input_origin bc.bPacket
    bc.bRun.tail_size bc.bRun.lowLatency bc.bRun.firstHighLatency bc.bRun.restHighLatency
    bc.bRun.low_latency_bounds bc.bRun.first_high_latency_bounds
    bc.bRun.rest_high_latency_bounds bc.bRun.high_latency_order i
  change bc.outputPacket.actual i.val=bc.bPacket.actual k.val+latency at he
  rw [he,bc.b_packet_eq,bc.fullC.received_leaf_actual]
  have hg := bc.fullC.leaf_packet_dates_in_contact k
  have hd := bc.wire_bound (bc.fullC.leafPacket.actual k.val)
  constructor <;> linarith [hg.1,hg.2,hd.1,hd.2]

/-- The return contact samples its delay at the actual B FIRE. -/
noncomputable def bWireError (backDelay : ℝ → ℝ) (i : ℕ) : ℝ :=
  backDelay (bc.outputPacket.actual i)-7/20

theorem b_wire_error_bounds (backDelay : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤backDelay time ∧ backDelay time≤2/5) (i : ℕ) :
    -(1/20:ℝ)≤bc.bWireError backDelay i ∧ bc.bWireError backDelay i≤1/20 := by
  dsimp [bWireError]
  constructor <;> linarith [(hd (bc.outputPacket.actual i)).1,(hd (bc.outputPacket.actual i)).2]

noncomputable def receivedBPacket (backDelay : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤backDelay time ∧ backDelay time≤2/5) :
    KernelR.Chain.Packet 5 13 (1/10) := by
  let wired := bc.outputPacket.wire (7/20) (1/20) (by norm_num)
    (bc.bWireError backDelay) (bc.b_wire_error_bounds backDelay hd)
  exact {
    slowDate:=wired.slowDate,settle:=wired.settle,phase:=wired.phase
    prefix_pos:=wired.prefix_pos,tail_pos:=wired.tail_pos,jitter_nonneg:=by norm_num
    prefix_gap:=wired.prefix_gap,settle_bounds:=wired.settle_bounds
    phase_bounds:=by simpa only [show (1/20:ℝ)+1/20=1/10 by norm_num] using wired.phase_bounds
  }

theorem received_b_actual (backDelay : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤backDelay time ∧ backDelay time≤2/5) (i : ℕ) :
    (bc.receivedBPacket backDelay hd).actual i=
      bc.outputPacket.actual i+backDelay (bc.outputPacket.actual i) := by
  change (bc.outputPacket.wire (7/20) (1/20) (by norm_num)
    (bc.bWireError backDelay) (bc.b_wire_error_bounds backDelay hd)).actual i=_
  rw [KernelR.Chain.wire_actual]
  dsimp [bWireError]
  ring

theorem received_b_first_after_teaching (backDelay : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤backDelay time ∧ backDelay time≤2/5) :
    (6399/10:ℝ)<(bc.receivedBPacket backDelay hd).actual 0 := by
  rw [bc.received_b_actual]
  have hg := bc.b_packet_dates_in_contact (0:Fin 18)
  norm_num only [Fin.val_zero] at hg
  linarith [hg.1,(hd (bc.outputPacket.actual 0)).1]

theorem received_b_terminal (backDelay : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤backDelay time ∧ backDelay time≤2/5) (i : Fin 18) :
    (bc.receivedBPacket backDelay hd).actual i.val+19/5≤(7899/10:ℝ) := by
  rw [bc.received_b_actual]
  linarith [(bc.b_packet_dates_in_contact i).2,(hd (bc.outputPacket.actual i.val)).2]

/-- A local analysis input queue derived from the actual B ledger, before a
surrounding causal weaver issues these tokens operationally. -/
noncomputable def returnTokens (backDelay : ℝ → ℝ) : List (Delivery 1) :=
  (bc.execution.emissionTimes 0).map (fun time => ⟨0,2,time+backDelay time⟩)

theorem return_tokens_received_calendar (backDelay : ℝ → ℝ)
    (hd : ∀ time, (3/10:ℝ)≤backDelay time ∧ backDelay time≤2/5) :
    bc.returnTokens backDelay=List.ofFn (fun i : Fin 18 =>
      (⟨0,2,(bc.receivedBPacket backDelay hd).actual i.val⟩ : Delivery 1)) := by
  rw [returnTokens,bc.output_packet_calendar,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [bc.received_b_actual]
  rfl

theorem return_token_provenance (backDelay : ℝ → ℝ) (d : Delivery 1)
    (hd : d∈bc.returnTokens backDelay) :
    ∃ time, time∈bc.execution.emissionTimes 0 ∧ d=⟨0,2,time+backDelay time⟩ := by
  obtain ⟨time,ht,he⟩ := List.mem_map.mp hd
  exact ⟨time,ht,he.symm⟩

end ConstructedBCadence

theorem prepend_cadenceBCParameters (θ : Fin 1 → Parameters) (freshB freshC : Parameters) :
    prependParameters θ (cadenceBCParameters freshB freshC)=
      extendParameters (extendParameters θ freshB) freshC := by
  funext i
  fin_cases i <;> rfl

end KernelR.Hybrid
