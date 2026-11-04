import KernelR.HybridCadenceGlobalGlue

/-! Construct the complete three-cell cadence from the original prepared
teaching boundary, using real locally constructed paths and causal wiring. -/
namespace KernelR.Hybrid

private noncomputable def cadence_cast_router {n θ route route' s u}
    (e : @Execution n θ route s u) (h : route = route') : Execution θ route' s u := h ▸ e

private theorem cadence_router_ledger {n θ route route' s u}
    (e : @Execution n θ route s u) (h : route = route') :
    (cadence_cast_router e h).ledger = e.ledger := by cases h; rfl

private theorem cadence_router_heq {n θ route route' s u}
    (e : @Execution n θ route s u) (h : route = route') :
    HEq (cadence_cast_router e h) e := by cases h; rfl

private theorem cadence_parameters_heq {n θ θ' route s u}
    (e : @Execution n θ route s u) (h : θ = θ') : HEq (e.cast_parameters h) e := by cases h; rfl

private theorem cadence_source_heq {n θ route s v u}
    (e : @Execution n θ route s u) (h : v = s) : HEq (e.cast_source h) e := by cases h; rfl

private theorem cadence_router_complete {n θ route route' s u T}
    (e : @Execution n θ route s u) (h : route = route') (hc : CompleteThrough e T) :
    CompleteThrough (cadence_cast_router e h) T := by cases h; exact hc

structure ConstructedCadenceCascade
    {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward) where
  backward_bound : ∀ time, (3 / 10 : ℝ) ≤ cascadeBackward time ∧ cascadeBackward time ≤ 2 / 5
  bc : ConstructedBCadence c
  aPacket : KernelR.Chain.Packet 5 13 (1 / 10)
  a_packet_eq : aPacket = bc.receivedBPacket cascadeBackward backward_bound
  aSource : Snapshot 1
  a_source_state : aSource = cadenceAReceiverSource c aPacket
  a_head_queue : aSource.pending = bc.execution.headInputQueue (cadenceAContacts cascadeBackward)
  aRun : LocalCadenceReceiver θ aSource 2 aPacket (7899 / 10)
  weave : CausalHeadWeave bc.execution aRun.execution
    (bc.source.pending.map Delivery.succ) (cadenceAContacts cascadeBackward)
  final : Snapshot 3
  final_state : final = bc.final.prependQueued aRun.final weave.pending
  execution : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) c.wave.cadence.teaching.final final
  execution_eq : HEq execution weave.execution
  date : final.time = 7899 / 10
  pending : final.pending = []
  ready : ∀ i, ReadyCoordinates final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i q, final.raw i q = none
  a_emission_times : execution.emissionTimes 0 = aRun.execution.emissionTimes 0
  b_emission_times : execution.emissionTimes 1 = bc.execution.emissionTimes 0
  c_emission_times : execution.emissionTimes 2 = bc.execution.emissionTimes 1
  a_emission_count : (execution.emissionTimes 0).length = 16
  b_emission_count : (execution.emissionTimes 1).length = 18
  c_emission_count : (execution.emissionTimes 2).length = 20
  a_gain_target : final.x 0 (.z 2) = born.x 0 (.z 2) + 12 / 5
  b_gain_target : final.x 1 (.z 2) = newbornB.x (.z 2) + 12 / 5
  c_gain_target : final.x 2 (.z 0) = newbornC.x (.z 0) + 12 / 5
  a_gain_other : ∀ q, q ≠ 2 → final.x 0 (.z q) = c.wave.cadence.teaching.final.x 0 (.z q)
  b_gain_other : ∀ q, q ≠ 2 → final.x 1 (.z q) = c.wave.cadence.teaching.final.x 1 (.z q)
  c_gain_other : ∀ q, q ≠ 0 → final.x 2 (.z q) = c.wave.cadence.teaching.final.x 2 (.z q)
  a_recovery : final.x 0 .b = born.x 0 .b + 3 / 10
  b_recovery : final.x 1 .b = newbornB.x .b + 3 / 10
  c_recovery : final.x 2 .b = newbornC.x .b + 3 / 10
  physical : PhysicalInvariant (extendParameters (extendParameters θ freshB) freshC) final
  raw_valid : RawValid final
  complete : CompleteThrough execution (7899 / 10)

theorem constructed_cadence_cascade_exists
    {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward ε}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hborn : BirthState born)
    (hforward : ∀ time, (3 / 10 : ℝ) ≤ cascadeForward time ∧ cascadeForward time ≤ 2 / 5)
    (hback : ∀ time, (3 / 10 : ℝ) ≤ cascadeBackward time ∧ cascadeBackward time ≤ 2 / 5) :
    Nonempty (ConstructedCadenceCascade c) := by
  obtain ⟨bc⟩ := constructed_b_cadence_exists c hb hforward
  let packet := bc.receivedBPacket cascadeBackward hback
  let aSource := cadenceAReceiverSource c packet
  have hfA : PhysicalInvariant θ aSource := by
    refine ⟨fun _ => c.wave.cadence.teaching.physical.region 0,?_,?_,?_⟩
    · intro j q
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact c.wave.cadence.teaching.physical.gain_cap 0 q
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact c.wave.cadence.teaching.physical.recovery_cap 0
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact c.wave.cadence.teaching.physical.reserve 0
  have hvA : RawValid aSource := fun _ q origin h => c.wave.cadence.teaching.raw_valid 0 q origin h
  have hsA : PreparedSection aSource 0 :=
    ⟨(c.wave.cadence.teaching.prepared 0).ready,(c.wave.cadence.teaching.prepared 0).charge,
      (c.wave.cadence.teaching.prepared 0).recovery,(c.wave.cadence.teaching.prepared 0).auxiliary⟩
  have hqA : aSource.x 0 .q = 1 / 10 := c.wave.cadence.teaching.charge 0
  have hrA : ∀ q, aSource.raw 0 q = none := c.wave.cadence.teaching.raw_none 0
  have hzA : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ aSource.x 0 (.z 2) ∧
      aSource.x 0 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    change Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤
      c.wave.cadence.teaching.final.x 0 (.z 2) ∧
      c.wave.cadence.teaching.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000
    rw [c.wave.cadence.teaching.a_gain_target]
    have h := ((hborn.2.2 0).2.2.2.2 (2 : Port)).1
    simp only [nominalGain,show (2 : Port) ≠ 1 by decide,ite_false] at h
    constructor <;> linarith [h.1,h.2]
  have hFirst : aSource.time < packet.actual 0 := by
    rw [cadence_a_receiver_source_date]
    exact bc.received_b_first_after_teaching cascadeBackward hback
  have hLast : packet.actual (5 + 13 - 1) + 19 / 5 ≤ (7899 / 10 : ℝ) :=
    bc.received_b_terminal cascadeBackward hback (17 : Fin 18)
  obtain ⟨aRun⟩ := local_cadence_receiver_exists hb.extend_old.extend_old aSource 2 packet (7899 / 10)
    (by norm_num) (by norm_num) hfA hvA hsA hqA hrA hzA rfl hFirst hLast
  have hGate : ∀ time ∈ bc.execution.emissionTimes 0, (640 : ℝ) ≤ time ∧ time < 780 := by
    intro time ht
    rw [bc.output_packet_calendar] at ht
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨(bc.b_packet_dates_in_contact i).1,by linarith [(bc.b_packet_dates_in_contact i).2]⟩
  have hQueue : aSource.pending = bc.execution.headInputQueue (cadenceAContacts cascadeBackward) := by
    rw [cadence_a_head_input_queue bc.execution cascadeBackward hGate]
    change List.ofFn (fun i : Fin 18 => (⟨0,2,packet.actual i.val⟩ : Delivery 1)) = bc.returnTokens cascadeBackward
    exact (bc.return_tokens_received_calendar cascadeBackward hback).symm
  have hStart : bc.source.time = aSource.time :=
    bc.source_date.trans (cadence_a_receiver_source_date c packet).symm
  have hBalance := HeadQueueBalance.initial bc.execution aSource (cadenceAContacts cascadeBackward) hQueue
  obtain ⟨weave⟩ := bc.execution.prepend_causal_result aRun.execution
    hStart (bc.complete.1.trans aRun.complete.1.symm) (cadenceAContacts cascadeBackward)
    (cadence_a_contacts_strict cascadeBackward hback) (bc.source.pending.map Delivery.succ) hBalance
  let Qend := weave.pending
  let global := weave.execution
  have hComplete := weave.complete bc.complete aRun.complete
  let final : Snapshot 3 := bc.final.prependQueued aRun.final Qend
  have hEmpty : Qend = [] := weave.pending_empty bc.pending aRun.pending
  have hSource := cadence_global_source_eq bc packet
  have hParameters := cadence_global_parameters θ freshB freshC
  have hRouter := cadence_global_router_eq cascadeForward cascadeBackward
  let e0 := global.cast_source hSource.symm
  let e1 := e0.cast_parameters hParameters
  let execution : Execution (extendParameters (extendParameters θ freshB) freshC)
      (cadenceRouter cascadeForward cascadeBackward) c.wave.cadence.teaching.final final :=
    cadence_cast_router e1 hRouter
  have hLedger : execution.ledger = global.ledger :=
    (cadence_router_ledger e1 hRouter).trans
      ((e0.cast_parameters_ledger hParameters).trans (global.cast_source_ledger hSource.symm))
  have hTimes (i : Fin 3) : execution.emissionTimes i = global.emissionTimes i := by
    simp only [Execution.emissionTimes,hLedger]
  have hExec : HEq execution global := (cadence_router_heq e1 hRouter).trans
    ((cadence_parameters_heq e0 hParameters).trans (cadence_source_heq global hSource.symm))
  have hComplete1 : CompleteThrough e1 (7899 / 10) := by
    simpa only [CompleteThrough] using hComplete
  have hCompleteFinal : CompleteThrough execution (7899 / 10) :=
    cadence_router_complete e1 hRouter hComplete1
  have hReady : ∀ i, ReadyCoordinates final i := by
    intro i
    fin_cases i
    · exact ⟨(aRun.ready 0).ready,(aRun.ready 0).charge,(aRun.ready 0).auxiliary⟩
    · exact ⟨(bc.ready 0).ready,(bc.ready 0).charge,(bc.ready 0).auxiliary⟩
    · exact ⟨(bc.ready 1).ready,(bc.ready 1).charge,(bc.ready 1).auxiliary⟩
  have hCharge : ∀ i, final.x i .q = 1 / 10 := by
    intro i
    fin_cases i
    · exact aRun.charge
    · exact bc.charge 0
    · exact bc.charge 1
  have hRaw : ∀ i q, final.raw i q = none := by
    intro i q
    fin_cases i
    · exact aRun.raw_none 0 q
    · exact bc.raw_none 0 q
    · exact bc.raw_none 1 q
  have hATimes : execution.emissionTimes 0 = aRun.execution.emissionTimes 0 :=
    (hTimes 0).trans weave.head_emission_times
  have hBTimes : execution.emissionTimes 1 = bc.execution.emissionTimes 0 :=
    (hTimes 1).trans (weave.tail_emission_times 0)
  have hCTimes : execution.emissionTimes 2 = bc.execution.emissionTimes 1 :=
    (hTimes 2).trans (weave.tail_emission_times 1)
  have hAGain : final.x 0 (.z 2) = born.x 0 (.z 2) + 12 / 5 := by
    change aRun.final.x 0 (.z 2) = _
    rw [aRun.gain_target]
    change c.wave.cadence.teaching.final.x 0 (.z 2) + 3 / 5 = _
    rw [c.wave.cadence.teaching.a_gain_target]
    ring
  have hARecovery : final.x 0 .b = born.x 0 .b + 3 / 10 := by
    change aRun.final.x 0 .b = _
    rw [aRun.recovery_gain]
    change c.wave.cadence.teaching.final.x 0 .b + 1 / 5 = _
    rw [c.wave.cadence.teaching.a_recovery]
    ring
  refine ⟨{
    backward_bound := hback, bc := bc, aPacket := packet, a_packet_eq := rfl
    aSource := aSource, a_source_state := rfl, a_head_queue := hQueue, aRun := aRun, weave := weave
    final := final, final_state := rfl, execution := execution, execution_eq := hExec
    date := bc.date, pending := hEmpty, ready := hReady, charge := hCharge, raw_none := hRaw
    a_emission_times := hATimes, b_emission_times := hBTimes, c_emission_times := hCTimes
    a_emission_count := (congrArg List.length hATimes).trans aRun.emission_count
    b_emission_count := (congrArg List.length hBTimes).trans bc.b_emission_count
    c_emission_count := (congrArg List.length hCTimes).trans bc.c_emission_count
    a_gain_target := hAGain, b_gain_target := bc.b_gain_target, c_gain_target := bc.c_gain_target
    a_gain_other := ?_, b_gain_other := bc.b_gain_other, c_gain_other := bc.c_gain_other
    a_recovery := hARecovery, b_recovery := bc.b_recovery, c_recovery := bc.c_recovery
    physical := execution.physical_invariant hb c.wave.cadence.teaching.physical
    raw_valid := execution.raw_valid c.wave.cadence.teaching.raw_valid, complete := hCompleteFinal
  }⟩
  intro q hq
  change aRun.final.x 0 (.z q) = _
  rw [aRun.gain_other q hq]
  rfl

end KernelR.Hybrid
