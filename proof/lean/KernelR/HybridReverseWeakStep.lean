import KernelR.HybridReverseSourceWire
import KernelR.HybridPortWeakCut

/-! From a real reverse-wire receipt, construct the receiving weak response,
weave it with the sender's actual retained return, and consume the next
external B source at source+8. The receiver keeps its true carried charge. -/
namespace KernelR.Hybrid

namespace ReverseSourceWire
variable {θA θB forward backward source cycle}
  (r : ReverseSourceWire θA θB forward backward source cycle)

noncomputable def receiverLocal : Snapshot 1 := r.final.cellProjection 0 []

theorem receiver_local_physical : PhysicalInvariant θA r.receiverLocal := by
  refine ⟨fun _ => r.physical.region 0,?_,fun _ => r.physical.recovery_cap 0,
    fun _ => r.physical.reserve 0⟩
  intro j q
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact r.physical.gain_cap 0 q

theorem receiver_local_raw_valid : RawValid r.receiverLocal :=
  fun _ q origin h => r.raw_valid 0 q origin h

theorem product_receiver_projection :
    r.receiverLocal.product r.cutH.state source.pending = r.final := by
  have extensionality {n} (s u : Snapshot n) (ht : s.time = u.time) (hx : s.x = u.x)
      (hm : s.main = u.main) (ha : s.aux = u.aux) (hr : s.raw = u.raw) (hp : s.pending = u.pending) : s = u := by
    cases s
    cases u
    simp_all only
  apply extensionality
  · rfl
  · funext i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · rfl
    · exact r.b_values.symm
  · funext i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · rfl
    · exact r.b_main.symm
  · funext i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · rfl
    · funext q; exact (r.b_aux q).symm
  · funext i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · rfl
    · funext q; exact (r.b_raw q).symm
  · exact r.pending.symm

end ReverseSourceWire

structure ReverseWeakStep {θA θB forward backward source cycle}
    (r : ReverseSourceWire θA θB forward backward source cycle) (later : List (Delivery 2)) where
  receiver : PortWeakCut θA r.receiverLocal 2 (source.time + 8)
  senderFinal : Snapshot 1
  senderExecution : Execution θB (fun _ _ => []) r.cutH.state senderFinal
  sender_date : senderFinal.time = source.time + 8
  sender_pending : senderFinal.pending = []
  sender_emissions : senderExecution.ledger.emissions = []
  sender_deliveries : senderExecution.deliveries = []
  final : Snapshot 2
  execution : Execution (extendParameters θA (θB 0)) (reciprocalEntryRouter forward backward) r.final final
  date : final.time = source.time + 8
  b_prepared : PreparedSection final 1
  b_charge : final.x 1 .q = 1 / 10
  b_gains : ∀ q, final.x 1 (.z q) = r.final.x 1 (.z q)
  a_values : final.x 0 = receiver.cut.state.x 0
  a_main : final.main 0 = receiver.cut.state.main 0
  a_aux : ∀ q, final.aux 0 q = receiver.cut.state.aux 0 q
  a_raw : ∀ q, final.raw 0 q = receiver.cut.state.raw 0 q
  raw_active : final.raw 1 2 = some (source.time + 8)
  raw_other_b : ∀ q, q ≠ 2 → final.raw 1 q = none
  pending : final.pending = later
  a_gain_target : final.x 0 (.z 2) = r.final.x 0 (.z 2) + 3 / 5
  a_gain_other : ∀ q, q ≠ 2 → final.x 0 (.z q) = r.final.x 0 (.z q)
  recovery : ∀ i, final.x i .b = r.final.x i .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨1,2,source.time + 8⟩]
  physical : PhysicalInvariant (extendParameters θA (θB 0)) final
  raw_valid : RawValid final
  complete : CompleteThrough execution (source.time + 8)

/-- The prepared receiving section is derived by the caller from its earlier
actual weak continuation. This constructor supplies every new local flow,
cut, global interleaving and next source arrival. -/
theorem reverse_weak_step_exists {θA θB ε forward backward source cycle}
    (r : ReverseSourceWire θA θB forward backward source cycle)
    (hb : PhysicalBox (extendParameters θA (θB 0)) ε)
    (hs : PreparedSection r.final 0) (hq : 1 / 10 ≤ r.final.x 0 .q)
    (hz : r.final.x 0 (.z 2) ≤ Real.log (6 / 5) + 1 / 1000)
    (hg : Real.exp (r.final.x 0 (.z 2)) ≤ 7 / 6)
    (later : List (Delivery 2))
    (hqueue : source.pending = ⟨1,2,source.time + 8⟩ :: later)
    (hlater : ∀ d ∈ later, source.time + 8 < d.due) :
    Nonempty (ReverseWeakStep r later) := by
  have hbB : PhysicalBox θB ε := by
    refine ⟨hb.1,?_⟩
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hb.2 1 q
  have hA : PreparedSection r.receiverLocal 0 := ⟨hs.ready,hs.charge,hs.recovery,hs.auxiliary⟩
  obtain ⟨receiver⟩ := port_weak_cut_exists hb.extend_old r.receiverLocal 2
    r.receiver_local_physical r.receiver_local_raw_valid hA hq r.raw_active r.raw_other_a hz hg rfl
    (source.time + 8)
    (by change r.final.time + 419 / 300 ≤ source.time + 8; linarith [r.window.2])
    (by change source.time + 8 < r.final.time + 15 / 2; linarith [r.window.1])
  have hpendingB : cycle.returned.final.pending = [] := cycle.pending
  have hwait : cycle.returned.final.time < source.time + 8 := by rw [cycle.date]; norm_num [reverseSourceLocalB,Snapshot.cellProjection]
  let waitFlow : Flow θB cycle.returned.final (quietAt cycle.returned.final (source.time + 8)) :=
    quietFlow cycle.returned.final hwait (fun j => (cycle.ready j).ready)
      (fun j q => ((cycle.ready j).auxiliary q).1) cycle.raw_none
      (fun j => by linarith [(cycle.ready j).charge.2])
      (fun j q => by linarith [((cycle.ready j).auxiliary q).2.2])
      (by intro d hd; rw [hpendingB] at hd; contradiction)
  let wait : Execution θB (fun _ _ => []) cycle.returned.final (quietAt cycle.returned.final (source.time + 8)) :=
    .cons (.flow waitFlow) (.nil _)
  let senderFinal := quietAt cycle.returned.final (source.time + 8)
  let fastTail : Execution θB (fun _ _ => []) r.cutH.state cycle.fast.final :=
    .cons (.flow r.cutH.flow) r.cutH.rest
  let senderExecution := fastTail.append (cycle.returned.execution.append wait)
  have heFast : fastTail.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (r.cutH.emissions.symm.trans cycle.fast.emissions)).2
  have hdFast : fastTail.deliveries = [] :=
    (List.append_eq_nil_iff.mp (r.cutH.deliveries.symm.trans cycle.fast.deliveries)).2
  have heB : senderExecution.ledger.emissions = [] := by
    change (fastTail.append (cycle.returned.execution.append wait)).ledger.emissions = []
    rw [Execution.emissions_append fastTail (cycle.returned.execution.append wait),heFast,
      Execution.emissions_append cycle.returned.execution wait,cycle.returned.emissions]
    rfl
  have hdB : senderExecution.deliveries = [] := by
    change (fastTail.append (cycle.returned.execution.append wait)).deliveries = []
    rw [Execution.deliveries_append fastTail (cycle.returned.execution.append wait),hdFast,
      Execution.deliveries_append cycle.returned.execution wait,cycle.returned.deliveries]
    rfl
  have hBready : ∀ j, ReadyCoordinates senderFinal j :=
    fun j => quietAt_ready_coordinates cycle.returned.final j (cycle.ready j) hwait.le
  have hBprepared : PreparedSection senderFinal 0 :=
    ⟨(hBready 0).ready,(hBready 0).charge,(cycle.prepared 0).recovery,(hBready 0).auxiliary⟩
  have hBcharge : senderFinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (cycle.returned.final.x 0 .q) cycle.returned.final.time (source.time + 8) = _
    rw [cycle.charge]
    simp [relax]
  have hBgain : ∀ q, senderFinal.x 0 (.z q) = r.final.x 1 (.z q) := by
    intro q
    change cycle.returned.final.x 0 (.z q) = _
    rw [cycle.gains,r.gains]
    rfl
  have hBrec : senderFinal.x 0 .b = r.final.x 1 .b := by
    change cycle.returned.final.x 0 .b = _
    rw [cycle.recovery,r.recovery]
    rfl
  have hstart : r.receiverLocal.time = r.cutH.state.time := r.date.trans r.cutH.date.symm
  have hfinish : receiver.cut.state.time = senderFinal.time := receiver.cut.date
  have hQ : ∀ d ∈ source.pending, receiver.cut.state.time ≤ d.due := by
    intro d hd
    rw [receiver.cut.date,hqueue] at *
    rcases List.mem_cons.mp hd with rfl | hd
    · exact le_rfl
    · exact (hlater d hd).le
  obtain ⟨woven,heW,hdW⟩ := receiver.cut.cut.product_neutral senderExecution hstart hfinish
    receiver.cut_emissions receiver.cut_deliveries heB hdB source.pending hQ
    (reciprocalEntryRouter forward backward)
  let span := woven.cast_source r.product_receiver_projection.symm
  have heSpan : span.ledger.emissions = [] := by rw [Execution.cast_source_ledger]; exact heW
  have hdSpan : span.deliveries = [] := by rw [Execution.cast_source_deliveries]; exact hdW
  let before := receiver.cut.state.product senderFinal source.pending
  let final : Snapshot 2 := {(setRaw before 1 2 (some before.time)) with pending := [] ++ later}
  have hqueueBefore : before.pending = [] ++ (⟨1,2,source.time + 8⟩ : Delivery 2) :: later := hqueue
  have hfree : before.raw 1 2 = none := cycle.raw_none 0 2
  let arrival : Jump (reciprocalEntryRouter forward backward) before final :=
    .arrive before ⟨1,2,source.time + 8⟩ [] later hqueueBefore receiver.cut.date.symm hfree
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨1,2,source.time + 8⟩] := rfl
  let trace := span.append (.cons (.jump arrival) (.nil _))
  have hrawB : final.raw 1 2 = some (source.time + 8) := by
    simp [final,setRaw,before,Snapshot.product,receiver.cut.date]
  have hrawOther : ∀ q, q ≠ 2 → final.raw 1 q = none := by
    intro q hq
    have h : before.raw 1 q = none := cycle.raw_none 0 q
    simpa [final,setRaw,Function.update_apply,hq] using h
  have hrawA : ∀ q, final.raw 0 q = receiver.cut.state.raw 0 q := by
    intro q
    have h : before.raw 0 q = receiver.cut.state.raw 0 q := rfl
    simpa [final,setRaw,Function.update_apply] using h
  have hfuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    change d ∈ [] ++ later at hd
    simp only [List.nil_append] at hd
    change receiver.cut.state.time < d.due
    rw [receiver.cut.date]
    exact hlater d hd
  have hcomplete : CompleteThrough trace (source.time + 8) := by
    refine ⟨receiver.cut.date,?_,?_⟩
    · intro u
      apply BeforeGuards.no_jump
      · constructor
        · intro i
          rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
          · have hm : final.main 0 = receiver.cut.state.main 0 := rfl
            have hx : final.x 0 = receiver.cut.state.x 0 := rfl
            rw [hm,hx]; exact receiver.cut.before_guards.1 0
          · have hm : final.main 1 = .ready := hBprepared.ready
            have hx : final.x 1 .q = 1 / 10 := hBcharge
            rw [hm,hx]; norm_num
        · intro i q
          rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
          · have hm : final.aux 0 q = receiver.cut.state.aux 0 q := rfl
            have hx : final.x 0 = receiver.cut.state.x 0 := rfl
            rw [hm,hx]; exact receiver.cut.before_guards.2 0 q
          · have hm : final.aux 1 q = .ready := (hBprepared.auxiliary q).1
            have hx : RestBand (final.x 1 (.m q)) := (hBprepared.auxiliary q).2
            rw [hm]; linarith [hx.2]
      · intro i q origin hr
        rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
        · rw [hrawA] at hr
          have h := receiver.cut.raw_strict 0 q origin hr
          change receiver.cut.state.time < origin + 1
          rwa [receiver.cut.date]
        · by_cases hq : q = 2
          · subst q
            have ho : origin = source.time + 8 := Option.some.inj (hr.symm.trans hrawB)
            change receiver.cut.state.time < origin + 1
            rw [receiver.cut.date,ho]; linarith
          · rw [hrawOther q hq] at hr; contradiction
      · exact hfuture
    · intro d hd
      have h := hfuture d hd
      change receiver.cut.state.time < d.due at h
      rwa [receiver.cut.date] at h
  refine ⟨{
    receiver := receiver, senderFinal := senderFinal, senderExecution := senderExecution
    sender_date := rfl, sender_pending := hpendingB, sender_emissions := heB, sender_deliveries := hdB
    final := final, execution := trace, date := receiver.cut.date
    b_prepared := ⟨hBprepared.ready,hBprepared.charge,hBprepared.recovery,hBprepared.auxiliary⟩
    b_charge := hBcharge, b_gains := hBgain
    a_values := rfl, a_main := rfl, a_aux := fun _ => rfl, a_raw := hrawA
    raw_active := hrawB, raw_other_b := hrawOther, pending := rfl
    a_gain_target := receiver.cut_gain_target, a_gain_other := receiver.cut_gain_other
    recovery := ?_, emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb r.physical
    raw_valid := trace.raw_valid r.raw_valid, complete := hcomplete
  }⟩
  · intro i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact receiver.cut_recovery
    · exact hBrec
  · simp only [trace,Execution.emissions_append,heSpan,Execution.ledger,Move.ledger,haEm,
      Ledger.add,Ledger.zero,List.append_nil]
  · simp only [trace,Execution.deliveries_append,hdSpan,Execution.deliveries,Move.deliveries,haDel,
      List.nil_append,List.append_nil]

namespace ReverseWeakStep
variable {θA θB forward backward source cycle}
  {r : ReverseSourceWire θA θB forward backward source cycle} {later} (s : ReverseWeakStep r later)

/-- The next global source contains the exact receiver cut, including its
clock and empty local queue. This is an equality, not a new initial section. -/
theorem a_local : reverseSourceLocalA s.final = s.receiver.cut.state := by
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
    exact s.a_values
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.a_main
  · funext j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.a_aux q
  · funext j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact s.a_raw q
  · exact s.receiver.cut_pending.symm

theorem b_local_time : (reverseSourceLocalB s.final).time = source.time + 8 := s.date

theorem b_local_prepared : PreparedSection (reverseSourceLocalB s.final) 0 :=
  ⟨s.b_prepared.ready,s.b_prepared.charge,s.b_prepared.recovery,s.b_prepared.auxiliary⟩

theorem b_local_charge : (reverseSourceLocalB s.final).x 0 .q = 1 / 10 := s.b_charge

theorem b_local_raw_active : (reverseSourceLocalB s.final).raw 0 2 =
    some (reverseSourceLocalB s.final).time := by rw [s.b_local_time]; exact s.raw_active

theorem b_local_raw_other (q : Port) (hq : q ≠ 2) :
    (reverseSourceLocalB s.final).raw 0 q = none := s.raw_other_b q hq

theorem a_main_ready : s.final.main 0 = .ready := s.a_main.trans s.receiver.cut_main_ready

theorem a_charge_lower : 1 / 10 ≤ s.final.x 0 .q := by rw [s.a_values]; exact s.receiver.cut_charge_lower

theorem a_aux_rest (q : Port) : s.final.aux 0 q = .ready ∧ RestBand (s.final.x 0 (.m q)) := by
  rw [s.a_aux,s.a_values]
  exact s.receiver.cut_aux_rest q

theorem a_raw_none (q : Port) : s.final.raw 0 q = none := by rw [s.a_raw]; exact s.receiver.cut_raw_none q

theorem a_error_dose : s.execution.ledger.error 0 2 = 3 / 5 := by
  have h := s.execution.gain_balance 0 2
  rw [s.a_gain_target] at h
  linarith

theorem error_other (i : Fin 2) (q : Port) (h : i ≠ 0 ∨ q ≠ 2) :
    s.execution.ledger.error i q = 0 := by
  have hb := s.execution.gain_balance i q
  rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
  · rw [s.a_gain_other q (by simpa using h)] at hb
    linarith
  · rw [s.b_gains] at hb
    linarith

theorem recovery_zero (i : Fin 2) : s.execution.ledger.recovery i = 0 := by
  have h := s.execution.recovery_balance i
  rw [s.recovery] at h
  linarith

end ReverseWeakStep
end KernelR.Hybrid
