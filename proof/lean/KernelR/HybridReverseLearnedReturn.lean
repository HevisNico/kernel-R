import KernelR.HybridReverseSourceWire
import KernelR.HybridIntervalClosedExecutionProduct

/-! A prepared learned A response after a real reverse receipt, followed by
both physical returns and the actual next external B occurrence. -/
namespace KernelR.Hybrid

namespace ReverseSourceWire
variable {θA θB forward backward source cycle}
  (r : ReverseSourceWire θA θB forward backward source cycle)

noncomputable def learnedReceiver : Snapshot 1 := r.final.cellProjection 0 []

theorem learned_receiver_physical : PhysicalInvariant θA r.learnedReceiver := by
  refine ⟨fun _ => r.physical.region 0,?_,fun _ => r.physical.recovery_cap 0,
    fun _ => r.physical.reserve 0⟩
  intro j q
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact r.physical.gain_cap 0 q

theorem learned_receiver_raw_valid : RawValid r.learnedReceiver :=
  fun _ q origin h => r.raw_valid 0 q origin h

theorem learned_receiver_product :
    r.learnedReceiver.product r.cutH.state source.pending = r.final := by
  have extensionality {n} (s u : Snapshot n)
      (ht : s.time = u.time) (hx : s.x = u.x) (hm : s.main = u.main)
      (ha : s.aux = u.aux) (hr : s.raw = u.raw) (hp : s.pending = u.pending) : s = u := by
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
    · funext q; exact (r.b_aux q).symm
  · funext i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · rfl
    · funext q; exact (r.b_raw q).symm
  · exact r.pending.symm

end ReverseSourceWire

structure ReverseLearnedReturn {θA θB forward backward source cycle}
    (r : ReverseSourceWire θA θB forward backward source cycle) where
  receiver : ShortLearnedCycle θA r.learnedReceiver 2
  receiverFinal : Snapshot 1
  receiverWait : Execution θA (fun _ _ => []) receiver.returned.final receiverFinal
  receiver_final_eq : receiverFinal = quietAt receiver.returned.final (source.time + 8)
  senderFinal : Snapshot 1
  senderWait : Execution θB (fun _ _ => []) cycle.returned.final senderFinal
  sender_final_eq : senderFinal = quietAt cycle.returned.final (source.time + 8)
  senderPath : Execution θB (fun _ _ => []) r.cutH.state senderFinal
  sender_reconstruct : senderPath =
    (Execution.cons (.flow r.cutH.flow) r.cutH.rest).append (cycle.returned.execution.append senderWait)
  final : Snapshot 2
  execution : Execution (extendParameters θA (θB 0)) (reciprocalEntryRouter forward backward) r.final final
  final_product : final = receiverFinal.product senderFinal source.pending
  date : final.time = source.time + 8
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i q, final.raw i q = none
  pending : final.pending = source.pending
  gains : ∀ i q, final.x i (.z q) = r.final.x i (.z q)
  recovery : ∀ i, final.x i .b = r.final.x i .b
  emissions : execution.ledger.emissions = [(0,receiver.fire.final.time)]
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant (extendParameters θA (θB 0)) final
  raw_valid : RawValid final

/-- Preparation and learned gain at the actual receipt are supplied by the
caller from its preceding weak trajectory. Every subsequent event is built. -/
theorem reverse_learned_return_exists {θA θB ε forward backward source cycle}
    (r : ReverseSourceWire θA θB forward backward source cycle)
    (hb : PhysicalBox (extendParameters θA (θB 0)) ε)
    (hsource : 320 ≤ source.time)
    (hprepared : PreparedSection r.final 0)
    (hgain : 9 / 5 ≤ Real.exp (r.final.x 0 (.z 2)) ∧ Real.exp (r.final.x 0 (.z 2)) ≤ 11 / 5)
    (hQ : ∀ d ∈ source.pending, source.time + 8 ≤ d.due) :
    Nonempty (ReverseLearnedReturn r) := by
  have hbA : PhysicalBox θA ε := hb.extend_old
  have hA : PreparedSection r.learnedReceiver 0 :=
    ⟨hprepared.ready,hprepared.charge,hprepared.recovery,hprepared.auxiliary⟩
  have hRaw : r.learnedReceiver.raw 0 2 = some r.learnedReceiver.time := r.raw_active
  have hOther : ∀ q, q ≠ 2 → r.learnedReceiver.raw 0 q = none := r.raw_other_a
  obtain ⟨a⟩ := short_learned_cycle_exists hbA r.learnedReceiver 2 r.learned_receiver_physical
    r.learned_receiver_raw_valid hA hgain hRaw hOther
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  have hAend : a.returned.final.time < source.time + 8 := by
    rw [a.date]
    change r.final.time + 69 / 10 < source.time + 8
    linarith [r.window.2]
  have hBend : cycle.returned.final.time < source.time + 8 := by
    rw [cycle.date]
    change source.time + 69 / 10 < source.time + 8
    linarith
  have hApending : a.returned.final.pending = [] := a.pending
  have hBpending : cycle.returned.final.pending = [] := cycle.pending
  let aWaitFlow : Flow θA a.returned.final (quietAt a.returned.final (source.time + 8)) :=
    quietFlow a.returned.final hAend (fun j => (a.ready j).ready)
      (fun j q => ((a.ready j).auxiliary q).1) a.raw_none
      (fun j => by linarith [(a.ready j).charge.2])
      (fun j q => by linarith [((a.ready j).auxiliary q).2.2])
      (by intro d hd; rw [hApending] at hd; contradiction)
  let bWaitFlow : Flow θB cycle.returned.final (quietAt cycle.returned.final (source.time + 8)) :=
    quietFlow cycle.returned.final hBend (fun j => (cycle.ready j).ready)
      (fun j q => ((cycle.ready j).auxiliary q).1) cycle.raw_none
      (fun j => by linarith [(cycle.ready j).charge.2])
      (fun j q => by linarith [((cycle.ready j).auxiliary q).2.2])
      (by intro d hd; rw [hBpending] at hd; contradiction)
  let aWait : Execution θA (fun _ _ => []) a.returned.final (quietAt a.returned.final (source.time + 8)) :=
    .cons (.flow aWaitFlow) (.nil _)
  let bWait : Execution θB (fun _ _ => []) cycle.returned.final (quietAt cycle.returned.final (source.time + 8)) :=
    .cons (.flow bWaitFlow) (.nil _)
  let afinal := quietAt a.returned.final (source.time + 8)
  let bfinal := quietAt cycle.returned.final (source.time + 8)
  let ae := a.execution.append aWait
  let bTail : Execution θB (fun _ _ => []) r.cutH.state cycle.fast.final :=
    .cons (.flow r.cutH.flow) r.cutH.rest
  have heBTail : bTail.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (r.cutH.emissions.symm.trans cycle.fast.emissions)).2
  have hdBTail : bTail.deliveries = [] :=
    (List.append_eq_nil_iff.mp (r.cutH.deliveries.symm.trans cycle.fast.deliveries)).2
  let be := bTail.append (cycle.returned.execution.append bWait)
  have heA : ae.ledger.emissions = [(0,a.fire.final.time)] := by
    rw [Execution.emissions_append,a.emissions]
    rfl
  have hdA : ae.deliveries = [] := by rw [Execution.deliveries_append,a.deliveries]; rfl
  have heB : be.ledger.emissions = [] := by
    rw [Execution.emissions_append,heBTail,Execution.emissions_append,cycle.returned.emissions]
    rfl
  have hdB : be.deliveries = [] := by
    rw [Execution.deliveries_append,hdBTail,Execution.deliveries_append,cycle.returned.deliveries]
    rfl
  have hclock : r.learnedReceiver.time = r.cutH.state.time := r.date.trans r.cutH.date.symm
  have hclosed : ∀ t, r.learnedReceiver.time ≤ t → t ≤ afinal.time →
      reciprocalEntryRouter forward backward 0 t = [] := by
    intro t hlo _
    have ht : (310 : ℝ) ≤ t := by
      change r.final.time ≤ t at hlo
      linarith [r.window.1]
    classical
    have hn : ¬ t < (310 : ℝ) := by linarith
    simp [reciprocalEntryRouter,Contact.route,teachingContact,feedbackContact,hn]
  obtain ⟨woven,heW,hdW⟩ := ae.product_left_closed_on be hclock rfl hdA heB hdB source.pending hQ
    (reciprocalEntryRouter forward backward) hclosed
  let final := afinal.product bfinal source.pending
  let e : Execution (extendParameters θA (θB 0)) (reciprocalEntryRouter forward backward) r.final final :=
    woven.cast_source r.learned_receiver_product.symm
  have heE : e.ledger.emissions = [(0,a.fire.final.time)] := by
    have h := (congrArg (fun L : Ledger 2 => L.emissions)
      (woven.cast_source_ledger r.learned_receiver_product.symm)).trans heW
    rw [heA] at h
    exact h
  have hdE : e.deliveries = [] := (woven.cast_source_deliveries r.learned_receiver_product.symm).trans hdW
  have hAr : ∀ j, ReadyCoordinates afinal j :=
    fun j => quietAt_ready_coordinates a.returned.final j (a.ready j) hAend.le
  have hBr : ∀ j, ReadyCoordinates bfinal j :=
    fun j => quietAt_ready_coordinates cycle.returned.final j (cycle.ready j) hBend.le
  have hAq : afinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (a.returned.final.x 0 .q) a.returned.final.time (source.time + 8) = _
    rw [a.charge]
    simp [relax]
  have hBq : bfinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (cycle.returned.final.x 0 .q) cycle.returned.final.time (source.time + 8) = _
    rw [cycle.charge]
    simp [relax]
  refine ⟨{
    receiver := a, receiverFinal := afinal, receiverWait := aWait, receiver_final_eq := rfl
    senderFinal := bfinal, senderWait := bWait, sender_final_eq := rfl
    senderPath := be, sender_reconstruct := rfl
    final := final, execution := e, final_product := rfl, date := rfl
    prepared := ?_, charge := ?_, raw_none := ?_, pending := rfl, gains := ?_, recovery := ?_
    emissions := heE, deliveries := hdE, physical := e.physical_invariant hb r.physical
    raw_valid := e.raw_valid r.raw_valid
  }⟩
  · intro i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · exact ⟨(hAr 0).ready,(hAr 0).charge,(a.prepared 0).recovery,(hAr 0).auxiliary⟩
    · exact ⟨(hBr 0).ready,(hBr 0).charge,(cycle.prepared 0).recovery,(hBr 0).auxiliary⟩
  · intro i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · exact hAq
    · exact hBq
  · intro i q
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · exact a.raw_none 0 q
    · exact cycle.raw_none 0 q
  · intro i q
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · exact a.gains 0 q
    · change cycle.returned.final.x 0 (.z q) = r.final.x 1 (.z q)
      exact (cycle.gains 0 q).trans (r.gains 1 q).symm
  · intro i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> subst i
    · exact a.recovery 0
    · change cycle.returned.final.x 0 .b = r.final.x 1 .b
      exact (cycle.recovery 0).trans (r.recovery 1).symm

namespace ReverseLearnedReturn
variable {θA θB forward backward source cycle}
  {r : ReverseSourceWire θA θB forward backward source cycle} (u : ReverseLearnedReturn r)

theorem error_zero (i : Fin 2) (q : Port) : u.execution.ledger.error i q = 0 := by
  have h := u.execution.gain_balance i q
  rw [u.gains] at h
  linarith

theorem recovery_zero (i : Fin 2) : u.execution.ledger.recovery i = 0 := by
  have h := u.execution.recovery_balance i
  rw [u.recovery] at h
  linarith

theorem complete (hstrict : ∀ d ∈ source.pending, source.time + 8 < d.due) :
    CompleteThrough u.execution (source.time + 8) := by
  have hfuture : ∀ d ∈ u.final.pending, u.final.time < d.due := by
    intro d hd
    rw [u.pending] at hd
    rw [u.date]
    exact hstrict d hd
  refine ⟨u.date,?_,?_⟩
  · intro v
    apply BeforeGuards.no_jump
    · constructor
      · intro i
        rw [(u.prepared i).ready,u.charge i]
        norm_num
      · intro i q
        rw [((u.prepared i).auxiliary q).1]
        linarith [((u.prepared i).auxiliary q).2.2]
    · intro i q origin hr
      rw [u.raw_none i q] at hr
      contradiction
    · exact hfuture
  · intro d hd
    rw [u.pending] at hd
    exact hstrict d hd

end ReverseLearnedReturn

structure ReverseLearnedNextSource {θA θB forward backward source cycle}
    (r : ReverseSourceWire θA θB forward backward source cycle) (later : List (Delivery 2)) where
  returned : ReverseLearnedReturn r
  final : Snapshot 2
  execution : Execution (extendParameters θA (θB 0)) (reciprocalEntryRouter forward backward) r.final final
  date : final.time = source.time + 8
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_active : final.raw 1 2 = some final.time
  raw_other : ∀ i q, i ≠ 1 ∨ q ≠ 2 → final.raw i q = none
  pending : final.pending = later
  gains : ∀ i q, final.x i (.z q) = r.final.x i (.z q)
  recovery : ∀ i, final.x i .b = r.final.x i .b
  emissions : execution.ledger.emissions = [(0,returned.receiver.fire.final.time)]
  deliveries : execution.deliveries = [⟨1,2,source.time + 8⟩]
  physical : PhysicalInvariant (extendParameters θA (θB 0)) final
  raw_valid : RawValid final

/-- Deliver the actual head occurrence only after both real learned paths
return to the common source boundary. The due occurrence prevents earlier saturation. -/
theorem reverse_learned_next_source_exists {θA θB ε forward backward source cycle}
    (r : ReverseSourceWire θA θB forward backward source cycle)
    (hb : PhysicalBox (extendParameters θA (θB 0)) ε)
    (hsource : 320 ≤ source.time) (hprepared : PreparedSection r.final 0)
    (hgain : 9 / 5 ≤ Real.exp (r.final.x 0 (.z 2)) ∧ Real.exp (r.final.x 0 (.z 2)) ≤ 11 / 5)
    (later : List (Delivery 2))
    (hq : source.pending = ⟨1,2,source.time + 8⟩ :: later)
    (hlater : ∀ d ∈ later, source.time + 8 ≤ d.due) :
    Nonempty (ReverseLearnedNextSource r later) := by
  have hQ : ∀ d ∈ source.pending, source.time + 8 ≤ d.due := by
    intro d hd
    rw [hq] at hd
    rcases List.mem_cons.mp hd with hd | hd
    · subst d; exact le_rfl
    · exact hlater d hd
  obtain ⟨u⟩ := reverse_learned_return_exists r hb hsource hprepared hgain hQ
  let d : Delivery 2 := ⟨1,2,source.time + 8⟩
  let final : Snapshot 2 := {(setRaw u.final 1 2 (some u.final.time)) with pending := [] ++ later}
  have hpending : u.final.pending = [] ++ d :: later := by rw [u.pending,hq]; rfl
  let arrival : Jump (reciprocalEntryRouter forward backward) u.final final :=
    .arrive u.final d [] later hpending u.date.symm (u.raw_none 1 2)
  let e := u.execution.append (.cons (.jump arrival) (.nil _))
  refine ⟨{
    returned := u, final := final, execution := e, date := u.date
    prepared := fun i => ⟨(u.prepared i).ready,(u.prepared i).charge,
      (u.prepared i).recovery,(u.prepared i).auxiliary⟩
    charge := u.charge, raw_active := ?_, raw_other := ?_, pending := rfl
    gains := u.gains, recovery := u.recovery, emissions := ?_, deliveries := ?_
    physical := e.physical_invariant hb r.physical, raw_valid := e.raw_valid r.raw_valid
  }⟩
  · simp [final,setRaw]
  · intro i q h
    change (setRaw u.final 1 2 (some u.final.time)).raw i q = none
    rw [raw_update_other _ _ _ _ _ _ h]
    exact u.raw_none i q
  · have he : arrival.ledger.emissions = [] := rfl
    simp only [e,Execution.emissions_append,u.emissions,Execution.ledger,Move.ledger,he,
      Ledger.add,Ledger.zero,List.append_nil]
  · have hd : arrival.deliveries = [d] := rfl
    simp only [e,Execution.deliveries_append,u.deliveries,Execution.deliveries,Move.deliveries,hd,
      List.nil_append,List.append_nil]
    rfl

namespace ReverseLearnedNextSource
variable {θA θB forward backward source cycle}
  {r : ReverseSourceWire θA θB forward backward source cycle} {later : List (Delivery 2)}
  (u : ReverseLearnedNextSource r later)

theorem complete (hstrict : ∀ d ∈ later, source.time + 8 < d.due) :
    CompleteThrough u.execution (source.time + 8) := by
  have hfuture : ∀ d ∈ u.final.pending, u.final.time < d.due := by
    intro d hd
    rw [u.pending] at hd
    rw [u.date]
    exact hstrict d hd
  refine ⟨u.date,?_,?_⟩
  · intro v
    apply BeforeGuards.no_jump
    · constructor
      · intro i
        rw [(u.prepared i).ready,u.charge i]
        norm_num
      · intro i q
        rw [((u.prepared i).auxiliary q).1]
        linarith [((u.prepared i).auxiliary q).2.2]
    · intro i q origin hr
      by_cases h : i = 1 ∧ q = 2
      · obtain ⟨rfl,rfl⟩ := h
        have he : origin = u.final.time := Option.some.inj (hr.symm.trans u.raw_active)
        rw [he]
        linarith
      · rw [u.raw_other i q (by tauto)] at hr
        contradiction
    · exact hfuture
  · intro d hd
    rw [u.pending] at hd
    exact hstrict d hd

end ReverseLearnedNextSource
end KernelR.Hybrid
