import KernelR.HybridQuietExecutionProduct

namespace KernelR.Hybrid

structure QuietWireArrival (θA θB : Fin 1 → Parameters) (route : Router 2)
    (sA sB uA : Snapshot 1) (Q : List (Delivery 2)) (p : Port) where
  final : Snapshot 2
  execution : Execution (extendParameters θA (θB 0)) route
    (sA.product sB (Q ++ [⟨1,p,uA.time⟩])) final
  date : final.time = uA.time
  pending : final.pending = Q
  sender_values : final.x 0 = uA.x 0
  receiver_values : final.x 1 = (quietAt sB uA.time).x 0
  sender_main : final.main 0 = uA.main 0
  sender_aux : ∀ q, final.aux 0 q = uA.aux 0 q
  receiver_ready : ReadyCoordinates final 1
  sender_raw : ∀ q, final.raw 0 q = uA.raw 0 q
  raw_active : final.raw 1 p = some uA.time
  raw_other : ∀ q, q ≠ p → final.raw 1 q = none
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨1,p,uA.time⟩]
  physical : PhysicalInvariant (extendParameters θA (θB 0)) final
  raw_valid : RawValid final

/-- An already-issued wire token is consumed at its real date. The local
sender continuation is transported with the receiver's actual quiet state;
the token is the final occurrence of Q++[token], not a sorted-list premise. -/
theorem quiet_wire_arrival_exists {θA θB ε route sA uA}
    (hb : PhysicalBox (extendParameters θA (θB 0)) ε)
    (e : Execution θA (fun _ _ => []) sA uA)
    (he : e.ledger.emissions = []) (hd : e.deliveries = [])
    (sB : Snapshot 1) (hstart : sA.time = sB.time)
    (hsB : ReadyCoordinates sB 0) (hrB : ∀ q, sB.raw 0 q = none)
    (Q : List (Delivery 2)) (p : Port) (hQ : ∀ d ∈ Q, uA.time ≤ d.due)
    (hf : PhysicalInvariant (extendParameters θA (θB 0)) (sA.product sB (Q ++ [⟨1,p,uA.time⟩])))
    (hv : RawValid (sA.product sB (Q ++ [⟨1,p,uA.time⟩]))) :
    Nonempty (QuietWireArrival θA θB route sA sB uA Q p) := by
  have hqueue : ∀ d ∈ Q ++ [⟨1,p,uA.time⟩], uA.time ≤ d.due := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hQ d hd
    · have heq : d = (⟨1,p,uA.time⟩ : Delivery 2) := List.mem_singleton.mp hd
      subst d
      exact le_rfl
  obtain ⟨lifted,hem,hdel⟩ := e.product_with_quiet_left (θB := θB) he hd sB hstart hsB hrB
    (Q ++ [⟨1,p,uA.time⟩]) hqueue route
  let before := uA.product (quietAt sB uA.time) (Q ++ [⟨1,p,uA.time⟩])
  let final : Snapshot 2 := { (setRaw before 1 p (some before.time)) with pending := Q ++ [] }
  have hfree : before.raw 1 p = none := hrB p
  let jump : Jump route before final := .arrive before ⟨1,p,uA.time⟩ Q [] rfl rfl hfree
  have hjEm : jump.ledger.emissions = [] := rfl
  have hjDel : jump.deliveries = [⟨1,p,uA.time⟩] := rfl
  let trace := lifted.append (.cons (.jump jump) (.nil _))
  have hBtime : sB.time ≤ uA.time := by rw [← hstart]; exact e.time_monotone
  have hBready := quietAt_ready_coordinates sB 0 hsB hBtime
  refine ⟨{
    final := final
    execution := trace
    date := rfl
    pending := by simp [final]
    sender_values := rfl
    receiver_values := rfl
    sender_main := rfl
    sender_aux := fun _ => rfl
    receiver_ready := ⟨hBready.ready,hBready.charge,hBready.auxiliary⟩
    sender_raw := ?_
    raw_active := ?_
    raw_other := ?_
    emissions := ?_
    deliveries := ?_
    physical := trace.physical_invariant hb hf
    raw_valid := trace.raw_valid hv
  }⟩
  · intro q
    have hleft : before.raw 0 q = uA.raw 0 q := rfl
    simpa [final,setRaw,Function.update_apply] using hleft
  · simp [final,setRaw,before,Snapshot.product]
  · intro q hq
    have hright : before.raw 1 q = none := hrB q
    simpa [final,setRaw,Function.update_apply,hq] using hright
  · simp only [trace,Execution.emissions_append,hem,Execution.ledger,Move.ledger,
      Ledger.add,Ledger.zero,hjEm,List.append_nil]
  · simp only [trace,Execution.deliveries_append,hdel,Execution.deliveries,
      Move.deliveries,hjDel,List.nil_append,List.append_nil]

/-- A real next local flow witnesses that all sender guards and RAW ends at
the cut have been discharged. Thus receiver delivery can saturate the cut. -/
theorem QuietWireArrival.complete_of_next {θA θB route sA sB uA Q p}
    (c : QuietWireArrival θA θB route sA sB uA Q p) {vA : Snapshot 1}
    (next : Flow θA uA vA) (hQ : ∀ d ∈ Q, uA.time < d.due) :
    CompleteThrough c.execution uA.time := by
  have hg : BeforeGuards uA uA.x := by
    have h := next.guards uA.time ⟨le_rfl,next.positive⟩
    rw [next.initial] at h
    exact h
  have hguard : BeforeGuards c.final c.final.x := by
    constructor
    · intro j
      rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
      · rw [c.sender_main,c.sender_values]
        exact hg.1 0
      · rw [c.receiver_ready.ready]
        linarith [c.receiver_ready.charge.2]
    · intro j q
      rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
      · rw [c.sender_aux,c.sender_values]
        exact hg.2 0 q
      · rw [(c.receiver_ready.auxiliary q).1]
        linarith [(c.receiver_ready.auxiliary q).2.2]
  have hfuture : ∀ d ∈ c.final.pending, c.final.time < d.due := by
    intro d hd
    rw [c.pending] at hd
    rw [c.date]
    exact hQ d hd
  refine ⟨c.date,?_,?_⟩
  · intro u
    apply hguard.no_jump
    · intro j q origin hraw
      rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
      · rw [c.sender_raw] at hraw
        have h := (next.raw_support 0 q origin hraw).2
        rw [c.date]
        linarith [next.positive]
      · by_cases hq : q = p
        · subst q
          have ho : origin = uA.time := Option.some.inj (hraw.symm.trans c.raw_active)
          rw [ho,c.date]
          linarith
        · rw [c.raw_other q hq] at hraw
          contradiction
    · exact hfuture
  · intro d hd
    rw [c.pending] at hd
    exact hQ d hd

end KernelR.Hybrid
