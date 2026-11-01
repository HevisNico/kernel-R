import KernelR.HybridNeutralExecutionProduct
import KernelR.HybridPrefixBeforeFlow

/-! Consume an already issued left-directed token while the right sender
follows its actual neutral continuation and the left receiver stays quiet. -/
namespace KernelR.Hybrid

noncomputable def Execution.cast_parameters {n θ θ' route s u}
    (e : @Execution n θ route s u) (h : θ = θ') : Execution θ' route s u := h ▸ e

theorem Execution.cast_parameters_ledger {n θ θ' route s u}
    (e : @Execution n θ route s u) (h : θ = θ') : (e.cast_parameters h).ledger = e.ledger := by
  subst θ'
  rfl

theorem Execution.cast_parameters_deliveries {n θ θ' route s u}
    (e : @Execution n θ route s u) (h : θ = θ') : (e.cast_parameters h).deliveries = e.deliveries := by
  subst θ'
  rfl

structure QuietLeftWireArrival (θA θB : Fin 1 → Parameters) (route : Router 2)
    (sA sB uB : Snapshot 1) (Q : List (Delivery 2)) (p : Port) where
  final : Snapshot 2
  execution : Execution (extendParameters θA (θB 0)) route
    (sA.product sB (Q ++ [⟨0,p,uB.time⟩])) final
  date : final.time = uB.time
  pending : final.pending = Q
  receiver_values : final.x 0 = (quietAt sA uB.time).x 0
  sender_values : final.x 1 = uB.x 0
  receiver_ready : ReadyCoordinates final 0
  sender_main : final.main 1 = uB.main 0
  sender_aux : ∀ q, final.aux 1 q = uB.aux 0 q
  sender_raw : ∀ q, final.raw 1 q = uB.raw 0 q
  raw_active : final.raw 0 p = some uB.time
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨0,p,uB.time⟩]
  physical : PhysicalInvariant (extendParameters θA (θB 0)) final
  raw_valid : RawValid final

/-- The local receiver queue is empty metadata; the global queue alone
contains the actual issued occurrence, consumed after the retained sender path. -/
theorem quiet_left_wire_arrival_exists {θA θB ε route sB uB}
    (hb : PhysicalBox (extendParameters θA (θB 0)) ε)
    (e : Execution θB (fun _ _ => []) sB uB)
    (he : e.ledger.emissions = []) (hd : e.deliveries = [])
    (sA : Snapshot 1) (hstart : sA.time = sB.time) (hpos : sB.time < uB.time)
    (hsA : ReadyCoordinates sA 0) (hrA : ∀ q, sA.raw 0 q = none) (hpA : sA.pending = [])
    (Q : List (Delivery 2)) (p : Port) (hQ : ∀ d ∈ Q, uB.time ≤ d.due)
    (hf : PhysicalInvariant (extendParameters θA (θB 0)) (sA.product sB (Q ++ [⟨0,p,uB.time⟩])))
    (hv : RawValid (sA.product sB (Q ++ [⟨0,p,uB.time⟩]))) :
    Nonempty (QuietLeftWireArrival θA θB route sA sB uB Q p) := by
  have htime : sA.time < uB.time := hstart.trans_lt hpos
  let aflow : Flow θA sA (quietAt sA uB.time) := quietFlow sA htime
    (by intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hsA.ready)
    (by intro j q; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact (hsA.auxiliary q).1)
    (by intro j q; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hrA q)
    (by intro j; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [hsA.charge.2])
    (by intro j q; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(hsA.auxiliary q).2.2])
    (by intro d hd; rw [hpA] at hd; contradiction)
  let ae : Execution θA (fun _ _ => []) sA (quietAt sA uB.time) := .cons (.flow aflow) (.nil _)
  have hqueue : ∀ d ∈ Q ++ [⟨0,p,uB.time⟩], uB.time ≤ d.due := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hQ d hd
    · have heq : d = (⟨0,p,uB.time⟩ : Delivery 2) := List.mem_singleton.mp hd
      subst d
      exact le_rfl
  obtain ⟨lifted,hem,hdel⟩ := ae.product_neutral e hstart rfl rfl rfl he hd
    (Q ++ [⟨0,p,uB.time⟩]) hqueue route
  let before := (quietAt sA uB.time).product uB (Q ++ [⟨0,p,uB.time⟩])
  let final : Snapshot 2 := {(setRaw before 0 p (some before.time)) with pending := Q ++ []}
  have hfree : before.raw 0 p = none := hrA p
  let jump : Jump route before final := .arrive before ⟨0,p,uB.time⟩ Q [] rfl rfl hfree
  let trace := lifted.append (.cons (.jump jump) (.nil _))
  have hready := quietAt_ready_coordinates sA 0 hsA htime.le
  refine ⟨{
    final := final, execution := trace, date := rfl, pending := by simp [final]
    receiver_values := rfl, sender_values := rfl
    receiver_ready := ⟨hready.ready,hready.charge,hready.auxiliary⟩
    sender_main := rfl, sender_aux := fun _ => rfl
    sender_raw := ?_, raw_active := ?_, raw_other := ?_
    emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb hf, raw_valid := trace.raw_valid hv
  }⟩
  · intro q
    have hright : before.raw 1 q = uB.raw 0 q := rfl
    simpa [final,setRaw,Function.update_apply] using hright
  · simp [final,setRaw,before,Snapshot.product,quietAt]
  · intro q hq
    have hleft : before.raw 0 q = none := hrA q
    simpa [final,setRaw,Function.update_apply,hq] using hleft
  · have hj : jump.ledger.emissions = [] := rfl
    simp only [trace,Execution.emissions_append,hem,Execution.ledger,Move.ledger,
      hj,Ledger.add,Ledger.zero,List.nil_append]
  · have hj : jump.deliveries = [⟨0,p,uB.time⟩] := rfl
    simp only [trace,Execution.deliveries_append,hdel,Execution.deliveries,Move.deliveries,
      hj,List.nil_append,List.append_nil]

/-- The next real sender flow proves all coincident sender events have been
consumed before the actual receiver arrival is declared saturated. -/
theorem QuietLeftWireArrival.complete_of_next {θA θB route sA sB uB Q p}
    (c : QuietLeftWireArrival θA θB route sA sB uB Q p) {vB : Snapshot 1}
    (next : Flow θB uB vB) (hQ : ∀ d ∈ Q, uB.time < d.due) :
    CompleteThrough c.execution uB.time := by
  have hg := next.initial_before_guards
  have hguard : BeforeGuards c.final c.final.x := by
    constructor
    · intro j
      rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
      · rw [c.receiver_ready.ready]
        linarith [c.receiver_ready.charge.2]
      · rw [c.sender_main,c.sender_values]
        exact hg.1 0
    · intro j q
      rcases (show j = 0 ∨ j = 1 by omega) with hj | hj <;> subst j
      · rw [(c.receiver_ready.auxiliary q).1]
        linarith [(c.receiver_ready.auxiliary q).2.2]
      · rw [c.sender_aux,c.sender_values]
        exact hg.2 0 q
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
      · by_cases hq : q = p
        · subst q
          have ho : origin = uB.time := Option.some.inj (hraw.symm.trans c.raw_active)
          rw [ho,c.date]
          linarith
        · rw [c.raw_other q hq] at hraw
          contradiction
      · rw [c.sender_raw] at hraw
        rw [c.date]
        exact next.initial_raw_strict 0 q origin hraw
    · exact hfuture
  · intro d hd
    rw [c.pending] at hd
    exact hQ d hd

end KernelR.Hybrid
