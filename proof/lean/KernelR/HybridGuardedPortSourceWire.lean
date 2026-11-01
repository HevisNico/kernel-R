import KernelR.HybridPortSourceWire

/-! A real left sender issues an arbitrary-port wire while its right
receiver continues from strict READY guards. A narrow receiver charge band
is derived at the receipt, never imposed at the preceding source or FIRE. -/
namespace KernelR.Hybrid

structure GuardedPortSourceWire (θS θR : Fin 1 → Parameters) (route : Router 2)
    (source : Snapshot 2) {pS : Port}
    (cycle : ShortLearnedCycle θS (portSourceSender source) pS) (pR : Port)
    (delay : ℝ → ℝ) where
  cutH : cycle.fast.execution.BeforeFlowCut (cycle.fire.final.time + delay cycle.fire.final.time)
  final : Snapshot 2
  execution : Execution (extendParameters θS (θR 0)) route source final
  wireExecution : Execution (extendParameters θS (θR 0)) route
    (cycle.fire.final.product (quietAt (portSourceReceiver source) cycle.fire.final.time)
      (source.pending ++ [⟨1,pR,cutH.state.time⟩])) final
  wire_emissions : wireExecution.ledger.emissions = []
  wire_deliveries : wireExecution.deliveries = [⟨1,pR,cutH.state.time⟩]
  date : final.time = cycle.fire.final.time + delay cycle.fire.final.time
  window : source.time + 7 / 10 < final.time ∧ final.time < source.time + 11 / 10
  pending : final.pending = source.pending
  sender_values : final.x 0 = cutH.state.x 0
  sender_main : final.main 0 = cutH.state.main 0
  sender_aux : ∀ q, final.aux 0 q = cutH.state.aux 0 q
  sender_raw : ∀ q, final.raw 0 q = cutH.state.raw 0 q
  receiver_values : final.x 1 = (quietAt (portSourceReceiver source) final.time).x 0
  receiver_main : final.main 1 = source.main 1
  receiver_aux : ∀ q, final.aux 1 q = source.aux 1 q
  raw_active : final.raw 1 pR = some final.time
  raw_other : ∀ q, q ≠ pR → final.raw 1 q = none
  gains : ∀ i q, final.x i (.z q) = source.x i (.z q)
  recovery : ∀ i, final.x i .b = source.x i .b
  emissions : execution.ledger.emissions = [(0,cycle.fire.final.time)]
  deliveries : execution.deliveries = [⟨1,pR,final.time⟩]
  physical : PhysicalInvariant (extendParameters θS (θR 0)) final
  raw_valid : RawValid final
  complete : CompleteThrough execution final.time

/-- Every quiet receiver flow uses only its actual mode, RAW absence and
strict guards. The unique routed token is issued by the explicit global FIRE. -/
theorem guarded_port_source_wire_exists {θS θR ε route pS pR delay}
    (source : Snapshot 2) (cycle : ShortLearnedCycle θS (portSourceSender source) pS)
    (hb : PhysicalBox (extendParameters θS (θR 0)) ε)
    (hf : PhysicalInvariant (extendParameters θS (θR 0)) source) (hv : RawValid source)
    (hmR : source.main 1 = .ready) (haR : ∀ q, source.aux 1 q = .ready)
    (hrR : ∀ q, source.raw 1 q = none) (hqR : source.x 1 .q < 1)
    (hxR : ∀ q, source.x 1 (.m q) < 1)
    (hQ : ∀ d ∈ source.pending, source.time + 8 ≤ d.due)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ delay t ∧ delay t ≤ 2 / 5)
    (hroute : ∀ F, source.time + 2 / 5 < F → F < source.time + 7 / 10 →
      route 0 F = [⟨1,pR,F + delay F⟩]) :
    Nonempty (GuardedPortSourceWire θS θR route source cycle pR delay) := by
  let sS := portSourceSender source
  let sR := portSourceReceiver source
  let F := cycle.fire.final.time
  let H := F + delay F
  let Q := source.pending
  have hF : source.time + 2 / 5 < F ∧ F < source.time + 7 / 10 := cycle.fire_bounds
  have hH : source.time + 7 / 10 < H ∧ H < source.time + 11 / 10 := by
    constructor <;> dsimp [H] <;> linarith [(hdelay F).1,(hdelay F).2]
  have hSource : sS.product sR Q = source := source.cellProjection_product [] []
  have hFR : sR.time < F := by change source.time < F; linarith [hF.1]
  have hFH : F < H := by dsimp [H]; linarith [(hdelay F).1]
  let flowR : Flow θR sR (quietAt sR F) := quietFlow sR hFR
    (fun _ => hmR) (fun _ q => haR q) (fun _ q => hrR q)
    (fun _ => hqR) (fun _ q => hxR q)
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let preR : Execution θR (fun _ _ => []) sR (quietAt sR F) := .cons (.flow flowR) (.nil _)
  have hQF : ∀ d ∈ Q, cycle.fire.portBefore.time ≤ d.due := by
    intro d hd
    change F ≤ d.due
    linarith [hQ d hd,hF.2]
  obtain ⟨lifted,heL,hdL⟩ := cycle.fire.portBeforeExecution.product_neutral preR rfl rfl
    cycle.fire.portBefore_emissions cycle.fire.portBefore_deliveries rfl rfl Q hQF route
  let before := cycle.fire.portBefore.product (quietAt sR F) Q
  let after := cycle.fire.final.product (quietAt sR F) (Q ++ route 0 F)
  let pre : Execution (extendParameters θS (θR 0)) route source before := lifted.cast_source hSource.symm
  have hafter : after = {(setMain before 0 .fast) with pending := before.pending ++ route 0 before.time} := by
    dsimp [after,before]
    rw [cycle.fire.port_final_empty,Snapshot.product_setMain_left]
    rfl
  let fire : Jump route before after := hafter.symm ▸
    Jump.fire before 0 (cycle.fire.firstSilent.main_ready 0) cycle.fire.threshold
  have heFire : fire.ledger.emissions = [(0,F)] :=
    fire.ready_main_departure_emission 0 (cycle.fire.firstSilent.main_ready 0)
      (by have h : after.main 0 = .fast := cycle.fire.main_fast; rw [h]; decide)
  have hdFire : fire.deliveries = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have h := fire.no_emissions_of_delivery d hd
    rw [heFire] at h
    contradiction
  let firing := pre.append (.cons (.jump fire) (.nil _))
  have hePre : pre.ledger.emissions = [] := by rw [Execution.cast_source_ledger]; exact heL
  have hdPre : pre.deliveries = [] := by rw [Execution.cast_source_deliveries]; exact hdL
  have heFiring : firing.ledger.emissions = [(0,F)] := by
    simp only [firing,Execution.emissions_append,hePre,Execution.ledger,Move.ledger,heFire,
      Ledger.add,Ledger.zero,List.nil_append,List.append_nil]
  have hdFiring : firing.deliveries = [] := by
    simp only [firing,Execution.deliveries_append,hdPre,Execution.deliveries,Move.deliveries,hdFire,List.append_nil]
  obtain ⟨cut⟩ := cycle.fast.execution.before_flow_cut_exists H hFH.le
    (by rw [cycle.fast.date]; dsimp [H,F]; linarith [(hdelay cycle.fire.final.time).2])
  have heCut : cut.cut.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (cut.emissions.symm.trans cycle.fast.emissions)).1
  have hdCut : cut.cut.deliveries = [] :=
    (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans cycle.fast.deliveries)).1
  have hrouteF : route 0 F = [⟨1,pR,cut.state.time⟩] := by
    rw [cut.date]
    exact hroute F hF.1 hF.2
  have hAfter : after = cycle.fire.final.product (quietAt sR F) (Q ++ [⟨1,pR,cut.state.time⟩]) := by
    dsimp [after]
    rw [hrouteF]
  have hQH : ∀ d ∈ Q, cut.state.time < d.due := by
    intro d hd
    rw [cut.date]
    linarith [hQ d hd,hH.2]
  have hfuture : ∀ d ∈ Q ++ [⟨1,pR,cut.state.time⟩], cut.state.time ≤ d.due := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact (hQH d hd).le
    · have he : d = (⟨1,pR,cut.state.time⟩ : Delivery 2) := List.mem_singleton.mp hd
      subst d
      exact le_rfl
  let flowRH : Flow θR (quietAt sR F) (quietAt (quietAt sR F) cut.state.time) :=
    quietFlow (quietAt sR F) (by rw [cut.date]; exact hFH)
      (fun _ => hmR) (fun _ q => haR q) (fun _ q => hrR q)
      (fun _ => relax_lt (by norm_num) hFR.le hqR (by norm_num))
      (fun _ q => relax_lt (by norm_num) hFR.le (hxR q) (by norm_num))
      (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let waitR : Execution θR (fun _ _ => []) (quietAt sR F) (quietAt (quietAt sR F) cut.state.time) :=
    .cons (.flow flowRH) (.nil _)
  obtain ⟨wireSpan,heW,hdW⟩ := cut.cut.product_neutral waitR rfl rfl heCut hdCut rfl rfl
    (Q ++ [⟨1,pR,cut.state.time⟩]) hfuture route
  let beforeWire := cut.state.product (quietAt (quietAt sR F) cut.state.time)
    (Q ++ [⟨1,pR,cut.state.time⟩])
  let final : Snapshot 2 := {(setRaw beforeWire 1 pR (some beforeWire.time)) with pending := Q ++ []}
  have hfree : beforeWire.raw 1 pR = none := hrR pR
  let arrival : Jump route beforeWire final := .arrive beforeWire ⟨1,pR,cut.state.time⟩ Q [] rfl rfl hfree
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨1,pR,cut.state.time⟩] := rfl
  let wire := wireSpan.append (.cons (.jump arrival) (.nil _))
  let wireTrace : Execution (extendParameters θS (θR 0)) route after final := wire.cast_source hAfter
  have heWire : wireTrace.ledger.emissions = [] := by
    rw [Execution.cast_source_ledger]
    simp only [wire,Execution.emissions_append,heW,Execution.ledger,Move.ledger,haEm,
      Ledger.add,Ledger.zero,List.nil_append]
  have hdWire : wireTrace.deliveries = [⟨1,pR,cut.state.time⟩] := by
    rw [Execution.cast_source_deliveries]
    simp only [wire,Execution.deliveries_append,hdW,Execution.deliveries,Move.deliveries,haDel,
      List.nil_append,List.append_nil]
  have heWireBare : wire.ledger.emissions = [] := by
    simpa only [wireTrace,Execution.cast_source_ledger] using heWire
  have hdWireBare : wire.deliveries = [⟨1,pR,cut.state.time⟩] := by
    simpa only [wireTrace,Execution.cast_source_deliveries] using hdWire
  let trace := firing.append wireTrace
  have hvaluesR : final.x 1 = (quietAt sR final.time).x 0 := by
    change (quietAt (quietAt sR F) cut.state.time).x 0 = (quietAt sR cut.state.time).x 0
    rw [quietAt_quietAt]
  have hgainS : ∀ q, final.x 0 (.z q) = source.x 0 (.z q) := by
    intro q
    change cut.state.x 0 (.z q) = source.x 0 (.z q)
    have h := cut.isPrefix.gain_eq_of_final hb.extend_old 0 q (cycle.fast.gains 0 q)
    exact h.trans (cycle.fire.gain_preserved 0 q)
  have hrecS : final.x 0 .b = source.x 0 .b := by
    have h := cut.isPrefix.recovery_eq_of_final hb.extend_old 0 (cycle.fast.recovery 0)
    exact h.trans (cycle.fire.recovery_preserved 0)
  have hrawActive : final.raw 1 pR = some final.time := by
    simp [final,setRaw,beforeWire,Snapshot.product,quietAt]
  have hrawOther : ∀ q, q ≠ pR → final.raw 1 q = none := by
    intro q hq
    have h : beforeWire.raw 1 q = none := hrR q
    simpa [final,setRaw,Function.update_apply,hq] using h
  have hSraw : ∀ q, final.raw 0 q = cut.state.raw 0 q := by
    intro q
    have h : beforeWire.raw 0 q = cut.state.raw 0 q := rfl
    simpa [final,setRaw,Function.update_apply] using h
  have hRq : final.x 1 .q < 1 := by
    rw [hvaluesR]
    exact relax_lt (by norm_num) (hFR.le.trans (by change F ≤ cut.state.time; rw [cut.date]; exact hFH.le)) hqR (by norm_num)
  have hRm : ∀ q, final.x 1 (.m q) < 1 := by
    intro q
    rw [hvaluesR]
    exact relax_lt (by norm_num) (hFR.le.trans (by change F ≤ cut.state.time; rw [cut.date]; exact hFH.le)) (hxR q) (by norm_num)
  have hrawFuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    change d ∈ Q ++ [] at hd
    simp only [List.append_nil] at hd
    exact hQH d hd
  have hcomplete : CompleteThrough trace final.time := by
    refine ⟨rfl,?_,hrawFuture⟩
    intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro i
        rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
        · have hm : final.main 0 = cut.state.main 0 := rfl
          have hx : final.x 0 = cut.state.x 0 := rfl
          rw [hm,hx]; exact cut.before_guards.1 0
        · have hm : final.main 1 = .ready := hmR
          rw [hm]; exact hRq
      · intro i q
        rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
        · have hm : final.aux 0 q = cut.state.aux 0 q := rfl
          have hx : final.x 0 = cut.state.x 0 := rfl
          rw [hm,hx]; exact cut.before_guards.2 0 q
        · have hm : final.aux 1 q = .ready := haR q
          rw [hm]; exact hRm q
    · intro i q origin hr
      rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
      · rw [hSraw] at hr
        exact cut.flow.initial_raw_strict 0 q origin hr
      · by_cases hq : q = pR
        · subst q
          have ho : origin = final.time := Option.some.inj (hr.symm.trans hrawActive)
          rw [ho]; linarith
        · rw [hrawOther q hq] at hr; contradiction
    · exact hrawFuture
  refine ⟨{
    cutH := cut, final := final, execution := trace, wireExecution := wire
    wire_emissions := heWireBare, wire_deliveries := hdWireBare, date := cut.date
    window := ?_, pending := by simp [final,Q]
    sender_values := rfl, sender_main := rfl, sender_aux := fun _ => rfl, sender_raw := hSraw
    receiver_values := hvaluesR, receiver_main := rfl, receiver_aux := fun _ => rfl
    raw_active := hrawActive, raw_other := hrawOther
    gains := ?_, recovery := ?_, emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb hf, raw_valid := trace.raw_valid hv, complete := hcomplete
  }⟩
  · change source.time + 7 / 10 < cut.state.time ∧ cut.state.time < source.time + 11 / 10
    rw [cut.date]
    exact hH
  · intro i q
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact hgainS q
    · rw [hvaluesR]; rfl
  · intro i
    rcases (show i = (0 : Fin 2) ∨ i = (1 : Fin 2) by fin_cases i <;> norm_num) with hi | hi <;> subst i
    · exact hrecS
    · rw [hvaluesR]; rfl
  · rw [Execution.emissions_append,heFiring,heWire,List.append_nil]
  · rw [Execution.deliveries_append,hdFiring,hdWire,List.nil_append]
    rfl

namespace GuardedPortSourceWire
variable {θS θR route source pS cycle pR delay}
  (r : @GuardedPortSourceWire θS θR route source pS cycle pR delay)

theorem receiver_ready
    (h : ReadyCoordinates (quietAt (portSourceReceiver source) r.final.time) 0) :
    ReadyCoordinates r.final 1 := by
  refine ⟨r.receiver_main.trans h.ready,?_,?_⟩
  · rw [r.receiver_values]; exact h.charge
  · intro q
    refine ⟨(r.receiver_aux q).trans (h.auxiliary q).1,?_⟩
    rw [r.receiver_values]; exact (h.auxiliary q).2

/-- Once the real preceding weak path supplies READY at H, expose the same
actual trace through the existing port-wire interface. No READY state at F
or replacement sender/receiver execution is required by this conversion. -/
noncomputable def to_portSourceWire
    (h : ReadyCoordinates (quietAt (portSourceReceiver source) r.final.time) 0) :
    PortSourceWire θS θR route source cycle pR delay := by
  have hdate : r.final.time = r.cutH.state.time := r.date.trans r.cutH.date.symm
  let receipt : QuietWireArrival θS θR route cycle.fire.final
      (quietAt (portSourceReceiver source) cycle.fire.final.time) r.cutH.state source.pending pR := {
    final := r.final, execution := r.wireExecution, date := hdate, pending := r.pending
    sender_values := r.sender_values
    receiver_values := by rw [r.receiver_values,quietAt_quietAt,hdate]
    sender_main := r.sender_main, sender_aux := r.sender_aux, sender_raw := r.sender_raw
    receiver_ready := r.receiver_ready h
    raw_active := by rw [← hdate]; exact r.raw_active
    raw_other := r.raw_other, emissions := r.wire_emissions, deliveries := r.wire_deliveries
    physical := r.physical, raw_valid := r.raw_valid
  }
  exact {
    cutH := r.cutH, wireReceipt := receipt, final := r.final, final_eq := rfl, execution := r.execution
    date := r.date, window := r.window, pending := r.pending
    sender_values := r.sender_values, sender_main := r.sender_main, sender_aux := r.sender_aux, sender_raw := r.sender_raw
    receiver_values := r.receiver_values, receiver_ready := r.receiver_ready h
    raw_active := r.raw_active, raw_other := r.raw_other, gains := r.gains, recovery := r.recovery
    emissions := r.emissions, deliveries := r.deliveries
    physical := r.physical, raw_valid := r.raw_valid, complete := r.complete
  }

theorem error_zero (i : Fin 2) (q : Port) : r.execution.ledger.error i q = 0 := by
  have h := r.execution.gain_balance i q
  rw [r.gains] at h
  linarith

theorem recovery_zero (i : Fin 2) : r.execution.ledger.recovery i = 0 := by
  have h := r.execution.recovery_balance i
  rw [r.recovery] at h
  linarith

end GuardedPortSourceWire
end KernelR.Hybrid
