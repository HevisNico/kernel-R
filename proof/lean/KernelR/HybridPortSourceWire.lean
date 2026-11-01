import KernelR.HybridShortLearnedCycle
import KernelR.HybridFirstReceiverFire
import KernelR.HybridQuietWireArrival
import KernelR.HybridPrefixStableMemory

/-! A real learned sender FIRE issues an arbitrary-port wire to a quiet READY
receiver. In particular the receiver may retain newborn recovery near .08. -/
namespace KernelR.Hybrid

noncomputable def portSourceSender (s : Snapshot 2) : Snapshot 1 := s.cellProjection 0 []
noncomputable def portSourceReceiver (s : Snapshot 2) : Snapshot 1 := s.cellProjection 1 []

structure PortSourceWire (θS θR : Fin 1 → Parameters) (route : Router 2)
    (source : Snapshot 2) {pS : Port}
    (cycle : ShortLearnedCycle θS (portSourceSender source) pS) (pR : Port)
    (delay : ℝ → ℝ) where
  cutH : cycle.fast.execution.BeforeFlowCut (cycle.fire.final.time + delay cycle.fire.final.time)
  wireReceipt : QuietWireArrival θS θR route cycle.fire.final
    (quietAt (portSourceReceiver source) cycle.fire.final.time) cutH.state source.pending pR
  final : Snapshot 2
  final_eq : final = wireReceipt.final
  execution : Execution (extendParameters θS (θR 0)) route source final
  date : final.time = cycle.fire.final.time + delay cycle.fire.final.time
  window : source.time + 7 / 10 < final.time ∧ final.time < source.time + 11 / 10
  pending : final.pending = source.pending
  sender_values : final.x 0 = cutH.state.x 0
  sender_main : final.main 0 = cutH.state.main 0
  sender_aux : ∀ q, final.aux 0 q = cutH.state.aux 0 q
  sender_raw : ∀ q, final.raw 0 q = cutH.state.raw 0 q
  receiver_values : final.x 1 = (quietAt (portSourceReceiver source) final.time).x 0
  receiver_ready : ReadyCoordinates final 1
  raw_active : final.raw 1 pR = some final.time
  raw_other : ∀ q, q ≠ pR → final.raw 1 q = none
  gains : ∀ i q, final.x i (.z q) = source.x i (.z q)
  recovery : ∀ i, final.x i .b = source.x i .b
  emissions : execution.ledger.emissions = [(0,cycle.fire.final.time)]
  deliveries : execution.deliveries = [⟨1,pR,final.time⟩]
  physical : PhysicalInvariant (extendParameters θS (θR 0)) final
  raw_valid : RawValid final
  complete : CompleteThrough execution final.time

/-- The only wire token is appended by the actual sender FIRE. A local cycle
is supplied, while the receiver follows its own unreset quiet coordinates. -/
theorem port_source_wire_exists {θS θR ε route pS pR delay}
    (source : Snapshot 2) (cycle : ShortLearnedCycle θS (portSourceSender source) pS)
    (hb : PhysicalBox (extendParameters θS (θR 0)) ε)
    (hf : PhysicalInvariant (extendParameters θS (θR 0)) source) (hv : RawValid source)
    (hready : ReadyCoordinates source 1) (hraw : ∀ q, source.raw 1 q = none)
    (hQ : ∀ d ∈ source.pending, source.time + 8 ≤ d.due)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ delay t ∧ delay t ≤ 2 / 5)
    (hroute : ∀ F, source.time + 2 / 5 < F → F < source.time + 7 / 10 →
      route 0 F = [⟨1,pR,F + delay F⟩]) :
    Nonempty (PortSourceWire θS θR route source cycle pR delay) := by
  let sS := portSourceSender source
  let sR := portSourceReceiver source
  let F := cycle.fire.final.time
  let H := F + delay F
  let Q := source.pending
  have hF : source.time + 2 / 5 < F ∧ F < source.time + 7 / 10 := cycle.fire_bounds
  have hH : source.time + 7 / 10 < H ∧ H < source.time + 11 / 10 := by
    constructor <;> dsimp [H] <;> linarith [(hdelay F).1,(hdelay F).2]
  have hFH : F < H := by dsimp [H]; linarith [(hdelay F).1]
  have hSource : sS.product sR Q = source := source.cellProjection_product [] []
  have hRF : sR.time < F := by change source.time < F; linarith [hF.1]
  let quiet : Flow θR sR (quietAt sR F) := quietFlow sR hRF
    (fun _ => hready.ready) (fun _ q => (hready.auxiliary q).1) (fun _ q => hraw q)
    (fun _ => by change source.x 1 .q < 1; linarith [hready.charge.2])
    (fun _ q => by change source.x 1 (.m q) < 1; linarith [(hready.auxiliary q).2.2])
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let wait : Execution θR (fun _ _ => []) sR (quietAt sR F) := .cons (.flow quiet) (.nil _)
  have hQF : ∀ d ∈ Q, cycle.fire.portBefore.time ≤ d.due := by
    intro d hd
    change F ≤ d.due
    linarith [hQ d hd,hF.2]
  obtain ⟨lifted,heL,hdL⟩ := cycle.fire.portBeforeExecution.product_neutral wait rfl rfl
    cycle.fire.portBefore_emissions cycle.fire.portBefore_deliveries rfl rfl Q hQF route
  let before := cycle.fire.portBefore.product (quietAt sR F) Q
  let after := cycle.fire.final.product (quietAt sR F) (Q ++ route 0 F)
  let pre : Execution (extendParameters θS (θR 0)) route source before :=
    lifted.cast_source hSource.symm
  have hafter : after = {setMain before 0 .fast with pending := before.pending ++ route 0 before.time} := by
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
    simp only [firing,Execution.deliveries_append,hdPre,Execution.deliveries,Move.deliveries,hdFire,
      List.append_nil]
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
  have hlocalReady : ReadyCoordinates sR 0 := ⟨hready.ready,hready.charge,hready.auxiliary⟩
  have hRready : ReadyCoordinates (quietAt sR F) 0 :=
    quietAt_ready_coordinates sR 0 hlocalReady hRF.le
  have hfAfter : PhysicalInvariant (extendParameters θS (θR 0))
      (cycle.fire.final.product (quietAt sR F) (Q ++ [⟨1,pR,cut.state.time⟩])) := by
    rw [← hAfter]
    exact firing.physical_invariant hb hf
  have hvAfter : RawValid (cycle.fire.final.product (quietAt sR F) (Q ++ [⟨1,pR,cut.state.time⟩])) := by
    rw [← hAfter]
    exact firing.raw_valid hv
  obtain ⟨wire⟩ := quiet_wire_arrival_exists hb cut.cut heCut hdCut (quietAt sR F) rfl
    hRready hraw Q pR (fun d hd => (hQH d hd).le) hfAfter hvAfter
  let wireTrace : Execution (extendParameters θS (θR 0)) route after wire.final :=
    wire.execution.cast_source hAfter
  let trace := firing.append wireTrace
  have heWire : wireTrace.ledger.emissions = [] := by
    rw [Execution.cast_source_ledger]
    exact wire.emissions
  have hdWire : wireTrace.deliveries = [⟨1,pR,cut.state.time⟩] := by
    rw [Execution.cast_source_deliveries]
    exact wire.deliveries
  have hvaluesR : wire.final.x 1 = (quietAt sR wire.final.time).x 0 := by
    rw [wire.receiver_values,wire.date,quietAt_quietAt]
  have hgainS : ∀ q, wire.final.x 0 (.z q) = source.x 0 (.z q) := by
    intro q
    rw [wire.sender_values]
    have h := cut.isPrefix.gain_eq_of_final hb.extend_old 0 q (cycle.fast.gains 0 q)
    exact h.trans (cycle.fire.gain_preserved 0 q)
  have hrecS : wire.final.x 0 .b = source.x 0 .b := by
    rw [wire.sender_values]
    have h := cut.isPrefix.recovery_eq_of_final hb.extend_old 0 (cycle.fast.recovery 0)
    exact h.trans (cycle.fire.recovery_preserved 0)
  have hcomplete : CompleteThrough trace wire.final.time := by
    rw [wire.date]
    exact wire.complete_of_next cut.flow hQH
  refine ⟨{
    cutH := cut, wireReceipt := wire, final := wire.final, final_eq := rfl, execution := trace
    date := wire.date.trans cut.date, window := ?_, pending := wire.pending
    sender_values := wire.sender_values, sender_main := wire.sender_main
    sender_aux := wire.sender_aux, sender_raw := wire.sender_raw
    receiver_values := hvaluesR, receiver_ready := wire.receiver_ready
    raw_active := ?_, raw_other := wire.raw_other, gains := ?_, recovery := ?_
    emissions := ?_, deliveries := ?_, physical := trace.physical_invariant hb hf
    raw_valid := trace.raw_valid hv, complete := hcomplete
  }⟩
  · rw [wire.date,cut.date]
    exact hH
  · rw [wire.date]
    exact wire.raw_active
  · intro i q
    fin_cases i
    · exact hgainS q
    · change wire.final.x 1 (.z q) = source.x 1 (.z q)
      rw [hvaluesR]; rfl
  · intro i
    fin_cases i
    · exact hrecS
    · change wire.final.x 1 .b = source.x 1 .b
      rw [hvaluesR]; rfl
  · rw [Execution.emissions_append,heFiring,heWire,List.append_nil]
  · rw [Execution.deliveries_append,hdFiring,hdWire,List.nil_append,wire.date]

namespace PortSourceWire
variable {θS θR route source pS cycle pR delay}
  (r : @PortSourceWire θS θR route source pS cycle pR delay)

theorem error_zero (i : Fin 2) (q : Port) : r.execution.ledger.error i q = 0 := by
  have h := r.execution.gain_balance i q
  rw [r.gains] at h
  linarith

theorem recovery_zero (i : Fin 2) : r.execution.ledger.recovery i = 0 := by
  have h := r.execution.recovery_balance i
  rw [r.recovery] at h
  linarith

end PortSourceWire
end KernelR.Hybrid
