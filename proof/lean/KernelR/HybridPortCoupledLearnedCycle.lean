import KernelR.HybridPortSourceWire
import KernelR.HybridIntervalClosedExecutionProduct

/-! A genuine learned left-to-right cycle on arbitrary receiving ports. -/
namespace KernelR.Hybrid

private theorem port_cycle_physical {θS θR : Fin 1 → Parameters} {s : Snapshot 2}
    (hf : PhysicalInvariant (extendParameters θS (θR 0)) s) (i : Fin 2)
    (θ : Fin 1 → Parameters) (hθ : θ 0 = (extendParameters θS (θR 0)) i) :
    PhysicalInvariant θ (s.cellProjection i []) := by
  refine ⟨fun _ => hf.region i,?_,fun _ => hf.recovery_cap i,fun _ => hf.reserve i⟩
  intro j p
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  change s.x i (.z p) ≤ Real.log ((θ 0).cap p)
  rw [hθ]
  exact hf.gain_cap i p

private theorem port_cycle_raw {s : Snapshot 2} (hv : RawValid s) (i : Fin 2) :
    RawValid (s.cellProjection i []) := fun _ p origin h => hv i p origin h

private theorem port_wire_product {θS θR route source pS cycle pR delay}
    (r : @PortSourceWire θS θR route source pS cycle pR delay) :
    r.cutH.state.product (portSourceReceiver r.final) source.pending = r.final := by
  have extensionality {n} (s u : Snapshot n)
      (ht : s.time = u.time) (hx : s.x = u.x) (hm : s.main = u.main)
      (ha : s.aux = u.aux) (hr : s.raw = u.raw) (hp : s.pending = u.pending) : s = u := by
    cases s; cases u; simp_all only
  apply extensionality
  · exact r.cutH.date.trans r.date.symm
  · funext j
    fin_cases j
    · exact r.sender_values.symm
    · rfl
  · funext j
    fin_cases j
    · exact r.sender_main.symm
    · rfl
  · funext j q
    fin_cases j
    · exact (r.sender_aux q).symm
    · rfl
  · funext j q
    fin_cases j
    · exact (r.sender_raw q).symm
    · rfl
  · exact r.pending.symm

structure PortCoupledLearnedCycle (θS θR : Fin 1 → Parameters) (route : Router 2)
    (source : Snapshot 2) (pS pR : Port) (delay : ℝ → ℝ) where
  source_charge : ∀ i, source.x i .q = 1 / 10
  senderCycle : ShortLearnedCycle θS (portSourceSender source) pS
  wire : PortSourceWire θS θR route source senderCycle pR delay
  receiverCycle : ShortLearnedCycle θR (portSourceReceiver wire.final) pR
  final : Snapshot 2
  execution : Execution (extendParameters θS (θR 0)) route source final
  date : final.time = source.time + 8
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i p, final.raw i p = none
  pending : final.pending = source.pending
  gains : ∀ i p, final.x i (.z p) = source.x i (.z p)
  recovery : ∀ i, final.x i .b = source.x i .b
  emissions : execution.ledger.emissions =
    [(0,senderCycle.fire.final.time),(1,receiverCycle.fire.final.time)]
  deliveries : execution.deliveries = [⟨1,pR,wire.final.time⟩]
  physical : PhysicalInvariant (extendParameters θS (θR 0)) final
  raw_valid : RawValid final

theorem port_coupled_learned_cycle_exists {θS θR ε route pS pR delay}
    (hb : PhysicalBox (extendParameters θS (θR 0)) ε)
    (source : Snapshot 2) (hf : PhysicalInvariant (extendParameters θS (θR 0)) source) (hv : RawValid source)
    (htime : 480 ≤ source.time ∧ source.time ≤ 600)
    (hs : ∀ i, PreparedSection source i) (hq : ∀ i, source.x i .q = 1 / 10)
    (hGS : 9 / 5 ≤ Real.exp (source.x 0 (.z pS)) ∧ Real.exp (source.x 0 (.z pS)) ≤ 2)
    (hGR : 9 / 5 ≤ Real.exp (source.x 1 (.z pR)) ∧ Real.exp (source.x 1 (.z pR)) ≤ 11 / 5)
    (hr : source.raw 0 pS = some source.time)
    (ho : ∀ i p, i ≠ 0 ∨ p ≠ pS → source.raw i p = none)
    (hp : ∀ d ∈ source.pending, source.time + 8 ≤ d.due)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ delay t ∧ delay t ≤ 2 / 5)
    (hroute : ∀ F, 480 ≤ F → F < 601 → route 0 F = [⟨1,pR,F + delay F⟩])
    (hclosed : ∀ t, 480 ≤ t → t ≤ 608 → route 1 t = []) :
    Nonempty (PortCoupledLearnedCycle θS θR route source pS pR delay) := by
  have hbR : PhysicalBox θR ε := by
    refine ⟨hb.1,?_⟩
    intro j p
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hb.2 1 p
  have hS : PreparedSection (portSourceSender source) 0 :=
    ⟨(hs 0).ready,(hs 0).charge,(hs 0).recovery,(hs 0).auxiliary⟩
  obtain ⟨sc⟩ := short_learned_cycle_exists hb.extend_old (portSourceSender source) pS
    (port_cycle_physical hf 0 θS rfl) (port_cycle_raw hv 0) hS
    ⟨hGS.1,by change Real.exp (source.x 0 (.z pS)) ≤ 11 / 5; linarith [hGS.2]⟩ hr
    (fun p hp => ho 0 p (Or.inr hp))
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  obtain ⟨wire⟩ := port_source_wire_exists (route := route) (pR := pR) (delay := delay)
    source sc hb hf hv (hs 1).ready_coordinates (fun p => ho 1 p (Or.inl (by decide))) hp hdelay
    (by intro F hlo hhi; apply hroute F <;> linarith [htime.1,htime.2])
  have hR : PreparedSection (portSourceReceiver wire.final) 0 := by
    refine ⟨wire.receiver_ready.ready,wire.receiver_ready.charge,?_,wire.receiver_ready.auxiliary⟩
    change 17999 / 100000 ≤ wire.final.x 1 .b ∧ wire.final.x 1 .b ≤ 18001 / 100000
    rw [wire.recovery]
    exact (hs 1).recovery
  have hRG : 9 / 5 ≤ Real.exp ((portSourceReceiver wire.final).x 0 (.z pR)) ∧
      Real.exp ((portSourceReceiver wire.final).x 0 (.z pR)) ≤ 11 / 5 := by
    change 9 / 5 ≤ Real.exp (wire.final.x 1 (.z pR)) ∧ Real.exp (wire.final.x 1 (.z pR)) ≤ 11 / 5
    rw [wire.gains]
    exact hGR
  obtain ⟨rc⟩ := short_learned_cycle_exists hbR (portSourceReceiver wire.final) pR
    (port_cycle_physical wire.physical 1 θR rfl) (port_cycle_raw wire.raw_valid 1) hR hRG
    wire.raw_active wire.raw_other
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let sTail : Execution θS (fun _ _ => []) wire.cutH.state sc.fast.final :=
    .cons (.flow wire.cutH.flow) wire.cutH.rest
  have heSTail : sTail.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (wire.cutH.emissions.symm.trans sc.fast.emissions)).2
  have hdSTail : sTail.deliveries = [] :=
    (List.append_eq_nil_iff.mp (wire.cutH.deliveries.symm.trans sc.fast.deliveries)).2
  have hSend : sc.returned.final.time < source.time + 8 := by
    rw [sc.date]; change source.time + 69 / 10 < _; linarith
  have hSempty : sc.returned.final.pending = [] := sc.pending
  let sWaitFlow : Flow θS sc.returned.final (quietAt sc.returned.final (source.time + 8)) :=
    quietFlow sc.returned.final hSend (fun j => (sc.ready j).ready)
      (fun j p => ((sc.ready j).auxiliary p).1) sc.raw_none
      (fun j => by linarith [(sc.ready j).charge.2])
      (fun j p => by linarith [((sc.ready j).auxiliary p).2.2])
      (by intro d hd; rw [hSempty] at hd; contradiction)
  let sWait : Execution θS (fun _ _ => []) sc.returned.final (quietAt sc.returned.final (source.time + 8)) :=
    .cons (.flow sWaitFlow) (.nil _)
  let sfinal := quietAt sc.returned.final (source.time + 8)
  let se := sTail.append (sc.returned.execution.append sWait)
  have heS : se.ledger.emissions = [] := by
    rw [Execution.emissions_append,heSTail,Execution.emissions_append,sc.returned.emissions]; rfl
  have hdS : se.deliveries = [] := by
    rw [Execution.deliveries_append,hdSTail,Execution.deliveries_append,sc.returned.deliveries]; rfl
  have hRend : rc.returned.final.time < source.time + 8 := by
    rw [rc.date]; change wire.final.time + 69 / 10 < source.time + 8
    linarith [wire.window.2]
  have hRempty : rc.returned.final.pending = [] := rc.pending
  let rWaitFlow : Flow θR rc.returned.final (quietAt rc.returned.final (source.time + 8)) :=
    quietFlow rc.returned.final hRend (fun j => (rc.ready j).ready)
      (fun j p => ((rc.ready j).auxiliary p).1) rc.raw_none
      (fun j => by linarith [(rc.ready j).charge.2])
      (fun j p => by linarith [((rc.ready j).auxiliary p).2.2])
      (by intro d hd; rw [hRempty] at hd; contradiction)
  let rWait : Execution θR (fun _ _ => []) rc.returned.final (quietAt rc.returned.final (source.time + 8)) :=
    .cons (.flow rWaitFlow) (.nil _)
  let rfinal := quietAt rc.returned.final (source.time + 8)
  let re := rc.execution.append rWait
  have heR : re.ledger.emissions = [(0,rc.fire.final.time)] := by
    rw [Execution.emissions_append,rc.emissions]; rfl
  have hdR : re.deliveries = [] := by rw [Execution.deliveries_append,rc.deliveries]; rfl
  have hstart : wire.cutH.state.time = (portSourceReceiver wire.final).time :=
    wire.cutH.date.trans wire.date.symm
  obtain ⟨woven,heW,hdW⟩ := se.product_right_closed_on re hstart rfl heS hdS hdR source.pending hp route
    (by intro t hlo hhi; apply hclosed t <;> change wire.final.time ≤ t at hlo <;>
      change t ≤ source.time + 8 at hhi <;> linarith [wire.window.1,htime.1,htime.2])
  let final := sfinal.product rfinal source.pending
  let tail : Execution (extendParameters θS (θR 0)) route wire.final final :=
    woven.cast_source (port_wire_product wire).symm
  have heTail : tail.ledger.emissions = [(1,rc.fire.final.time)] := by
    rw [Execution.cast_source_ledger]
    rw [heR] at heW
    exact heW
  have hdTail : tail.deliveries = [] := by rw [Execution.cast_source_deliveries]; exact hdW
  let trace := wire.execution.append tail
  have hSready : ∀ j, ReadyCoordinates sfinal j := fun j =>
    quietAt_ready_coordinates sc.returned.final j (sc.ready j) hSend.le
  have hRready : ∀ j, ReadyCoordinates rfinal j := fun j =>
    quietAt_ready_coordinates rc.returned.final j (rc.ready j) hRend.le
  have hSq : sfinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (sc.returned.final.x 0 .q) sc.returned.final.time (source.time + 8) = _
    rw [sc.charge]; simp [relax]
  have hRq : rfinal.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (rc.returned.final.x 0 .q) rc.returned.final.time (source.time + 8) = _
    rw [rc.charge]; simp [relax]
  refine ⟨{
    source_charge := hq, senderCycle := sc, wire := wire, receiverCycle := rc, final := final, execution := trace
    date := rfl, prepared := ?_, charge := ?_, raw_none := ?_, pending := rfl
    gains := ?_, recovery := ?_, emissions := ?_, deliveries := ?_
    physical := trace.physical_invariant hb hf, raw_valid := trace.raw_valid hv}⟩
  · intro i; fin_cases i
    · exact ⟨(hSready 0).ready,(hSready 0).charge,(sc.prepared 0).recovery,(hSready 0).auxiliary⟩
    · exact ⟨(hRready 0).ready,(hRready 0).charge,(rc.prepared 0).recovery,(hRready 0).auxiliary⟩
  · intro i; fin_cases i
    · exact hSq
    · exact hRq
  · intro i p; fin_cases i
    · exact sc.raw_none 0 p
    · exact rc.raw_none 0 p
  · intro i p; fin_cases i
    · exact sc.gains 0 p
    · change rc.returned.final.x 0 (.z p) = source.x 1 (.z p)
      exact (rc.gains 0 p).trans (wire.gains 1 p)
  · intro i; fin_cases i
    · exact sc.recovery 0
    · change rc.returned.final.x 0 .b = source.x 1 .b
      exact (rc.recovery 0).trans (wire.recovery 1)
  · rw [Execution.emissions_append,wire.emissions,heTail]; rfl
  · rw [Execution.deliveries_append,wire.deliveries,hdTail,List.append_nil]

namespace PortCoupledLearnedCycle
variable {θS θR route source pS pR delay}
  (c : PortCoupledLearnedCycle θS θR route source pS pR delay)
noncomputable def fireS : ℝ := c.senderCycle.fire.final.time
noncomputable def fireR : ℝ := c.receiverCycle.fire.final.time
noncomputable def wireTime : ℝ := c.wire.final.time

theorem wire_date : c.wireTime = c.fireS + delay c.fireS := c.wire.date

theorem sender_bounds : source.time + 2 / 5 < c.fireS ∧ c.fireS < source.time + 7 / 10 :=
  c.senderCycle.fire_bounds

theorem receiver_bounds : c.wireTime + 2 / 5 < c.fireR ∧ c.fireR < c.wireTime + 7 / 10 :=
  c.receiverCycle.fire_bounds

theorem error_zero (i : Fin 2) (p : Port) : c.execution.ledger.error i p = 0 := by
  have h := c.execution.gain_balance i p
  rw [c.gains] at h; linarith

theorem recovery_zero (i : Fin 2) : c.execution.ledger.recovery i = 0 := by
  have h := c.execution.recovery_balance i
  rw [c.recovery] at h; linarith

theorem complete (hstrict : ∀ d ∈ source.pending, source.time + 8 < d.due) :
    CompleteThrough c.execution (source.time + 8) := by
  have hfuture : ∀ d ∈ c.final.pending, c.final.time < d.due := by
    intro d hd; rw [c.pending,c.date] at *; exact hstrict d hd
  refine ⟨c.date,?_,?_⟩
  · intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro i; rw [(c.prepared i).ready,c.charge i]; norm_num
      · intro i p; rw [((c.prepared i).auxiliary p).1]; linarith [((c.prepared i).auxiliary p).2.2]
    · intro i p origin hr; rw [c.raw_none i p] at hr; contradiction
    · exact hfuture
  · intro d hd; rw [c.pending] at hd; exact hstrict d hd
end PortCoupledLearnedCycle
end KernelR.Hybrid
