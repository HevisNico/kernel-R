import KernelR.HybridFirstReverseInterleavedPair
import KernelR.HybridPortWeakCut
import KernelR.HybridReverseSourceWire
import KernelR.HybridReverseLatencyGeometry

/-! Continue the actual section352 through B's next real FIRE and reverse
receipt. A's preparation follows its retained first weak path and the actual
inter-receipt lower bound; its charge at352 is not reset. -/
namespace KernelR.Hybrid

namespace FirstReverseInterleavedPair
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
  {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
  (p : FirstReverseInterleavedPair r)

/-- Package precisely the weak response and cut already retained by p.
No second response, new cut or replacement coordinate is chosen. -/
noncomputable def receiver_port_weak_cut {ε} (hb : PhysicalBox θ ε)
    (hz : r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000) :
    PortWeakCut f.parametersA r.receiverLocal 2 352 where
  source_prepared := r.receiver_local_prepared 0
  weak := p.receiver.weak
  cut := p.receiver.cut352
  cut_emissions := p.receiver.cut_emissions
  cut_deliveries := p.receiver.cut_deliveries
  cut_main_ready := p.receiver.cut_main_ready
  cut_aux_rest := p.receiver.cut_aux_rest hb
  cut_raw_none := p.receiver.cut_raw_none
  cut_charge_lower := p.receiver.cut_charge_lower
  cut_error_dose := (p.receiver.cut_error_and_gain hb hz).1
  cut_gain_target := (p.receiver.cut_error_and_gain hb hz).2
  cut_gain_other := fun q hq =>
    (p.receiver.cut352.cut.aux_no_input_rest_band 0 q ((r.receiver_local_prepared 0).auxiliary q).1
      ((r.receiver_local_prepared 0).auxiliary q).2 (r.receiver_local_other 0 q (Or.inr hq))
      (p.receiver.cut_no_arrival q)).2
  cut_recovery := p.receiver.cut_recovery
  cut_pending := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    rcases p.receiver.cut352.cut.pending_provenance d hd with hs | ⟨event,_,hr⟩
    · change d ∈ ([] : List (Delivery 1)) at hs
      contradiction
    · contradiction
  cut_physical := p.receiver.cut_physical
  cut_raw_valid := p.receiver.cut_raw_valid

theorem receiver_source_projection {ε} (hb : PhysicalBox θ ε)
    (hz : r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000) :
    reverseSourceLocalA p.final = (p.receiver_port_weak_cut hb hz).cut.state := by
  let a := p.receiver_port_weak_cut hb hz
  have extensionality {n} (s u : Snapshot n) (ht : s.time = u.time) (hx : s.x = u.x)
      (hm : s.main = u.main) (ha : s.aux = u.aux) (hr : s.raw = u.raw)
      (hp : s.pending = u.pending) : s = u := by
    cases s
    cases u
    simp_all only
  apply extensionality
  · exact p.date.trans a.cut.date.symm
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact p.a_values
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact p.a_main
  · funext j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact p.a_aux q
  · funext j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact p.a_raw q
  · exact a.cut_pending.symm

end FirstReverseInterleavedPair

structure FirstReverseNextWire {θ forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    (p : FirstReverseInterleavedPair r) where
  receiver : PortWeakCut f.parametersA r.receiverLocal 2 352
  cycle : ShortLearnedCycle f.parametersB (reverseSourceLocalB p.final) 2
  wire : ReverseSourceWire f.parametersA f.parametersB forward backward p.final cycle
  execution : Execution θ (reciprocalEntryRouter forward backward) p.final wire.final
  execution_eq : execution = wire.execution.cast_parameters f.parameters_product
  received_gap : r.final.time + 79 / 10 ≤ wire.final.time
  after_weak : receiver.weak.final.time ≤ wire.final.time
  a_prepared : PreparedSection wire.final 0
  a_charge_lower : 1 / 10 ≤ wire.final.x 0 .q

/-- Source352 drives a real independent own B response. The first residual
FIRE bound derives enough waiting for A's actual weak return before H2. -/
theorem first_reverse_next_wire_exists {θ ε forward backward start}
    {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
    {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
    (p : FirstReverseInterleavedPair r) (hb : PhysicalBox θ ε)
    (hzA : r.final.x 0 (.z 2) ≤ Real.log (3 / 10) + 1 / 100000)
    (hGB : 9 / 5 ≤ Real.exp (w.final.x 1 (.z 2)) ∧ Real.exp (w.final.x 1 (.z 2)) ≤ 11 / 5)
    (hback : ∀ t, (3 / 10 : ℝ) ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (FirstReverseNextWire p) := by
  let receiver := p.receiver_port_weak_cut hb hzA
  let sB := reverseSourceLocalB p.final
  have hfB : PhysicalInvariant f.parametersB sB :=
    ⟨fun _ => p.physical.region 1,fun _ q => p.physical.gain_cap 1 q,
      fun _ => p.physical.recovery_cap 1,fun _ => p.physical.reserve 1⟩
  have hvB : RawValid sB := fun _ q origin h => p.raw_valid 1 q origin h
  have hsB : PreparedSection sB 0 :=
    ⟨p.b_prepared.ready,p.b_prepared.charge,p.b_prepared.recovery,p.b_prepared.auxiliary⟩
  have hqB : sB.x 0 .q = 1 / 10 := p.b_charge
  have hzB : sB.x 0 (.z 2) = w.final.x 1 (.z 2) := p.b_gains 2
  have hgB : 9 / 5 ≤ Real.exp (sB.x 0 (.z 2)) ∧ Real.exp (sB.x 0 (.z 2)) ≤ 11 / 5 := by
    rw [hzB]
    exact hGB
  have hrB : sB.raw 0 2 = some sB.time := by
    change p.final.raw 1 2 = some p.final.time
    rw [p.raw_active,p.date]
  obtain ⟨cycle⟩ := short_learned_cycle_exists (f.localB_box hb) sB 2 hfB hvB hsB hgB hrB
    p.raw_other_b (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  have hqA : p.final.x 0 .q < 1 := by
    rw [p.a_values]
    have h := p.receiver.cut352.before_guards.1 0
    rwa [p.receiver.cut_main_ready] at h
  have hxA : ∀ q, p.final.x 0 (.m q) < 1 := by
    intro q
    linarith [(p.a_aux_rest hb q).2.2]
  have hbProduct : PhysicalBox (extendParameters f.parametersA (f.parametersB 0)) ε := by
    rw [f.parameters_product]
    exact hb
  have hfProduct : PhysicalInvariant (extendParameters f.parametersA (f.parametersB 0)) p.final := by
    rw [f.parameters_product]
    exact p.physical
  have hQ : ∀ d ∈ p.final.pending, p.final.time + 8 ≤ d.due := by
    intro d hd
    rw [p.pending] at hd
    rw [p.date]
    rcases List.mem_append.mp hd with hd | hd
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨wire⟩ := reverse_source_wire_exists (forward := forward) p.final cycle hbProduct hfProduct p.raw_valid
    (by rw [p.date]; norm_num) p.a_main_ready (fun q => (p.a_aux_rest hb q).1)
    p.a_raw_none hqA hxA hQ hback
  have htimeB : sB.time = w.final.time + 8 := by
    change p.final.time = w.final.time + 8
    rw [p.date,w.date]
    norm_num
  have hgap : r.final.time + 79 / 10 ≤ wire.final.time := by
    rw [r.date,wire.date]
    exact f.next_rest_receipt_gap cycle.fire hqB
      ⟨hgB.1,by linarith [hgB.2]⟩ hzB htimeB hback
  have hAfter : receiver.weak.final.time ≤ wire.final.time := by
    rw [receiver.weak.date]
    change r.final.time + 15 / 2 ≤ wire.final.time
    linarith
  have hSourceA : reverseSourceLocalA p.final = receiver.cut.state :=
    p.receiver_source_projection hb hzA
  have hQuiet : PreparedSection (quietAt (reverseSourceLocalA p.final) wire.final.time) 0 := by
    rw [hSourceA]
    exact receiver.quiet_after_cut_prepared hAfter 0
  have hCharge : 1 / 10 ≤ wire.final.x 0 .q := by
    rw [wire.a_values,hSourceA]
    exact receiver.quiet_after_cut_charge_lower wire.final.time
  exact ⟨{
    receiver := receiver, cycle := cycle, wire := wire
    execution := wire.execution.cast_parameters f.parameters_product, execution_eq := rfl
    received_gap := hgap, after_weak := hAfter
    a_prepared := wire.receiver_prepared hQuiet, a_charge_lower := hCharge
  }⟩

namespace FirstReverseNextWire
variable {θ forward backward start}
  {w : FeedbackWeakEntry θ (reciprocalEntryRouter forward backward) start}
  {f : FeedbackFirstFire w} {r : FirstReverseWiredArrival f}
  {p : FirstReverseInterleavedPair r} (n : FirstReverseNextWire p)

noncomputable def final : Snapshot 2 := n.wire.final

theorem date : n.final.time = n.cycle.fire.final.time + backward n.cycle.fire.final.time := n.wire.date

theorem window : 352 + (7 / 10 : ℝ) < n.final.time ∧ n.final.time < 352 + 11 / 10 := by
  simpa only [final,p.date] using n.wire.window

theorem pending : n.final.pending = firstReverseInterleavedPending := n.wire.pending.trans p.pending

theorem pending_length : n.final.pending.length = 27 := by
  rw [n.pending]
  simp [firstReverseInterleavedPending,sourceTrain]

theorem gains (i : Fin 2) (q : Port) : n.final.x i (.z q) = p.final.x i (.z q) := n.wire.gains i q

theorem recovery (i : Fin 2) : n.final.x i .b = p.final.x i .b := n.wire.recovery i

theorem emissions : n.execution.ledger.emissions = [(1,n.cycle.fire.final.time)] := by
  rw [n.execution_eq,Execution.cast_parameters_ledger]
  exact n.wire.emissions

theorem deliveries : n.execution.deliveries = [⟨0,2,n.final.time⟩] := by
  rw [n.execution_eq,Execution.cast_parameters_deliveries]
  exact n.wire.deliveries

theorem raw_active : n.final.raw 0 2 = some n.final.time := n.wire.raw_active

theorem raw_other_a (q : Port) (hq : q ≠ 2) : n.final.raw 0 q = none := n.wire.raw_other_a q hq

theorem physical : PhysicalInvariant θ n.final := by
  have h := n.wire.physical
  rw [f.parameters_product] at h
  exact h

theorem raw_valid : RawValid n.final := n.wire.raw_valid

theorem complete : CompleteThrough n.execution n.final.time := by
  simpa only [final,CompleteThrough] using n.wire.complete

end FirstReverseNextWire
end KernelR.Hybrid
