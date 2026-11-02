import KernelR.HybridCWeakEntry
import KernelR.HybridGuardedPortSourceWire
import KernelR.HybridReverseLatencyGeometry

/-! C's second contact is issued by B's real response to source488. Its
READY band at receipt follows from C's retained own weak trajectory. -/
namespace KernelR.Hybrid

structure CSecondWire {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay} {c : ConstructedCBirth t freshC newbornC delay}
    (w : CWeakEntry c) where
  sender : ShortLearnedCycle (fun _ : Fin 1 => freshB) (portSourceSender w.final) 2
  wire : PortSourceWire (fun _ => freshB) (fun _ => freshC)
    (cBirthPairRouter delay) w.final sender 1 delay
  received_gap : w.wire.final.time + 79 / 10 ≤ wire.final.time ∧
    wire.final.time ≤ w.wire.final.time + 81 / 10

theorem c_second_wire_exists {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay ε} {c : ConstructedCBirth t freshC newbornC delay}
    (w : CWeakEntry c)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hd : ∀ F, (3 / 10 : ℝ) ≤ delay F ∧ delay F ≤ 2 / 5) :
    Nonempty (CSecondWire w) := by
  have hbPair := cBirthPairParameters_physical_box hb
  have hsB : PreparedSection (portSourceSender w.final) 0 :=
    ⟨w.weak.sender_prepared.ready,w.weak.sender_prepared.charge,
      w.weak.sender_prepared.recovery,w.weak.sender_prepared.auxiliary⟩
  have hfB : PhysicalInvariant (fun _ : Fin 1 => freshB) (portSourceSender w.final) :=
    ⟨fun _ => w.weak.physical.region 0,fun _ p => w.weak.physical.gain_cap 0 p,
      fun _ => w.weak.physical.recovery_cap 0,fun _ => w.weak.physical.reserve 0⟩
  have hgainB : 9 / 5 ≤ Real.exp (w.final.x 0 (.z 2)) ∧ Real.exp (w.final.x 0 (.z 2)) ≤ 2 := by
    rw [w.sender_gains]
    exact c.active_pair_b_gain_bounds
  obtain ⟨sender⟩ := short_learned_cycle_exists hbPair.extend_old (portSourceSender w.final) 2
    hfB (fun _ p origin h => w.weak.raw_valid 0 p origin h) hsB
    ⟨hgainB.1,by change Real.exp (w.final.x 0 (.z 2)) ≤ 11 / 5; linarith [hgainB.2]⟩
    (by change w.final.raw 0 2 = some w.final.time; rw [w.weak.raw_active,w.weak.date])
    w.weak.raw_other_sender
    (by intro d h; change d ∈ ([] : List (Delivery 1)) at h; contradiction)
  have hmain : w.final.main 1 = .ready := w.weak.receiver_main_ready
  have haux : ∀ p, w.final.aux 1 p = .ready := fun p => (w.weak.receiver_aux_rest p).1
  have hraw : ∀ p, w.final.raw 1 p = none := w.weak.receiver_raw_none
  have hq : w.final.x 1 .q < 1 := by
    rw [w.weak.receiver_values]
    have h := w.weak.receiver.cut.before_guards.1 0
    rwa [w.weak.receiver.cut_main_ready] at h
  have hm : ∀ p, w.final.x 1 (.m p) < 1 := by
    intro p
    linarith [(w.weak.receiver_aux_rest p).2.2]
  have hQ : ∀ d ∈ w.final.pending, w.final.time + 8 ≤ d.due := by
    intro d hdue
    rw [w.pending] at hdue
    rw [w.date]
    rcases List.mem_append.mp hdue with hdue | hdue
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hdue
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨guarded⟩ := guarded_port_source_wire_exists (θR := fun _ : Fin 1 => freshC)
    (pR := (1 : Port)) w.final sender hbPair w.weak.physical w.weak.raw_valid
    hmain haux hraw hq hm hQ hd
    (by intro F h1 h2; exact cBirthPairRouter_fire delay (by rw [w.date]; norm_num) ⟨h1,h2⟩)
  have hfireGap := w.sender.fire.rest_receipt_gap delay sender.fire
    c.active_pair_b_charge w.weak.sender_charge
    ⟨c.active_pair_b_gain_bounds.1,by
      change Real.exp (c.activePair.x 0 (.z 2)) ≤ 12 / 5
      linarith [c.active_pair_b_gain_bounds.2]⟩
    (w.sender_gains 2)
    (by change w.final.time = c.activePair.time + 8; rw [w.date,c.active_pair_date]; norm_num) hd
  have hgap : w.wire.final.time + 79 / 10 ≤ guarded.final.time ∧
      guarded.final.time ≤ w.wire.final.time + 81 / 10 := by
    rw [w.wire.date,guarded.date]
    exact hfireGap
  have hfinish : w.weak.receiver.weak.final.time ≤ guarded.final.time := by
    rw [w.weak.receiver.weak.date]
    change w.wire.final.time + 15 / 2 ≤ guarded.final.time
    linarith [hgap.1]
  have hready : ReadyCoordinates (quietAt (portSourceReceiver w.final) guarded.final.time) 0 := by
    rw [w.weak.receiver_local]
    exact w.weak.receiver.quiet_after_cut_ready hfinish 0
  exact ⟨⟨sender,guarded.to_portSourceWire hready,hgap⟩⟩

namespace CSecondWire
variable {θ born freshB newbornB forward backward}
  {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
  {freshC newbornC delay} {c : ConstructedCBirth t freshC newbornC delay}
  {w : CWeakEntry c} (v : CSecondWire w)

theorem c_gain_target : v.wire.final.x 1 (.z 1) = newbornC.x (.z 1) + 3 / 5 := by
  rw [v.wire.gains,w.c_gain_target]

theorem c_recovery : v.wire.final.x 1 .b = newbornC.x .b := by
  rw [v.wire.recovery,w.c_recovery]

theorem c_gain_bounds : 9 / 5 ≤ Real.exp (v.wire.final.x 1 (.z 1)) ∧
    Real.exp (v.wire.final.x 1 (.z 1)) ≤ 11 / 5 := by
  have hz := newbornC.gain (1 : Port)
  simp only [nominalGain,ite_true] at hz
  rw [v.c_gain_target]
  exact fast_learned_gain_sharp_bounds (by linarith [hz.1]) (by linarith [hz.2])

theorem c_low_recovery : 7999 / 100000 ≤ v.wire.final.x 1 .b ∧
    v.wire.final.x 1 .b ≤ 8001 / 100000 := by
  rw [v.c_recovery]
  constructor <;> linarith [newbornC.recovery.1,newbornC.recovery.2]

end CSecondWire
end KernelR.Hybrid
