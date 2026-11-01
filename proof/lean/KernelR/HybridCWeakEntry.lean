import KernelR.HybridCBirthActivePair
import KernelR.HybridPortWeakStep

/-! C's first actual contact and weak learning from its own independent
newborn state. The next B source is consumed on the real pair trajectory. -/
namespace KernelR.Hybrid

noncomputable def cWeakEntryPending : List (Delivery 2) :=
  sourceTrain 0 2 496 8 14 ++ sourceTrain 1 0 640 4 25

structure CWeakEntry {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay} (c : ConstructedCBirth t freshC newbornC delay) where
  sender : ShortLearnedCycle (fun _ : Fin 1 => freshB) (portSourceSender c.activePair) 2
  wire : PortSourceWire (fun _ => freshB) (fun _ => freshC)
    (cBirthPairRouter delay) c.activePair sender 1 delay
  weak : PortWeakStep wire cWeakEntryPending
  execution : Execution (cBirthPairParameters freshB freshC) (cBirthPairRouter delay)
    c.activePair weak.final
  reconstruct : execution = wire.execution.append weak.execution

theorem c_weak_entry_exists {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay ε} (c : ConstructedCBirth t freshC newbornC delay)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hd : ∀ F, (3 / 10 : ℝ) ≤ delay F ∧ delay F ≤ 2 / 5) :
    Nonempty (CWeakEntry c) := by
  have hbPair := cBirthPairParameters_physical_box hb
  have hsB : PreparedSection (portSourceSender c.activePair) 0 :=
    ⟨c.active_pair_b_prepared.ready,c.active_pair_b_prepared.charge,
      c.active_pair_b_prepared.recovery,c.active_pair_b_prepared.auxiliary⟩
  have hfB : PhysicalInvariant (fun _ : Fin 1 => freshB) (portSourceSender c.activePair) :=
    ⟨fun _ => c.active_pair_physical.region 0,fun _ p => c.active_pair_physical.gain_cap 0 p,
      fun _ => c.active_pair_physical.recovery_cap 0,fun _ => c.active_pair_physical.reserve 0⟩
  have hgb := c.active_pair_b_gain_bounds
  obtain ⟨sender⟩ := short_learned_cycle_exists hbPair.extend_old (portSourceSender c.activePair) 2
    hfB (fun _ p origin h => c.active_pair_raw_valid 0 p origin h) hsB
    ⟨hgb.1,by change Real.exp (c.activePair.x 0 (.z 2)) ≤ 11 / 5; linarith [hgb.2]⟩
    (by change c.activePair.raw 0 2 = some c.activePair.time; rw [c.active_pair_date]; exact c.active_pair_raw_active)
    (fun p hp => c.active_pair_raw_other 0 p (Or.inr hp))
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  have hQ : ∀ d ∈ c.activePair.pending, c.activePair.time + 8 ≤ d.due := by
    intro d hdue
    rw [c.active_pair_pending] at hdue
    rw [c.active_pair_date]
    rcases List.mem_append.mp hdue with hdue | hdue
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hdue
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨wire⟩ := port_source_wire_exists (θR := fun _ : Fin 1 => freshC) (pR := (1 : Port)) c.activePair sender hbPair
    c.active_pair_physical c.active_pair_raw_valid c.active_pair_c_ready c.active_pair_c_raw_none hQ hd
    (by intro F h1 h2; exact cBirthPairRouter_fire delay (by rw [c.active_pair_date]; norm_num) ⟨h1,h2⟩)
  have hTime : c.activePair.time ≤ wire.final.time := by linarith [wire.window.1]
  have hnarrow : wire.final.x 1 .q ≤ 10001 / 100000 := by
    rw [wire.receiver_values]
    have hr := relax_mem_Icc (target := (1 / 10 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2) hTime
      c.active_pair_c_charge (by constructor <;> norm_num)
    change relax (1 / 2) (1 / 10) (c.activePair.x 1 .q) c.activePair.time wire.final.time ≤ 10001 / 100000
    linarith [hr.2]
  have hzC := c.active_pair_c_gain (1 : Port)
  simp only [nominalGain,ite_true] at hzC
  have hzWire : wire.final.x 1 (.z 1) ≤ Real.log (6 / 5) + 1 / 100000 := by
    rw [wire.gains]
    exact hzC.2
  have hgWire : Real.exp (wire.final.x 1 (.z 1)) ≤ 4 / 3 :=
    fast_nominal_raw_gain_upper (by linarith)
  have hqueue : c.activePair.pending = ⟨0,2,c.activePair.time + 8⟩ :: cWeakEntryPending := by
    rw [c.active_pair_pending,c.active_pair_date]
    dsimp [cWeakEntryPending]
    rw [sourceTrain_succ]
    norm_num
  have hLater : ∀ d ∈ cWeakEntryPending, c.activePair.time + 8 < d.due := by
    intro d hdue
    rw [c.active_pair_date]
    rcases List.mem_append.mp hdue with hdue | hdue
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hdue
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨weak⟩ := port_weak_step_exists wire hbPair wire.receiver_ready hnarrow hgWire
    (by linarith) cWeakEntryPending hqueue hLater
  exact ⟨⟨sender,wire,weak,wire.execution.append weak.execution,rfl⟩⟩

namespace CWeakEntry
variable {θ born freshB newbornB forward backward}
  {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
  {freshC newbornC delay} {c : ConstructedCBirth t freshC newbornC delay} (w : CWeakEntry c)

noncomputable abbrev final : Snapshot 2 := w.weak.final

theorem date : w.final.time = 488 := by
  rw [final,w.weak.date,c.active_pair_date]
  norm_num

theorem pending : w.final.pending = cWeakEntryPending := w.weak.pending

theorem pending_length : w.final.pending.length = 39 := by
  rw [w.pending]
  simp [cWeakEntryPending,sourceTrain]

theorem c_gain_target : w.final.x 1 (.z 1) = newbornC.x (.z 1) + 3 / 5 := by
  rw [final,w.weak.receiver_gain_target,w.wire.gains,c.active_pair_c_coordinates]

theorem c_recovery : w.final.x 1 .b = newbornC.x .b := by
  rw [final,w.weak.recovery,w.wire.recovery,c.active_pair_c_coordinates]

theorem sender_gains (p : Port) : w.final.x 0 (.z p) = c.activePair.x 0 (.z p) := by
  rw [final,w.weak.sender_gains,w.wire.gains]

theorem emissions : w.execution.ledger.emissions = [(0,w.sender.fire.final.time)] := by
  rw [w.reconstruct,Execution.emissions_append,w.wire.emissions,w.weak.emissions,List.append_nil]

theorem deliveries : w.execution.deliveries = [⟨1,1,w.wire.final.time⟩,⟨0,2,488⟩] := by
  rw [w.reconstruct,Execution.deliveries_append,w.wire.deliveries,w.weak.deliveries,c.active_pair_date]
  norm_num

theorem complete : CompleteThrough w.execution 488 := by
  have h := w.weak.complete
  simpa only [CompleteThrough,c.active_pair_date,show (480 : ℝ) + 8 = 488 by norm_num] using h

theorem lifted_execution_exists : ∃ lifted :
    Execution (extendParameters (extendParameters θ freshB) freshC) (cTeachingRouter delay)
      c.final (w.final.prependQuiet (quietAt c.quietA w.final.time)),
    lifted.ledger.emissions = [(1,w.sender.fire.final.time)] ∧
      lifted.deliveries = [⟨2,1,w.wire.final.time⟩,⟨1,2,488⟩] := by
  obtain ⟨e,he,hd⟩ := w.execution.prepend_quiet θ c.quietA rfl c.quiet_a_ready c.quiet_a_raw_none
    c.quiet_a_pending (cTeachingRouter delay) (cBirthPairRouter_prepend delay)
  let lifted := (e.cast_source c.active_pair_reconstruct.symm).cast_parameters
    (cBirthPairParameters_prepend θ freshB freshC)
  have hledger : lifted.ledger = e.ledger :=
    ((e.cast_source c.active_pair_reconstruct.symm).cast_parameters_ledger
      (cBirthPairParameters_prepend θ freshB freshC)).trans
      (e.cast_source_ledger c.active_pair_reconstruct.symm)
  have hdel : lifted.deliveries = e.deliveries :=
    ((e.cast_source c.active_pair_reconstruct.symm).cast_parameters_deliveries
      (cBirthPairParameters_prepend θ freshB freshC)).trans
      (e.cast_source_deliveries c.active_pair_reconstruct.symm)
  refine ⟨lifted,?_,?_⟩
  · rw [hledger,he,w.emissions]
    rfl
  · rw [hdel,hd,w.deliveries]
    rfl

end CWeakEntry
end KernelR.Hybrid
