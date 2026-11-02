import KernelR.HybridCSecondWire
import KernelR.HybridPortFirstLearnedCut

/-! C's first learned output and the true B496 source boundary, with the
original C SLOW flow retained for the following protected contact. -/
namespace KernelR.Hybrid

noncomputable def cFirstLearnedPending : List (Delivery 2) :=
  sourceTrain 0 2 504 8 13 ++ sourceTrain 1 0 640 4 25

structure CFirstLearnedBoundary {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay} {c : ConstructedCBirth t freshC newbornC delay}
    (w : CWeakEntry c) where
  second : CSecondWire w
  learned : PortFirstLearnedCut second.wire cFirstLearnedPending
  execution : Execution (cBirthPairParameters freshB freshC) (cBirthPairRouter delay)
    c.activePair learned.final
  reconstruct : execution = (w.execution.append second.wire.execution).append learned.execution

theorem c_first_learned_boundary_exists {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay ε} {c : ConstructedCBirth t freshC newbornC delay}
    (w : CWeakEntry c)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hd : ∀ F, (3 / 10 : ℝ) ≤ delay F ∧ delay F ≤ 2 / 5) :
    Nonempty (CFirstLearnedBoundary w) := by
  obtain ⟨second⟩ := c_second_wire_exists w hb hd
  have hbPair := cBirthPairParameters_physical_box hb
  have hqueue : w.final.pending = ⟨0,2,w.final.time + 8⟩ :: cFirstLearnedPending := by
    rw [w.pending,w.date]
    dsimp [cWeakEntryPending,cFirstLearnedPending]
    rw [sourceTrain_succ]
    norm_num
  have hfuture : ∀ d ∈ cFirstLearnedPending, w.final.time + 8 < d.due := by
    intro d hdue
    rw [w.date]
    rcases List.mem_append.mp hdue with hdue | hdue
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hdue
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨learned⟩ := port_first_learned_cut_exists second.wire hbPair
    second.wire.receiver_ready second.c_gain_bounds second.c_low_recovery
    (by intro time _ _; simp [cBirthPairRouter,cBirthPairContact,Contact.route])
    cFirstLearnedPending hqueue hfuture
  exact ⟨⟨second,learned,(w.execution.append second.wire.execution).append learned.execution,rfl⟩⟩

namespace CFirstLearnedBoundary
variable {θ born freshB newbornB forward backward}
  {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
  {freshC newbornC delay} {c : ConstructedCBirth t freshC newbornC delay}
  {w : CWeakEntry c} (p : CFirstLearnedBoundary w)

noncomputable abbrev final : Snapshot 2 := p.learned.final

theorem date : p.final.time = 496 := by rw [p.learned.date,w.date]; norm_num

theorem pending : p.final.pending = cFirstLearnedPending := p.learned.pending

theorem pending_length : p.final.pending.length = 38 := by
  rw [p.pending]
  simp [cFirstLearnedPending,sourceTrain]

theorem c_gain_target : p.final.x 1 (.z 1) = newbornC.x (.z 1) + 3 / 5 := by
  rw [p.learned.gains,p.second.c_gain_target]

theorem c_recovery : p.final.x 1 .b = newbornC.x .b := by
  rw [p.learned.recovery,p.second.c_recovery]

theorem sender_gains (q : Port) : p.final.x 0 (.z q) = c.activePair.x 0 (.z q) := by
  rw [p.learned.gains,p.second.wire.gains,w.sender_gains]

theorem emissions : p.execution.ledger.emissions =
    [(0,w.sender.fire.final.time),(0,p.second.sender.fire.final.time),(1,p.learned.fire.final.time)] := by
  rw [p.reconstruct,Execution.emissions_append,Execution.emissions_append,
    w.emissions,p.second.wire.emissions,p.learned.emissions]
  rfl

theorem complete : CompleteThrough p.execution 496 := by
  have h := p.learned.complete
  simpa only [CompleteThrough,w.date,show (488 : ℝ) + 8 = 496 by norm_num] using h

end CFirstLearnedBoundary
end KernelR.Hybrid
