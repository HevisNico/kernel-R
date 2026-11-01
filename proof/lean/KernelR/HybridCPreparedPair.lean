import KernelR.HybridCFirstLearnedBoundary
import KernelR.HybridPortSlowWire
import KernelR.HybridPortProtectedReturn

/-! The genuine third B contact gives C its protected MARK and its own
prepared recovery. Both real paths meet before consuming source B504. -/
namespace KernelR.Hybrid

noncomputable def cPreparedPending : List (Delivery 2) :=
  sourceTrain 0 2 512 8 12 ++ sourceTrain 1 0 640 4 25

structure CPreparedPair {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay} {c : ConstructedCBirth t freshC newbornC delay}
    {w : CWeakEntry c} (p : CFirstLearnedBoundary w) where
  slow : PortSlowWire p.learned
  protectedReturn : PortProtectedReturn slow cPreparedPending
  execution : Execution (cBirthPairParameters freshB freshC) (cBirthPairRouter delay)
    c.activePair protectedReturn.final
  reconstruct : execution = (p.execution.append slow.execution).append protectedReturn.execution

theorem c_prepared_pair_exists {θ born freshB newbornB forward backward}
    {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
    {freshC newbornC delay ε} {c : ConstructedCBirth t freshC newbornC delay}
    {w : CWeakEntry c} (p : CFirstLearnedBoundary w)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (hd : ∀ F, (3 / 10 : ℝ) ≤ delay F ∧ delay F ≤ 2 / 5) :
    Nonempty (CPreparedPair p) := by
  have hbPair := cBirthPairParameters_physical_box hb
  have hgB : 9 / 5 ≤ Real.exp (p.final.x 0 (.z 2)) ∧ Real.exp (p.final.x 0 (.z 2)) ≤ 2 := by
    rw [p.sender_gains]
    exact c.active_pair_b_gain_bounds
  have hQ : ∀ d ∈ cFirstLearnedPending, p.final.time + 8 ≤ d.due := by
    intro d hdue
    rw [p.date]
    rcases List.mem_append.mp hdue with hdue | hdue
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hdue
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨slow⟩ := port_slow_wire_exists p.learned hbPair hgB w.weak.sender_charge hQ hd
    (by intro F h1 h2; exact cBirthPairRouter_fire delay (by rw [p.date]; norm_num) ⟨h1,h2⟩)
  have hqueue : cFirstLearnedPending = ⟨0,2,p.final.time + 8⟩ :: cPreparedPending := by
    rw [p.date]
    dsimp [cFirstLearnedPending,cPreparedPending]
    rw [sourceTrain_succ]
    norm_num
  have hfuture : ∀ d ∈ cPreparedPending, p.final.time + 8 < d.due := by
    intro d hdue
    rw [p.date]
    rcases List.mem_append.mp hdue with hdue | hdue
    all_goals
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hdue
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨returned⟩ := port_protected_return_exists slow hbPair cPreparedPending hqueue hfuture
  exact ⟨⟨slow,returned,(p.execution.append slow.execution).append returned.execution,rfl⟩⟩

namespace CPreparedPair
variable {θ born freshB newbornB forward backward}
  {t : ConstructedReverseTeaching θ born freshB newbornB forward backward}
  {freshC newbornC delay} {c : ConstructedCBirth t freshC newbornC delay}
  {w : CWeakEntry c} {p : CFirstLearnedBoundary w} (x : CPreparedPair p)

noncomputable abbrev final : Snapshot 2 := x.protectedReturn.final

theorem date : x.final.time = 504 := by rw [x.protectedReturn.date,p.date]; norm_num

theorem pending : x.final.pending = cPreparedPending := x.protectedReturn.pending

theorem pending_length : x.final.pending.length = 37 := by
  rw [x.pending]
  simp [cPreparedPending,sourceTrain]

theorem sender_gains (q : Port) : x.final.x 0 (.z q) = c.activePair.x 0 (.z q) := by
  rw [x.protectedReturn.gains,x.slow.gains,p.sender_gains]

theorem c_gain_target : x.final.x 1 (.z 1) = newbornC.x (.z 1) + 3 / 5 := by
  rw [x.protectedReturn.gains,x.slow.gains,p.c_gain_target]

theorem c_gain_other (q : Port) (hq : q ≠ 1) : x.final.x 1 (.z q) = newbornC.x (.z q) := by
  rw [x.protectedReturn.gains,x.slow.gains,p.learned.gains,p.second.wire.gains,
    w.weak.receiver_gain_other q hq,w.wire.gains,c.active_pair_c_coordinates]

theorem sender_recovery : x.final.x 0 .b = c.activePair.x 0 .b := by
  rw [x.protectedReturn.sender_recovery,x.slow.recovery,p.learned.recovery,p.second.wire.recovery,
    w.weak.recovery,w.wire.recovery]

theorem c_recovery : x.final.x 1 .b = newbornC.x .b + 1 / 10 := by
  rw [x.protectedReturn.receiver_recovery,x.slow.recovery,p.c_recovery]

theorem sender_gain_bounds : 9 / 5 ≤ Real.exp (x.final.x 0 (.z 2)) ∧
    Real.exp (x.final.x 0 (.z 2)) ≤ 2 := by
  rw [x.sender_gains]
  exact c.active_pair_b_gain_bounds

theorem c_gain_bounds : 9 / 5 ≤ Real.exp (x.final.x 1 (.z 1)) ∧
    Real.exp (x.final.x 1 (.z 1)) ≤ 11 / 5 := by
  have hz := newbornC.gain (1 : Port)
  simp only [nominalGain,ite_true] at hz
  rw [x.c_gain_target]
  exact fast_learned_gain_sharp_bounds (by linarith [hz.1]) (by linarith [hz.2])

theorem emissions : x.execution.ledger.emissions =
    [(0,w.sender.fire.final.time),(0,p.second.sender.fire.final.time),
      (1,p.learned.fire.final.time),(0,x.slow.nextCycle.fire.final.time)] := by
  rw [x.reconstruct,Execution.emissions_append,Execution.emissions_append,
    p.emissions,x.slow.emissions,x.protectedReturn.emissions,List.append_nil]
  rfl

theorem sender_emission_count : (x.execution.emissionTimes 0).length = 3 := by
  simp [Execution.emissionTimes,x.emissions]

theorem c_emission_count : (x.execution.emissionTimes 1).length = 1 := by
  simp [Execution.emissionTimes,x.emissions]

theorem complete : CompleteThrough x.execution 504 := by
  have h := x.protectedReturn.complete
  simpa only [CompleteThrough,p.date,show (496 : ℝ) + 8 = 504 by norm_num] using h

end CPreparedPair
end KernelR.Hybrid
