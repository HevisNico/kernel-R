import KernelR.HybridFirstReceiverWeak
import KernelR.HybridQuietExecutionProduct

/-! Recover the next receiver's READY band from its real remaining weak
execution, without assuming the band at the intermediate clock168. -/
namespace KernelR.Hybrid
namespace FirstReceiverWeak
variable {θ born fresh newborn forward backward} {c : ConstructedBirthPreparation θ born}
  {b : ConstructedBBirth c fresh newborn (reciprocalEntryRouter forward backward) constructedBBirthSources}
  {r : FirstWiredArrival b} (w : FirstReceiverWeak r)

theorem cut_raw_none
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) (p : Port) :
    w.cut168.state.raw 0 p = none := by
  by_cases hp : p = 1
  · subst p
    have hs := w.cut168.cut.raw_allowed_states 0 1 r.receiverLocal.time
      (Or.inr r.receiver_local_raw) (w.cut_no_arrival 1)
    rcases w.cut168.cut.allStates_final hs with hn | ha
    · exact hn
    · have hv := (w.cut_raw_valid 0 1 r.receiverLocal.time ha).2
      rw [w.cut168.date] at hv
      change (168 : ℝ) ≤ r.final.time + 1 at hv
      linarith [(r.date_bounds hdelay).2]
  · exact (w.cut168.cut.raw_absent_of_no_arrival 0 p
      (r.receiver_local_raw_other 0 p (Or.inr hp)) (w.cut_no_arrival p)).1

theorem continuation_main_states : w.continuation.AllStates (fun v => v.main 0 = .ready) :=
  w.continuation.ready_states_of_no_emissions 0 w.cut_main_ready
    (by simp [Execution.emissionTimes,w.continuation_emissions])

theorem continuation_raw_absent
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) (p : Port) :
    w.continuation.RawAbsent 0 p :=
  (w.continuation.raw_absent_of_no_arrival 0 p (w.cut_raw_none hdelay p)
    (by simp [NoArrivalAt,w.continuation_deliveries])).2

/-- Only the q solution is needed: no endpoint energy identity or assumed
future trajectory is used to transfer the actual terminal charge band. -/
theorem quiet_after_cut_charge_identity
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) (T : ℝ) :
    (quietAt w.cut168.state T).x 0 .q =
      relax (1 / 2) (1 / 10) (w.weak.final.x 0 .q) w.weak.final.time T := by
  have hsol := w.continuation.ready_no_current_solution 0
    (w.continuation.allStates_main_flows 0 .ready w.continuation_main_states)
    (w.continuation_raw_absent hdelay)
  change relax (1 / 2) (1 / 10) (w.cut168.state.x 0 .q) w.cut168.state.time T = _
  rw [hsol]
  change relax (1 / 2) (1 / 10) (w.cut168.state.x 0 .q) w.cut168.state.time T =
    relax (1 / 2) (1 / 10)
      (relax (1 / 2) (1 / 10) (w.cut168.state.x 0 .q) w.cut168.state.time w.weak.final.time)
      w.weak.final.time T
  exact (relax_restart _ _ _ _ _ _).symm

/-- At a date after the actual full weak return, the explicit quiet suffix
has the real READY charge band, even if its charge at168 was outside it. -/
theorem quiet_after_cut_ready {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5)
    {T : ℝ} (hT : r.final.time + 15 / 2 ≤ T) :
    ReadyCoordinates (quietAt w.cut168.state T) 0 := by
  have hfinish : w.weak.final.time ≤ T := by rw [w.weak.date]; exact hT
  have hstart : w.cut168.state.time ≤ T := w.continuation.time_monotone.trans hfinish
  refine ⟨w.cut_main_ready,?_,?_⟩
  · rw [w.quiet_after_cut_charge_identity hdelay T]
    exact relax_mem_Icc (by norm_num) hfinish w.weak.pulse.coordinates.charge
      (by constructor <;> norm_num)
  · intro p
    have hs := w.cut_aux_rest hb hdelay p
    refine ⟨hs.1,?_⟩
    exact relax_mem_Icc (by norm_num) hstart hs.2 (by constructor <;> norm_num)

theorem quiet_after_cut_main (T : ℝ) : (quietAt w.cut168.state T).main 0 = .ready :=
  w.cut_main_ready

theorem quiet_after_cut_aux {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) (T : ℝ) (p : Port) :
    (quietAt w.cut168.state T).aux 0 p = .ready := (w.cut_aux_rest hb hdelay p).1

theorem quiet_after_cut_raw
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) (T : ℝ) (p : Port) :
    (quietAt w.cut168.state T).raw 0 p = none := w.cut_raw_none hdelay p

theorem quiet_after_cut_gains (T : ℝ) (p : Port) :
    (quietAt w.cut168.state T).x 0 (.z p) = w.cut168.state.x 0 (.z p) := rfl

theorem quiet_after_cut_gain_target {ε} (hb : @PhysicalBox 2 (extendParameters θ fresh) ε)
    (hdelay : ∀ t, (3 / 10 : ℝ) ≤ forward t ∧ forward t ≤ 2 / 5) (T : ℝ) :
    (quietAt w.cut168.state T).x 0 (.z 1) = newborn.x (.z 1) + 3 / 5 := by
  rw [w.quiet_after_cut_gains,w.cut_gain_target hb hdelay]
  change r.final.x 1 (.z 1) + 3 / 5 = _
  rw [r.receiver_gain]

theorem quiet_after_cut_gain_other (T : ℝ) (p : Port) (hp : p ≠ 1) :
    (quietAt w.cut168.state T).x 0 (.z p) = newborn.x (.z p) := by
  rw [w.quiet_after_cut_gains,(w.cut_other_aux p hp).2]
  exact r.receiver_gain p

theorem quiet_after_cut_recovery (T : ℝ) :
    (quietAt w.cut168.state T).x 0 .b = newborn.x .b := by
  change w.cut168.state.x 0 .b = _
  rw [w.cut_recovery]
  exact r.receiver_recovery

end FirstReceiverWeak
end KernelR.Hybrid
