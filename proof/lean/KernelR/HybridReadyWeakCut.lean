import KernelR.HybridNewbornWeakCycle
import KernelR.HybridPrefixBeforeFlow
import KernelR.HybridQuietExecutionProduct
import KernelR.HybridResidualLatency

/-! A narrow READY weak response with its actual interior cut. Newborn
recovery and perturbed charge are retained; no prepared recovery is assumed.
The fast nominal port is covered by the real narrow-input constructor. -/
namespace KernelR.Hybrid
open Set

structure ReadyWeakCut (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port) (C : ℝ) where
  source_ready : ReadyCoordinates s 0
  weak : WeakInputCycle θ (fun _ _ => []) s 0 p
  cut : weak.execution.BeforeFlowCut C
  cut_emissions : cut.cut.ledger.emissions = []
  cut_deliveries : cut.cut.deliveries = []
  cut_main_ready : cut.state.main 0 = .ready
  cut_aux_rest : ∀ q, cut.state.aux 0 q = .ready ∧ RestBand (cut.state.x 0 (.m q))
  cut_raw_none : ∀ q, cut.state.raw 0 q = none
  cut_charge_lower : 1 / 10 - 1 / 100000 ≤ cut.state.x 0 .q
  cut_error_dose : cut.cut.ledger.error 0 p = 3 / 5
  cut_gain_target : cut.state.x 0 (.z p) = s.x 0 (.z p) + 3 / 5
  cut_gain_other : ∀ q, q ≠ p → cut.state.x 0 (.z q) = s.x 0 (.z q)
  cut_recovery : cut.state.x 0 .b = s.x 0 .b
  cut_pending : cut.state.pending = []
  cut_physical : PhysicalInvariant θ cut.state
  cut_raw_valid : RawValid cut.state

/-- Construct a weak response at nominal fast-port gain from its narrow
READY charge, then retain the actual cut after sensor completion. Neither
prepared recovery nor an incoming execution is required. -/
theorem ready_weak_cut_exists {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1) (p : Port)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hs : ReadyCoordinates s 0)
    (hnarrow : s.x 0 .q ≤ 10001 / 100000)
    (hg : Real.exp (s.x 0 (.z p)) ≤ 4 / 3)
    (hz : s.x 0 (.z p) ≤ Real.log (6 / 5) + 1 / 1000)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hEmpty : s.pending = [])
    (C : ℝ) (hSensorDone : s.time + 419 / 300 ≤ C) (hInterior : C < s.time + 15 / 2) :
    Nonempty (ReadyWeakCut θ s p C) := by
  have hready : ∀ j, ReadyCoordinates s j := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hs
  have hother : ∀ j q, j ≠ 0 ∨ q ≠ p → s.raw j q = none := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ho q (by simpa using h)
  obtain ⟨weak⟩ := narrow_weak_input_cycle_exists (route := fun _ _ => []) s hb hf hv 0 p
    hready hnarrow hg hz hr hother (by intro d hd; rw [hEmpty] at hd; contradiction)
  obtain ⟨cut⟩ := weak.execution.before_flow_cut_exists C
    (by linarith) (by rw [weak.date]; exact hInterior)
  have he := (List.append_eq_nil_iff.mp (cut.emissions.symm.trans weak.emissions)).1
  have hd := (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans weak.deliveries)).1
  have hmain := cut.cut.ready_states_of_no_emissions 0 hs.ready
    (by simp [Execution.emissionTimes,he])
  have hno : ∀ q, NoArrivalAt cut.cut 0 q := by intro q; simp [NoArrivalAt,hd]
  obtain ⟨cycle⟩ := cut.cut.sensor_cycle hb hf.region 0 p (hs.auxiliary p).1 hr
    (hs.auxiliary p).2 (by rw [cut.date]; exact hSensorDone)
  have hheadroom : s.x 0 (.z p) + 3 / 5 < Real.log ((θ 0).cap p) := by
    linarith [hb.fast_nominal_headroom 0 p]
  have herror := cycle.total_error_of_invariant hb hf hv hmain hheadroom hr (hno p)
  have haux : ∀ q, cut.state.aux 0 q = .ready ∧ RestBand (cut.state.x 0 (.m q)) := by
    intro q
    by_cases hqp : q = p
    · subst q
      obtain ⟨hm,hmemory⟩ := cycle.final_rest hv hr (hno p)
      exact ⟨hm,by rw [hmemory]; norm_num [RestBand]⟩
    · exact (cut.cut.aux_no_input_rest_band 0 q (hs.auxiliary q).1
        (hs.auxiliary q).2 (ho q hqp) (hno q)).1
  have hraw : ∀ q, cut.state.raw 0 q = none := by
    intro q
    by_cases hqp : q = p
    · subst q
      have hallowed := cut.cut.raw_allowed_states 0 p s.time (Or.inr hr) (hno p)
      rcases cut.cut.allStates_final hallowed with hn | ha
      · exact hn
      · have ht := cut.raw_strict 0 p s.time ha
        linarith
    · exact (cut.cut.raw_absent_of_no_arrival 0 q (ho q hqp) (hno q)).1
  have hpending : cut.state.pending = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hdue
    rcases cut.cut.pending_provenance d hdue with hsource | ⟨event,_,hroute⟩
    · rw [hEmpty] at hsource
      contradiction
    · contradiction
  exact ⟨{
    source_ready := hs, weak := weak, cut := cut
    cut_emissions := he, cut_deliveries := hd
    cut_main_ready := cut.cut.allStates_final hmain, cut_aux_rest := haux, cut_raw_none := hraw
    cut_charge_lower := cut.cut.ready_charge_lower 0 (cut.cut.allStates_main_flows 0 .ready hmain) hs.charge.1
    cut_error_dose := herror.1, cut_gain_target := herror.2
    cut_gain_other := fun q hqp => (cut.cut.aux_no_input_rest_band 0 q (hs.auxiliary q).1
      (hs.auxiliary q).2 (ho q hqp) (hno q)).2
    cut_recovery := cut.cut.recovery_constant_ready 0 (cut.cut.allStates_main_flows 0 .ready hmain)
    cut_pending := hpending, cut_physical := cut.cut.physical_invariant hb hf
    cut_raw_valid := cut.cut.raw_valid hv
  }⟩

namespace ReadyWeakCut
variable {θ s p C} (w : ReadyWeakCut θ s p C)

noncomputable def continuation : Execution θ (fun _ _ => []) w.cut.state w.weak.final :=
  .cons (.flow w.cut.flow) w.cut.rest

theorem continuation_emissions : w.continuation.ledger.emissions = [] :=
  (List.append_eq_nil_iff.mp (w.cut.emissions.symm.trans w.weak.emissions)).2

theorem continuation_deliveries : w.continuation.deliveries = [] :=
  (List.append_eq_nil_iff.mp (w.cut.deliveries.symm.trans w.weak.deliveries)).2

theorem continuation_main_states : w.continuation.AllStates (fun v => v.main 0 = .ready) :=
  w.continuation.ready_states_of_no_emissions 0 w.cut_main_ready
    (by simp [Execution.emissionTimes,w.continuation_emissions])

theorem continuation_raw_absent (q : Port) : w.continuation.RawAbsent 0 q :=
  (w.continuation.raw_absent_of_no_arrival 0 q (w.cut_raw_none q)
    (by simp [NoArrivalAt,w.continuation_deliveries])).2

/-- Match only the charge coordinate to the remaining actual weak path.
No equality of endpoint energies or replacement of the carried charge is used. -/
theorem quiet_after_cut_charge_identity (T : ℝ) :
    (quietAt w.cut.state T).x 0 .q =
      relax (1 / 2) (1 / 10) (w.weak.final.x 0 .q) w.weak.final.time T := by
  have hsol := w.continuation.ready_no_current_solution 0
    (w.continuation.allStates_main_flows 0 .ready w.continuation_main_states)
    w.continuation_raw_absent
  change relax (1 / 2) (1 / 10) (w.cut.state.x 0 .q) w.cut.state.time T = _
  rw [hsol]
  change relax (1 / 2) (1 / 10) (w.cut.state.x 0 .q) w.cut.state.time T =
    relax (1 / 2) (1 / 10)
      (relax (1 / 2) (1 / 10) (w.cut.state.x 0 .q) w.cut.state.time w.weak.final.time)
      w.weak.final.time T
  exact (relax_restart _ _ _ _ _ _).symm

theorem quiet_after_cut_ready {T : ℝ} (hT : w.weak.final.time ≤ T) (j : Fin 1) :
    ReadyCoordinates (quietAt w.cut.state T) j := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  have hstart : w.cut.state.time ≤ T := w.continuation.time_monotone.trans hT
  refine ⟨w.cut_main_ready,?_,?_⟩
  · rw [w.quiet_after_cut_charge_identity T]
    exact relax_mem_Icc (by norm_num) hT w.weak.pulse.coordinates.charge
      (by constructor <;> norm_num)
  · intro q
    refine ⟨(w.cut_aux_rest q).1,?_⟩
    exact relax_mem_Icc (by norm_num) hstart (w.cut_aux_rest q).2 (by constructor <;> norm_num)

/-- The retained birth-band lower charge persists during forward quiet
relaxation. A perturbed newborn may start below exact rest. -/
theorem quiet_after_cut_charge_lower {T : ℝ} (hT : w.cut.state.time ≤ T) :
    1 / 10 - 1 / 100000 ≤ (quietAt w.cut.state T).x 0 .q := by
  have hq : w.cut.state.x 0 .q ≤ 1 := by
    have h := w.cut.before_guards.1 0
    rw [w.cut_main_ready] at h
    exact h.le
  change 1 / 10 - 1 / 100000 ≤
    relax (1 / 2) (1 / 10) (w.cut.state.x 0 .q) w.cut.state.time T
  exact (relax_mem_Icc (by norm_num) hT ⟨w.cut_charge_lower,hq⟩
    (by constructor <;> norm_num)).1

/-- Any source recovery band, including the newborn band near0.08, is
transported unchanged. No prepared-recovery band is imposed. -/
theorem quiet_after_cut_recovery_band (T lower upper : ℝ)
    (hb : lower ≤ s.x 0 .b ∧ s.x 0 .b ≤ upper) :
    lower ≤ (quietAt w.cut.state T).x 0 .b ∧
      (quietAt w.cut.state T).x 0 .b ≤ upper := by
  change lower ≤ w.cut.state.x 0 .b ∧ w.cut.state.x 0 .b ≤ upper
  rw [w.cut_recovery]
  exact hb

theorem quiet_after_cut_raw (T : ℝ) (j : Fin 1) (q : Port) :
    (quietAt w.cut.state T).raw j q = none := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact w.cut_raw_none q

theorem quiet_after_cut_gain_target (T : ℝ) :
    (quietAt w.cut.state T).x 0 (.z p) = s.x 0 (.z p) + 3 / 5 := w.cut_gain_target

theorem quiet_after_cut_gain_other (T : ℝ) (q : Port) (hq : q ≠ p) :
    (quietAt w.cut.state T).x 0 (.z q) = s.x 0 (.z q) := w.cut_gain_other q hq

theorem quiet_after_cut_recovery (T : ℝ) :
    (quietAt w.cut.state T).x 0 .b = s.x 0 .b := w.cut_recovery

theorem complete : CompleteThrough w.cut.cut C := w.cut.complete

end ReadyWeakCut
end KernelR.Hybrid
