import NativeMultiTokenTarget
import KernelR.HybridFlowCuts
import KernelR.HybridRecoveryTrace

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid

/-- Nominal fabrication parameters at every cell. -/
theorem native_box (N : Nat) : PhysicalBox (nativeParameters N) (1 / 10) :=
  ⟨KernelR.FutureControls.parameters_box.1,
    fun _ q => KernelR.FutureControls.parameters_box.2 0 q⟩

theorem prepared_physical {p : Parameters N} (accepted : p.check = true) :
    PhysicalInvariant (nativeParameters N) (prepared p) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    norm_num [prepared, UpperRegion, auxUpper]
  · intro i q
    obtain ⟨lo, hi⟩ := (of_decide_eq_true accepted : p.Valid).2.1 i
    change (9 / 5 : ℚ) ≤ (3320 / 1000) * p.amplitude i at lo
    change (3321 / 1000 : ℚ) * p.amplitude i ≤ 2 at hi
    have low : 0 < p.amplitude i := by linarith
    have high : p.amplitude i ≤ 1 := by linarith
    have lowR : 0 < (p.amplitude i : ℝ) := by exact_mod_cast low
    have highR : (p.amplitude i : ℝ) ≤ 1 := by exact_mod_cast high
    change (if q = 0 then Real.log (p.amplitude i : ℝ) else 0) ≤ Real.log 4
    split
    · exact Real.log_le_log lowR (highR.trans (by norm_num))
    · exact Real.log_nonneg (by norm_num)
  · intro i
    norm_num [prepared]
  · intro i
    norm_num [prepared]

private theorem flow_gain_before_endpoint {s u : Snapshot N}
    (flow : Flow (nativeParameters N) s u) (i : Fin N) (p : Port)
    (t : ℝ) (inside : t ∈ Set.Icc s.time u.time) :
    flow.path t i (.z p) ≤ u.x i (.z p) := by
  by_cases endpoint : t = u.time
  · rw [endpoint, flow.final]
  · let suffix := flow.suffix inside.1 (lt_of_le_of_ne inside.2 endpoint)
    have bound := suffix.gain_nondecreasing (native_box N) i p u.time ⟨inside.2, le_rfl⟩
    exact bound.trans_eq (congrFun (congrFun flow.final i) (.z p))

/-- The memory coordinates are nondecreasing within and across moves,
so strict headroom at the endpoint bounds each earlier path value. -/
theorem all_below_rail_of_endpoint {route : Router N} {s u : Snapshot N}
    (run : Execution (nativeParameters N) route s u) (endpoint : BelowRail u.x) :
    run.AllStates (fun v => BelowRail v.x) ∧
      run.AllFlows (fun {v w} flow => ∀ t ∈ Set.Icc v.time w.time, BelowRail (flow.path t)) := by
  induction run with
  | nil => exact ⟨endpoint, trivial⟩
  | @cons start cut last step rest ih =>
    have box := native_box N
    have tailRails := ih endpoint
    have cutHeadroom : BelowRail cut.x :=
      ⟨fun i p => (rest.gain_nondecreasing box i p).trans_lt (endpoint.1 i p),
        fun i => (rest.recovery_nondecreasing box i).trans_lt (endpoint.2 i)⟩
    cases step with
    | flow f =>
      have during (t : ℝ) (ht : t ∈ Set.Icc start.time cut.time) : BelowRail (f.path t) :=
        ⟨fun i p => (flow_gain_before_endpoint f i p t ht).trans_lt (cutHeadroom.1 i p),
          fun i => (f.recovery_le_final box i t ht).trans_lt (cutHeadroom.2 i)⟩
      have source := during start.time ⟨le_rfl, f.positive.le⟩
      rw [f.initial] at source
      exact ⟨⟨source, tailRails.1⟩, ⟨during, tailRails.2⟩⟩
    | jump j =>
      have source : BelowRail start.x := by
        rw [← j.physical_continuous]
        exact cutHeadroom
      exact ⟨⟨source, tailRails.1⟩, tailRails.2⟩

/-- Once the witness and a competing trace both saturate the horizon, the
native uniqueness theorem gives agreement of the endpoint and FIRE multiset. -/
theorem native_horizon_unique {p : Parameters N} {last other : Snapshot N}
    (run : Execution (nativeParameters N) (router p) (prepared p) last)
    (comparison : Execution (nativeParameters N) (router p) (prepared p) other)
    (physical : PhysicalInvariant (nativeParameters N) (prepared p))
    (complete : CompleteThrough run (horizon p))
    (comparisonComplete : CompleteThrough comparison (horizon p)) :
    last.ObservationalEq other ∧ run.ledger.emissions.Perm comparison.ledger.emissions :=
  run.observational_unique comparison (native_box N) physical complete comparisonComplete

end NetworkStability.NativeMultiToken
