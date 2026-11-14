import NativeMultiTokenTarget
import KernelR.HybridWeakInputCycleExistence
import KernelR.HybridPrefixBeforeFlow
import KernelR.HybridResidualLatency

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid Set

private theorem raw_active_through {θ : Fin N → KernelR.Hybrid.Parameters}
    {route : Router N} {s u : Snapshot N} (run : Execution θ route s u)
    (i : Fin N) (p : Port) (origin : ℝ) (raw : s.raw i p = some origin)
    (endDate : u.time ≤ origin + 1) :
    run.AllFlows (fun {v _} _ => v.raw i p = some origin) := by
  induction run with
  | nil => trivial
  | @cons s v u move tail ih =>
    cases move with
    | flow f => exact ⟨raw, ih (by rw [f.raw_fixed]; exact raw) endDate⟩
    | jump j =>
      by_cases early : s.time < origin + 1
      · exact ih (j.raw_persists i p origin raw early) endDate
      · have times : v.time = u.time := by
          have h := tail.time_monotone
          rw [j.time_unchanged] at h ⊢
          linarith
        have noFlow {a b : Snapshot N} (e : Execution θ route a b) (eq : a.time = b.time) :
            e.AllFlows (fun {x _} _ => x.raw i p = some origin) := by
          induction e with
          | nil => trivial
          | cons step rest next =>
            cases step with
            | flow f => exact False.elim (by linarith [f.positive, rest.time_monotone])
            | jump k => exact next (k.time_unchanged.trans eq)
        exact noFlow tail times

private theorem nominal_error_after_raw {route : Router N} {s u : Snapshot N}
    {run : Execution (nativeParameters N) route s u} {i : Fin N} {p : Port}
    (cycle : SensorCycle run i p) :
    s.time + 1 < cycle.phases.silentPhase.afterExit.time := by
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  have nominal :
      Real.log 8 / (nativeParameters N i).ls p = (53 / 50 : ℝ) := by
    change Real.log 8 / (Real.log 8 / (53 / 50 : ℝ)) = _
    have pos : 0 < Real.log (8 : ℝ) := Real.log_pos (by norm_num)
    field_simp [ne_of_gt pos]
  have period : auxRemaining (nativeParameters N) mk.afterExit i p .silent = 53 / 50 := by
    have edge : mk.afterExit.x i (.m p) = 4 / 5 := mk.after_charge
    norm_num [auxRemaining, protectedFloor, auxRate, edge, nominal]
  have earlier : s.time ≤ mk.afterExit.time := by
    have m := mk.span.time_monotone
    have t := cycle.trigger.span.time_monotone
    rw [mk.exit.time_unchanged, cycle.trigger.entry.time_unchanged] at *
    linarith
  change s.time + 1 < si.afterExit.time
  rw [si.after_time, period]
  linarith

private theorem nominal_gain_during_raw {route : Router N} {s u : Snapshot N}
    {run : Execution (nativeParameters N) route s u} {i : Fin N} {p : Port}
    (cycle : SensorCycle run i p) :
    run.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, t ≤ s.time + 1 →
      f.path t i (.z p) = s.x i (.z p)) := by
  let tr := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  have htr := tr.span.gain_constant_aux i p .ready (by decide) tr.flows
  have hmk := mk.span.gain_constant_aux i p .mark (by decide) mk.flows
  have hsi := si.span.gain_constant_aux i p .silent (by decide) si.flows
  have hzmk : tr.afterMark.x i (.z p) = s.x i (.z p) := by
    rw [tr.entry.physical_continuous]; exact htr.1
  have hzsi : mk.afterExit.x i (.z p) = s.x i (.z p) := by
    rw [mk.exit.physical_continuous, hmk.1, hzmk]
  let P : ∀ {v w : Snapshot N}, Flow (nativeParameters N) v w → Prop := fun {v w} f =>
    ∀ t ∈ Icc v.time w.time, t ≤ s.time + 1 → f.path t i (.z p) = s.x i (.z p)
  have hPTr : tr.span.AllFlows P := tr.span.allFlows_mono (fun f hf t ht _ => hf t ht) htr.2
  have hPMk : mk.span.AllFlows P := mk.span.allFlows_mono (fun f hf t ht _ => by rw [hf t ht,hzmk]) hmk.2
  have hPSi : si.span.AllFlows P := si.span.allFlows_mono (fun f hf t ht _ => by rw [hf t ht,hzsi]) hsi.2
  have late : s.time + 1 < si.afterExit.time := nominal_error_after_raw cycle
  have hPRest : si.rest.AllFlows P := si.rest.allFlows_mono (fun f hf t ht hu => by
    exact False.elim (by have h := (hf t ht).1; linarith)) si.rest.allFlows_time_bounds
  rw [tr.reconstruct, Execution.allFlows_append]
  refine ⟨hPTr, ?_⟩
  change tr.rest.AllFlows P
  rw [mk.reconstruct, Execution.allFlows_append]
  refine ⟨hPMk, ?_⟩
  change mk.rest.AllFlows P
  rw [si.reconstruct, Execution.allFlows_append]
  exact ⟨hPSi,hPRest⟩

/-- A weak nominal pulse fixes the exact charge at its RAW boundary and
thereafter relaxes from that residual. The next-wave charge is carried
from the actual one-unit pulse. -/
theorem native_training_clock {route : Router N} {s u : Snapshot N}
    (run : Execution (nativeParameters N) route s u)
    (i : Fin N) (p : Port) (pulse : SilentPulse run i p)
    (active : s.raw i p = some s.time) (inactive : ∀ q, q ≠ p → s.raw i q = none)
    (isolated : ∀ q, NoArrivalAt run i q)
    (after : s.time + 1 < u.time) :
    u.x i .q = afterSilent (s.x i .q) (Real.exp (s.x i (.z p))) (u.time - s.time) := by
  obtain ⟨cut⟩ := run.before_flow_cut_exists (s.time + 1) (by linarith) after
  let head := cut.cut
  have headReady : head.MainFlows i .ready :=
    cut.isPrefix.main_flows i .ready (run.allStates_main_flows i .ready pulse.ready_states)
  have raw := raw_active_through head i p s.time active cut.date.le
  have other : head.AllFlows (fun {v _} _ => ∀ q, q ≠ p → v.raw i q = none) := by
    apply head.allFlows_forall (fun q {v _} _ => q ≠ p → v.raw i q = none)
    intro q
    by_cases eq : q = p
    · subst q; exact head.allFlows_mono (fun _ _ h => (h rfl).elim) raw
    · exact head.allFlows_mono (fun _ h _ => h)
        (head.raw_absent_allFlows i q
          (head.raw_absent_of_no_arrival i q (inactive q eq) (cut.isPrefix.no_arrival i q (isolated q))).2)
  have hgain := cut.isPrefix.all_flows
    (fun {v w} f => ∀ t ∈ Icc v.time w.time, t ≤ s.time + 1 → f.path t i (.z p) = s.x i (.z p))
    (fun {v w} f {c} _ hend hf t ht hu => hf t ⟨ht.1, ht.2.trans hend⟩ hu)
    (nominal_gain_during_raw pulse.cycle)
  have drive : head.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t = Real.exp (s.x i (.z p)) * a * Real.exp (-a * (t - s.time))) := by
    refine head.allFlows_mono ?_ (head.allFlows_and raw
      (head.allFlows_and other (head.allFlows_and hgain head.allFlows_time_bounds)))
    intro v w f hf t ht
    have inside : t ∈ Icc v.time w.time := ⟨ht.1, ht.2.le⟩
    have before := (hf.2.2.2 t inside).2.trans cut.date.le
    unfold tailDrive
    rw [Finset.sum_eq_single p]
    · simp only [hf.2.2.1 t inside before, rawTail, hf.1, mul_assoc]
    · intro q _ ne
      simp [rawTail, hf.2.1 q ne]
    · simp
  have atEnd : cut.state.x i .q =
      readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time (s.time + 1) := by
    have upper := head.ready_drive_upper i headReady (s.x i .q) (Real.exp (s.x i (.z p))) s.time
      (by rw [readyPulse_initial]) (head.allFlows_mono (fun _ h t ht => (h t ht).le) drive)
    have lower := head.ready_drive_lower i headReady (s.x i .q) (Real.exp (s.x i (.z p))) s.time
      (by rw [readyPulse_initial]) (head.allFlows_mono (fun _ h t ht => (h t ht).ge) drive)
    rw [← cut.date]
    exact le_antisymm upper lower
  obtain ⟨rest⟩ := cut.isPrefix.continuation
  have quiet : rest.tail.emissionTimes i = [] :=
    (List.append_eq_nil_iff.mp ((rest.emissionTimes i).symm.trans pulse.emissions)).2
  have lastReady : cut.state.main i = .ready := by
    have noFire : head.emissionTimes i = [] :=
      (List.append_eq_nil_iff.mp ((rest.emissionTimes i).symm.trans pulse.emissions)).1
    have start := run.allStates_initial pulse.ready_states
    exact head.allStates_final (head.ready_states_of_no_emissions i start noFire)
  have afterReady := rest.tail.allStates_main_flows i .ready
    (rest.tail.ready_states_of_no_emissions i lastReady quiet)
  have atCut (q : Port) : cut.state.raw i q = none := by
    by_cases eq : q = p
    · subst q
      have allowed := head.raw_allowed_states i p s.time (Or.inr active) (cut.isPrefix.no_arrival i p (isolated p))
      rcases head.allStates_final allowed with absent | same
      · exact absent
      · exact False.elim ((lt_irrefl _) (cut.raw_strict i p s.time same))
    · exact (head.raw_absent_of_no_arrival i q (inactive q eq) (cut.isPrefix.no_arrival i q (isolated q))).1
  have tailQuiet (q : Port) : NoArrivalAt rest.tail i q := by
    intro token mem
    apply isolated q token
    rw [rest.deliveries]
    exact List.mem_append_right _ mem
  have finish := rest.tail.ready_no_current_solution i afterReady (fun q =>
    (rest.tail.raw_absent_of_no_arrival i q (atCut q) (tailQuiet q)).2)
  rw [finish, atEnd, cut.date]
  unfold afterSilent
  have shift : s.time + 1 - s.time = (1 : ℝ) := by ring
  rw [show u.time - (s.time + 1) = u.time - s.time - 1 by ring]
  simp only [readyPulse, shift, sub_zero]

end NetworkStability.NativeMultiToken
