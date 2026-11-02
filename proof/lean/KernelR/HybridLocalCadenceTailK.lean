import KernelR.HybridLocalCadenceHighJitterTrain
import KernelR.HybridCadenceSecondStrongResponse
import KernelR.HybridCadenceMixedNextSource

/-! The autonomous tail starts at an already-arrived second strong source.
Its date, port, regular tail length and final quiet date are parameters. The
actual second strong, mixed response, high train and all arrivals are retained;
no execution or emitted calendar is a premise. -/
namespace KernelR.Hybrid

private theorem regular_high_jitter_schedule (p : Port) (S : ℝ) (n : ℕ) :
    CadenceHighJitterSchedule S
      ((sourceTrain (0 : Fin 1) p (S + 4) 4 n).map Delivery.due)
      (S + 4 * ((n : ℝ) + 1)) := by
  induction n generalizing S with
  | zero =>
    simp only [sourceTrain,List.ofFn_zero,List.map_nil,CadenceHighJitterSchedule,Nat.cast_zero]
    linarith
  | succ n ih =>
    rw [sourceTrain_succ,List.map_cons]
    constructor
    · change S + 19 / 5 ≤ S + 4
      linarith
    · have hT : S + 4 * (((n + 1 : ℕ) : ℝ) + 1) = (S + 4) + 4 * ((n : ℝ) + 1) := by
        push_cast
        ring
      rw [hT]
      exact ih (S + 4)

private theorem source_train_due_tokens (p : Port) (S : ℝ) (n : ℕ) :
    ((sourceTrain (0 : Fin 1) p S 4 n).map Delivery.due).map
      (fun time => (⟨0,p,time⟩ : Delivery 1)) = sourceTrain 0 p S 4 n := by
  simp only [sourceTrain,List.map_ofFn]
  rfl

structure LocalCadenceTailK (θ : Fin 1 → Parameters) (source : Snapshot 1)
    (p : Port) (n : ℕ) (terminal : ℝ) where
  tail_pos : 1 ≤ n
  second : CadenceSecondStrongResponse θ source p
    (sourceTrain 0 p (source.time + 8) 4 (n + 1))
  mixed : CadenceMixedResponse θ second.final p
  sourceHigh : CadenceMixedNextSource mixed
    (sourceTrain 0 p (source.time + 12) 4 n)
  high : LocalCadenceHighJitterTrain θ sourceHigh.final p
    ((sourceTrain (0 : Fin 1) p (source.time + 12) 4 n).map Delivery.due)
    (source.time + 12 + 4 * (n : ℝ))
  source_high_date : sourceHigh.final.time = source.time + 8
  high_date : high.final.time = source.time + 12 + 4 * (n : ℝ)
  final : Snapshot 1
  wait : Execution θ (fun _ _ => []) high.final final
  final_state : final = quietAt high.final terminal
  execution : Execution θ (fun _ _ => []) source final
  reconstruct : execution = second.execution.append
    (sourceHigh.execution.append (high.execution.append wait))
  date : final.time = terminal
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j q, final.raw j q = none
  pending : final.pending = []
  gain_target : final.x 0 (.z p) = source.x 0 (.z p) + 3 / 5
  gain_other : ∀ q, q ≠ p → final.x 0 (.z q) = source.x 0 (.z q)
  recovery_gain : final.x 0 .b = source.x 0 .b + 1 / 10
  emission_count : (execution.emissionTimes 0).length = n + 2
  calendar : execution.emissionTimes 0 = second.fire.final.time :: high.execution.emissionTimes 0
  deliveries : execution.deliveries = sourceTrain 0 p (source.time + 4) 4 (n + 2)
  wait_emissions : wait.ledger.emissions = []
  wait_deliveries : wait.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution terminal

/-- The section already includes its actual active source. All remaining
n+2 inputs are present in its queue; n=K-8 gives the K-6 tail FIREs after the
six-input leaf prefix. The quiet endpoint may be chosen freely after the train. -/
theorem local_cadence_tail_k_exists {θ ε} (hb : PhysicalBox θ ε)
    (source : Snapshot 1) (p : Port) (n : ℕ) (terminal : ℝ) (hn : 1 ≤ n)
    (hf : PhysicalInvariant θ source) (hv : RawValid source)
    (hs : CadenceReadyCoordinates source 0 (3 / 10)) (hq : source.x 0 .q = 1 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ source.x 0 (.z p) ∧
      source.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hB : 27999 / 100000 ≤ source.x 0 .b ∧ source.x 0 .b ≤ 28001 / 100000)
    (hr : source.raw 0 p = some source.time) (ho : ∀ q, q ≠ p → source.raw 0 q = none)
    (hqueue : source.pending = sourceTrain 0 p (source.time + 4) 4 (n + 2))
    (hterminal : source.time + 12 + 4 * (n : ℝ) < terminal) :
    Nonempty (LocalCadenceTailK θ source p n terminal) := by
  have h4 : source.time + 4 + 4 = source.time + 8 := by ring
  have h8 : source.time + 8 + 4 = source.time + 12 := by ring
  have hHead : source.pending = ⟨0,p,source.time + 4⟩ ::
      sourceTrain 0 p (source.time + 8) 4 (n + 1) := by
    rw [hqueue,sourceTrain_succ,h4]
  obtain ⟨second⟩ := cadence_second_strong_response_exists hb source p hf hv hs hq hz hB hr ho
    (sourceTrain 0 p (source.time + 8) 4 (n + 1)) hHead
    (by intro d hd; obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
        change source.time + 4 < source.time + 8 + 4 * (k.val : ℝ)
        nlinarith [Nat.cast_nonneg (α := ℝ) k.val])
  have hSecondB : 27999 / 100000 ≤ second.final.x 0 .b ∧ second.final.x 0 .b ≤ 28001 / 100000 := by
    rw [second.recovery]
    exact hB
  have hSecondZ : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ second.final.x 0 (.z p) ∧
      second.final.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [second.gains]
    exact hz
  have hFuture : ∀ d ∈ second.final.pending, second.final.time + 4 ≤ d.due := by
    intro d hd
    rw [second.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [second.date]
    change source.time + 4 + 4 ≤ source.time + 8 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨mixed⟩ := cadence_mixed_response_exists hb second.final p second.physical second.raw_valid
    second.main_slow second.charge hSecondB (fun q => ⟨second.auxiliary 0 q,second.rest q⟩)
    hSecondZ second.raw_active second.raw_other hFuture
  have hMixedHead : second.final.pending = ⟨0,p,second.final.time + 4⟩ ::
      sourceTrain 0 p (source.time + 12) 4 n := by
    rw [second.date,h4]
    calc
      second.final.pending = sourceTrain 0 p (source.time + 8) 4 (n + 1) := second.pending
      _ = ⟨0,p,source.time + 8⟩ :: sourceTrain 0 p (source.time + 12) 4 n := by
        rw [sourceTrain_succ,h8]
  obtain ⟨input⟩ := cadence_mixed_next_source_exists mixed hb second.physical second.raw_valid
    (sourceTrain 0 p (source.time + 12) 4 n) hMixedHead
    (by intro d hd; obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd; rw [second.date]
        change source.time + 4 + 4 < source.time + 12 + 4 * (k.val : ℝ)
        nlinarith [Nat.cast_nonneg (α := ℝ) k.val])
  have hInputDate : input.final.time = source.time + 8 := by rw [input.date,second.date,h4]
  let dates := (sourceTrain (0 : Fin 1) p (source.time + 12) 4 n).map Delivery.due
  have hHighQueue : input.final.pending = dates.map (fun time => (⟨0,p,time⟩ : Delivery 1)) := by
    rw [input.pending]
    exact (source_train_due_tokens p (source.time + 12) n).symm
  have hSchedule : CadenceHighJitterSchedule input.final.time dates
      (source.time + 12 + 4 * (n : ℝ)) := by
    have h := regular_high_jitter_schedule p input.final.time n
    rw [hInputDate,h8] at h
    convert h using 1; ring
  obtain ⟨high⟩ := local_cadence_high_jitter_train_exists hb input.final p dates
    (source.time + 12 + 4 * (n : ℝ)) input.physical input.raw_valid input.coordinates input.charge_lower
    (input.high_gain_bounds hSecondZ) input.recovery_band input.raw_active input.raw_other hHighQueue hSchedule
  have hWait : high.final.time < terminal := by rw [high.date]; exact hterminal
  have hMain : ∀ j, high.final.main j = .ready := fun j => (high.ready j).ready
  have hAux : ∀ j q, high.final.aux j q = .ready := fun j q => ((high.ready j).auxiliary q).1
  have hCharge : ∀ j, high.final.x j .q < 1 := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rw [high.charge]
    norm_num
  have hSensor : ∀ j q, high.final.x j (.m q) < 1 := by
    intro j q
    linarith [((high.ready j).auxiliary q).2.2]
  have hNoPending : ∀ d ∈ high.final.pending, terminal < d.due := by rw [high.pending]; simp
  let flow := quietFlow (θ := θ) high.final hWait hMain hAux high.raw_none hCharge hSensor
    (fun d hd => (hNoPending d hd).le)
  let wait : Execution θ (fun _ _ => []) high.final (quietAt high.final terminal) :=
    .cons (.flow flow) (.nil _)
  let execution := second.execution.append (input.execution.append (high.execution.append wait))
  have hWaitEm : wait.ledger.emissions = [] := rfl
  have hWaitDel : wait.deliveries = [] := rfl
  have hCalendar : execution.emissionTimes 0 = second.fire.final.time :: high.execution.emissionTimes 0 := by
    rw [Execution.emissionTimes_append,Execution.emissionTimes_append,Execution.emissionTimes_append]
    have hSecond : second.execution.emissionTimes 0 = [second.fire.final.time] := by
      simp [Execution.emissionTimes,second.emissions]
    have hInput : input.execution.emissionTimes 0 = [] := by simp [Execution.emissionTimes,input.emissions]
    have hQuiet : wait.emissionTimes 0 = [] := by simp [Execution.emissionTimes,hWaitEm]
    rw [hSecond,hInput,hQuiet,List.append_nil,List.nil_append]
    rfl
  have hPartition : sourceTrain (0 : Fin 1) p (source.time + 4) 4 (n + 2) =
      [⟨0,p,source.time + 4⟩,⟨0,p,source.time + 8⟩] ++ sourceTrain 0 p (source.time + 12) 4 n := by
    rw [sourceTrain_succ,h4,sourceTrain_succ,h8]
    rfl
  obtain ⟨_,hc⟩ := quiet_complete_exists (θ := θ) (route := fun _ _ => []) high.final hWait
    hMain hAux high.raw_none hCharge hSensor hNoPending
  refine ⟨{
    tail_pos := hn, second := second, mixed := mixed, sourceHigh := input, high := high
    source_high_date := hInputDate, high_date := high.date
    final := quietAt high.final terminal, wait := wait, final_state := rfl
    execution := execution, reconstruct := rfl, date := rfl
    ready := fun j => quietAt_ready_coordinates high.final j (high.ready j) hWait.le
    charge := ?_, raw_none := high.raw_none, pending := high.pending
    gain_target := ?_, gain_other := ?_, recovery_gain := ?_
    emission_count := ?_, calendar := hCalendar, deliveries := ?_
    wait_emissions := hWaitEm, wait_deliveries := hWaitDel
    physical := wait.physical_invariant hb high.physical, raw_valid := wait.raw_valid high.raw_valid
    complete := by simpa only [CompleteThrough] using hc
  }⟩
  · change relax (1 / 2) (1 / 10) (high.final.x 0 .q) high.final.time terminal = 1 / 10
    rw [high.charge]
    simp [relax]
  · change high.final.x 0 (.z p) = _
    rw [high.gains,input.gain_target,second.gains]
  · intro q hq
    change high.final.x 0 (.z q) = _
    rw [high.gains,input.gain_other q hq,second.gains]
  · change high.final.x 0 .b = _
    rw [high.recovery,input.recovery_gain,second.recovery]
  · rw [hCalendar,List.length_cons,high.emission_count]
    simp [dates,sourceTrain]
  · rw [Execution.deliveries_append,Execution.deliveries_append,Execution.deliveries_append,
      second.deliveries,input.deliveries,high.deliveries,hWaitDel,List.append_nil,second.date,h4]
    rw [show dates.map (fun time => (⟨0,p,time⟩ : Delivery 1)) =
      sourceTrain 0 p (source.time + 12) 4 n from source_train_due_tokens p (source.time + 12) n]
    exact hPartition.symm

namespace LocalCadenceTailK
variable {θ : Fin 1 → Parameters} {source : Snapshot 1} {p : Port} {n : ℕ} {terminal : ℝ}
  (t : LocalCadenceTailK θ source p n terminal)

/-- The second strong source has exact rest charge, so its actual scalar
root uses that section's own three-dose gain. -/
theorem second_fire_latency (hq : source.x 0 .q = 1 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ source.x 0 (.z p) ∧
      source.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000) :
    t.second.fire.latency = restLatency (Real.exp (source.x 0 (.z p))) := by
  have hg := cadence_three_dose_gain_bounds hz
  apply restLatency_unique ⟨hg.1,by linarith [hg.2]⟩
  · exact ⟨by linarith [t.second.fire.early],t.second.fire.deadline.le⟩
  · simpa only [hq,readyPulse,add_sub_cancel_left,sub_zero] using t.second.fire.response_root

theorem second_fire_date (hq : source.x 0 .q = 1 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ source.x 0 (.z p) ∧
      source.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000) :
    t.second.fire.final.time = source.time + restLatency (Real.exp (source.x 0 (.z p))) := by
  rw [t.second.fire.date,t.second_fire_latency hq hz]

theorem second_fire_window (hq : source.x 0 .q = 1 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ source.x 0 (.z p) ∧
      source.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000) :
    source.time + 13 / 20 < t.second.fire.final.time ∧
      t.second.fire.final.time < source.time + 33 / 50 := by
  rw [t.second_fire_date hq hz]
  have h := restLatency_three_doses_bounds hz.1 hz.2
  constructor <;> linarith [h.1,h.2]

/-- The first high FIRE retains the real mixed-response residual latency. -/
theorem high_first_date :
    t.high.first.final.time = source.time + 8 + t.high.first.latency := by
  rw [t.high.first.date]
  change t.sourceHigh.final.time + t.high.first.latency = _
  rw [t.source_high_date]

theorem high_first_window :
    source.time + 8 + 4 / 25 < t.high.first.final.time ∧
      t.high.first.final.time < source.time + 8 + 13 / 50 := by
  have h := t.high.first.window
  change t.sourceHigh.final.time + 4 / 25 < t.high.first.final.time ∧
    t.high.first.final.time < t.sourceHigh.final.time + 13 / 50 at h
  rw [t.source_high_date] at h
  exact h

theorem high_gain_own : t.sourceHigh.final.x 0 (.z p) = source.x 0 (.z p) + 3 / 5 := by
  rw [t.sourceHigh.gain_target,t.second.gains]

theorem high_recovery_own : t.sourceHigh.final.x 0 .b = source.x 0 .b + 1 / 10 := by
  rw [t.sourceHigh.recovery_gain,t.second.recovery]

theorem high_first_latency_le_rest : t.high.first.latency ≤
    highRestLatency (Real.exp (t.sourceHigh.final.x 0 (.z p))) :=
  t.high.first_latency_le_rest

/-- The n regular high dates use the same cell's own exact-rest root. -/
theorem high_calendar : t.high.execution.emissionTimes 0 = t.high.first.final.time ::
    (sourceTrain (0 : Fin 1) p (source.time + 12) 4 n).map
      (fun d => d.due + highRestLatency (Real.exp (t.sourceHigh.final.x 0 (.z p)))) := by
  simpa only [List.map_map,Function.comp_def] using t.high.calendar

theorem calendar_exact : t.execution.emissionTimes 0 =
    t.second.fire.final.time :: t.high.first.final.time ::
      (sourceTrain (0 : Fin 1) p (source.time + 12) 4 n).map
        (fun d => d.due + highRestLatency (Real.exp (t.sourceHigh.final.x 0 (.z p)))) := by
  rw [t.calendar,t.high_calendar]

theorem calendar_with_roots (hq : source.x 0 .q = 1 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ source.x 0 (.z p) ∧
      source.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000) :
    t.execution.emissionTimes 0 =
      (source.time + restLatency (Real.exp (source.x 0 (.z p)))) ::
        (source.time + 8 + t.high.first.latency) ::
          List.ofFn (fun k : Fin n => source.time + 12 + 4 * (k.val : ℝ) +
            highRestLatency (Real.exp (t.sourceHigh.final.x 0 (.z p)))) := by
  have h := t.calendar_exact
  rw [t.second_fire_date hq hz,t.high_first_date] at h
  simpa only [sourceTrain,List.map_ofFn,Function.comp_def] using h

end LocalCadenceTailK

end KernelR.Hybrid
