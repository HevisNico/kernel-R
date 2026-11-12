import Coincidence.CoincidenceNetworkContract
import KernelR.HybridWeakInputErrorExistence
import KernelR.HybridErrorCompletion
import KernelR.HybridNominalSilent

/-! Local witnesses for the registered coincidence task. The read
addresses a queued port chosen before training starts. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

/-- The execution through admission of the scheduled read pulse. -/
structure CoincidencePrepared (θ : Fin 1 → Parameters) (gains : Port → ℝ)
    (trained tested : Port) (readTime : ℝ) where
  state : Snapshot 1
  execution : ParameterExecution θ (fun _ _ => [])
    (coincidenceTrialStart gains trained tested readTime) state
  time_eq : state.time = readTime
  ready : ReadoutReady state tested
  physical : PhysicalInvariant θ state
  other_gain : tested ≠ trained → state.x 0 (.z tested) = gains tested
  emissions : execution.emissions = []

/-- Change the port of the still-pending read. The physical training
trajectory and the state immediately before read admission are retained. -/
theorem TrainingRead.prepare_coincidence {θ gains trained upper lower level readTime}
    (run : TrainingRead θ 0 gains trained upper lower level readTime)
    (config : (θ 0).thresholds = trainingThresholds trained upper lower level)
    (positive : 0 < readTime) (tested : Port) :
    Nonempty (CoincidencePrepared θ gains trained tested readTime) := by
  let h := run.handoff
  let edit (d : Delivery 1) := if d.due = readTime then {d with port := tested} else d
  have dates (d : Delivery 1) : (edit d).due = d.due := by
    unfold edit
    split <;> rfl
  have birthFixed : edit (errorReadDelivery trained 0) = errorReadDelivery trained 0 := by
    simp [edit, errorReadDelivery, ne_of_lt positive]
  have editRead : edit (errorReadDelivery trained readTime) = errorReadDelivery tested readTime := by
    simp [edit, errorReadDelivery]
  obtain ⟨mapped, labels⟩ := map_execution_pending (run.parameterPrefix config) edit dates
    (by
      intro d hd
      rw [run.parameterPrefix_inputs config, List.mem_singleton] at hd
      exact hd ▸ birthFixed)
  have sourceEq : mapPending edit (trainingStart 0 gains trained readTime) =
      coincidenceTrialStart gains trained tested readTime := by
    simp [mapPending, trainingStart, coincidenceTrialStart, birthFixed, editRead]
  let s := mapPending edit h.beforeRead
  have queue : s.pending = [errorReadDelivery tested readTime] := by
    change run.errorStart.pending.map edit = _
    rw [h.queued]
    simp [show (0 : ℝ) + readTime = readTime by ring, editRead]
  have time : s.time = readTime := by change (0 : ℝ) + readTime = readTime; ring
  have noneRaw (q : Port) : s.raw 0 q = none := h.error_raw_empty q
  let admitted := {setRaw s 0 tested (some s.time) with pending := []}
  let arrive : ParameterJump θ (fun _ _ => []) s admitted :=
    .arrive _ (errorReadDelivery tested readTime) [] [] queue time.symm (noneRaw tested)
  have data : admitted.x = h.readStart.x ∧ admitted.main = h.readStart.main ∧
      admitted.aux = h.readStart.aux := by
    rw [h.read_start_eq]
    exact ⟨rfl, rfl, rfl⟩
  let head : ParameterExecution θ (fun _ _ => [])
      (coincidenceTrialStart gains trained tested readTime) s := sourceEq ▸ mapped
  let ex := head.append (.cons (.jump arrive) (.nil _))
  have headLabels : head.emissions = [] := by
    have sourceCast {a b c : Snapshot 1} (e : ParameterExecution θ (fun _ _ => []) a c)
        (eq : a = b) :
        (eq ▸ e : ParameterExecution θ (fun _ _ => []) b c).emissions = e.emissions := by
      subst b
      rfl
    change (sourceEq ▸ mapped : ParameterExecution θ (fun _ _ => []) _ _).emissions = []
    rw [sourceCast, labels, run.parameterPrefix_emissions config]
  have noEm : ex.emissions = [] := by
    change (head.append (.cons (.jump arrive) (.nil _))).emissions = []
    rw [parameter_emissions_append, headLabels]
    rfl
  have physical : PhysicalInvariant θ admitted := by
    have initial := h.decision.physical_start
    exact ⟨by simpa only [UpperRegion, data.1, data.2.2] using initial.region,
      by simpa only [data.1] using initial.gain_cap,
      by simpa only [data.1] using initial.recovery_cap,
      by simpa only [data.1] using initial.reserve⟩
  refine ⟨⟨admitted, ex, time, ?_, physical, ?_, noEm⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · rw [data.2.1]; exact h.ready_at_read.main
    · rw [data.1]; exact h.ready_at_read.charge
    · rw [data.2.2]; exact h.ready_at_read.aux
    · rw [data.1]; exact h.ready_at_read.rest
    · simp [admitted, setRaw]
    · intro i q neq
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have hq := neq.resolve_left (not_not_intro rfl)
      simp [admitted, setRaw, hq, noneRaw]
  · intro neq
    rw [data.1]
    exact run.other_gains_at_read tested neq

private structure QuietReadTrace (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (p : Port) (T : ℝ) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) s final
  time_eq : final.time = T
  aux : ∀ i q, final.aux i q = .ready
  sensor : ∀ i q, final.x i (.m q) < 1
  raw : ∀ i q, final.raw i q = none
  queue : final.pending = []
  arrivals : execution.deliveries = []
  drive : execution.AllFlows (fun {a b} f => ∀ t ∈ Ico a.time b.time,
    tailDrive a (f.path t) 0 t ≤ (4 / 3) * KernelR.Hybrid.a * Real.exp (-KernelR.Hybrid.a * (t - s.time)))

/-- Construct the nominal local mode sequence on the tested port.
Realized FIRE guards are supplied by the subthreshold bound below. -/
private theorem quiet_read_trace {θ ε s p T} (box : @PhysicalBox 1 θ ε)
    (ready : ReadoutReady s p) (physical : PhysicalInvariant θ s)
    (gain : Real.exp (s.x 0 (.z p)) ≤ 6 / 5) (horizon : s.time + 419 / 300 ≤ T) :
    Nonempty (QuietReadTrace θ s p T) := by
  let route : Router 1 := fun _ _ => []
  have margin (t : ℝ) (ht : s.time ≤ t) :
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t ≤ 24 / 25 := by
    have h := readyPulse_uniform_bound ready.charge.2 (by norm_num) gain (by norm_num) ht
    linarith
  have early (t : ℝ) (ht : s.time ≤ t) (_ : t ≤ s.time + 1 / 10) :
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t < 1 := by linarith [margin t ht]
  obtain ⟨mark⟩ := first_input_mark_of_response_margin_until_exists s box 0 p ready.main ready.aux
    ready.raw ready.otherRaw (by intro i; rw [Subsingleton.elim i 0]; linarith [ready.charge.2])
    (by intro i q; linarith [(ready.rest i q).2]) early (ready.rest 0 p) (by simp [ready.empty])
  obtain ⟨silent⟩ := mark.first_silent_of_response_margin_until_exists box early (by simp [ready.empty])
  obtain ⟨entry⟩ := silent.first_error_exists_of_margin route box margin (by simp [ready.empty])
  let headTrace := (silent.execution route).append entry.execution
  have phys := headTrace.physical_invariant box physical
  have empty : entry.final.pending = [] := entry.pending.trans ready.empty
  have logGain : s.x 0 (.z p) ≤ Real.log (6 / 5) := by
    have h := Real.log_le_log (Real.exp_pos _) gain
    rwa [Real.log_exp] at h
  have cap : entry.final.x 0 (.z p) + 8 * (entry.final.x 0 (.m p) - 1 / 40) <
      Real.log ((θ 0).cap p) := by
    change entry.beforeError.x 0 (.z p) + 8 * (entry.beforeError.x 0 (.m p) - 1 / 40) < _
    rw [entry.gain_preserved, entry.sensor_before]
    linarith [box.fast_nominal_headroom 0 p]
  have date : entry.final.time + errorTailDuration θ entry.final 0 p =
      s.time + mark.latency + auxCycleDuration (θ 0) p := by
    rw [entry.error_date_exact, silent.date]
    simp only [FirstInputMark.silentDate, errorTailDuration, entry.sensor_charge]
    norm_num only [show (40 : ℝ) * (1 / 10) = 4 by norm_num]
    dsimp [auxCycleDuration]
    ring
  have schedule := box.first_cycle_schedule 0 p ⟨mark.early, mark.deadline⟩
  have afterRaw : s.time + 1 < entry.final.time + errorTailDuration θ entry.final 0 p := by
    rw [date]
    linarith [schedule.2.2.2.2.1]
  have beforeHorizon : entry.final.time + errorTailDuration θ entry.final 0 p < T := by
    rw [date]
    linarith [schedule.2.2.2.2.2]
  have charge : 1 / 40 < entry.final.x 0 (.m p) := by rw [entry.sensor_charge]; norm_num
  have complete : Nonempty (ErrorCompletion θ route entry.final 0 p) := by
    rcases entry.raw_option with ⟨active, activeTime⟩ | ⟨expired, _⟩
    · exact error_completion_with_raw_tail box entry.final 0 p phys entry.main_ready entry.initialmode
        entry.aux_other s.time active entry.raw_other charge entry.sensor_charge.le cap
        (entry.error_date_lower box).le activeTime afterRaw entry.charge_margin entry.main_below
        entry.aux_below (by simp [empty])
    · have noRaw (i : Fin 1) (q : Port) : entry.final.raw i q = none := by
        rw [Subsingleton.elim i 0]
        by_cases eq : q = p
        · rwa [eq]
        · exact entry.raw_other 0 q (Or.inr eq)
      exact error_completion_without_raw box entry.final 0 p phys entry.main_ready entry.initialmode
        entry.aux_other noRaw charge entry.sensor_charge.le cap entry.main_below entry.aux_below
        (by simp [empty])
  obtain ⟨finish⟩ := complete
  have finishEarly : finish.final.time < T := finish.date ▸ beforeHorizon
  have finishEmpty : finish.final.pending = [] := finish.pending.trans empty
  let wait := quietFlow (θ := θ) finish.final finishEarly finish.main_ready finish.aux_ready finish.raw_none
    finish.main_below finish.aux_below (by simp [finishEmpty])
  let trace : Execution θ route s (quietAt finish.final T) :=
    headTrace.append (finish.execution.append (.cons (.flow wait) (.nil _)))
  have arrivals : trace.deliveries = [] := by
    simp [trace, headTrace, FirstInputSilent.execution, FirstInputMark.execution, FirstInputSilent.continuation,
      Execution.deliveries_append, Execution.deliveries, Move.deliveries, Jump.deliveries,
      entry.deliveries, finish.deliveries]
  have noArrival (q : Port) : NoArrivalAt trace 0 q := by simp [NoArrivalAt, arrivals]
  obtain ⟨cycle⟩ := trace.sensor_cycle box physical.1 0 p (ready.aux 0 p) ready.raw (ready.rest 0 p) horizon
  have drive := cycle.single_drive_upper box (4 / 3) (by norm_num)
    (fun z h => fast_nominal_raw_gain_upper (by linarith)) ready.raw
    (fun q neq => ready.otherRaw 0 q (Or.inr neq)) noArrival
  refine ⟨⟨quietAt finish.final T, trace, rfl, finish.aux_ready, ?_, finish.raw_none, finishEmpty,
    arrivals, drive⟩⟩
  intro i q
  exact relax_lt (by norm_num) finishEarly.le (finish.aux_below i q) (by norm_num)

private theorem quiet_read_jump {θ trained upper lower level s u}
    (j : @Jump 1 (fun _ _ => []) s u)
    (config : (θ 0).thresholds = trainingThresholds trained upper lower level)
    (main : s.main 0 = .ready) (mainAfter : u.main 0 = .ready)
    (passive : s.aux 0 trained = .ready) :
    ∃ k : ParameterJump θ (fun _ _ => []) s u, k.emissions = [] := by
  cases j with
  | fire i mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [setMain] at mainAfter
  | fastEnd i mode hit =>
    rw [Subsingleton.elim i 0, main] at mode
    cases mode
  | reopen i mode hit =>
    rw [Subsingleton.elim i 0, main] at mode
    cases mode
  | mark i q mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact ⟨.mark _ 0 q mode (by rw [config]; exact hit), rfl⟩
  | silent i q mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact ⟨.silent _ 0 q mode (by rw [config]; exact hit), rfl⟩
  | error i q mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have neq : q ≠ trained := by intro eq; subst q; rw [passive] at mode; cases mode
    exact ⟨.error _ 0 q mode (by rw [config]; simpa [trainingThresholds, neq] using hit), rfl⟩
  | auxReady i q mode hit =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have neq : q ≠ trained := by intro eq; subst q; rw [passive] at mode; cases mode
    exact ⟨.auxReady _ 0 q mode (by rw [config]; simpa [trainingThresholds, neq] using hit), rfl⟩
  | arrive d before after queue due free =>
    exact ⟨.arrive _ d before after queue due free, rfl⟩
  | rawEnd i q origin active due => exact ⟨.rawEnd _ i q origin active due, rfl⟩

private theorem quiet_read_realize {θ trained upper lower level origin initial s u}
    (e : @Execution 1 θ (fun _ _ => []) s u)
    (config : (θ 0).thresholds = trainingThresholds trained upper lower level)
    (main : e.AllStates (fun x => x.main 0 = .ready))
    (passive : e.AllStates (fun x => x.aux 0 trained = .ready))
    (drive : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) 0 t ≤ (4 / 3) * a * Real.exp (-a * (t - origin))))
    (after : origin ≤ s.time) (start : s.x 0 .q ≤ readyPulse initial (4 / 3) origin s.time)
    (bound : ∀ t, origin ≤ t → readyPulse initial (4 / 3) origin t < level) :
    ∃ run : ParameterExecution θ (fun _ _ => []) s u,
      run.emissions = [] ∧ u.x 0 .q < level := by
  induction e with
  | nil => exact ⟨.nil _, rfl, start.trans_lt (bound _ after)⟩
  | @cons v w u move rest ih =>
    cases move with
    | flow f =>
      have envelope := f.ready_drive_upper 0 main.1 initial (4 / 3) origin start drive.1
      have flow : ParameterFlow θ v w := {
        toFlowDynamics := f.toFlowDynamics
        guards := by
          intro t ht
          have stock := f.guards t ht
          constructor
          · intro i
            rw [Subsingleton.elim i 0, main.1]
            change f.path t 0 .q < (θ 0).thresholds.fire
            rw [config]
            exact (envelope t ⟨ht.1, ht.2.le⟩).trans_lt (bound _ (after.trans ht.1))
          · intro i q
            rw [Subsingleton.elim i 0]
            dsimp only
            rw [config]
            have h := stock.2 0 q
            by_cases eq : q = trained
            · subst q
              simpa [passive.1, trainingThresholds, Thresholds.nominal] using h
            · cases mode : v.aux 0 q <;>
                simpa [mode, trainingThresholds, Thresholds.nominal, eq] using h
      }
      have finish : w.x 0 .q ≤ readyPulse initial (4 / 3) origin w.time := by
        rw [← f.final]
        exact envelope _ ⟨f.positive.le, le_rfl⟩
      obtain ⟨tail, noFire, charge⟩ := ih main.2 passive.2 drive.2
        (after.trans f.positive.le) finish
      exact ⟨.cons (.flow flow) tail, noFire, charge⟩
    | jump j =>
      obtain ⟨jump, labels⟩ := quiet_read_jump j config main.1
        (rest.allStates_initial main.2) passive.1
      obtain ⟨tail, noFire, charge⟩ := ih main.2 passive.2 drive
        (j.time_unchanged.symm ▸ after) (by rwa [j.physical_continuous, j.time_unchanged])
      exact ⟨.cons (.jump jump) tail, by simp [ParameterExecution.emissions, labels, noFire], charge⟩

private theorem quiet_read_complete {θ ε s trained tested upper lower level T}
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds trained upper lower level)
    (wrong : tested ≠ trained) (fireFloor : 97 / 100 ≤ level)
    (ready : ReadoutReady s tested) (physical : PhysicalInvariant θ s)
    (gain : Real.exp (s.x 0 (.z tested)) ≤ 6 / 5) (horizon : s.time + 419 / 300 ≤ T) :
    ∃ u, ∃ run : ParameterExecution θ (fun _ _ => []) s u,
      ParameterCompleteThrough run T ∧ run.emissions = [] := by
  obtain ⟨trace⟩ := quiet_read_trace box ready physical gain horizon
  have noArr : NoArrivalAt trace.execution 0 trained := by simp [NoArrivalAt, trace.arrivals]
  have passive := trace.execution.aux_ready_without_input_band 0 trained (ready.aux 0 trained)
    (ready.rest 0 trained).2 (ready.otherRaw 0 trained (Or.inr wrong.symm)) noArr
  have bound (t : ℝ) (ht : s.time ≤ t) : readyPulse (s.x 0 .q) (4 / 3) s.time t < level := by
    have h := readyPulse_uniform_bound ready.charge.2 (by norm_num) (by rfl : (4 / 3 : ℝ) ≤ 4 / 3)
      (by norm_num) ht
    linarith
  have nominalBound (t : ℝ) (ht : s.time ≤ t) : readyPulse (s.x 0 .q) (4 / 3) s.time t < 1 := by
    have h := readyPulse_uniform_bound ready.charge.2 (by norm_num) (by rfl : (4 / 3 : ℝ) ≤ 4 / 3)
      (by norm_num) ht
    linarith
  have main := (trace.execution.ready_of_upper_drive 0 (ready.main 0) (4 / 3) trace.drive nominalBound).1
  obtain ⟨run, noFire, charge⟩ := quiet_read_realize trace.execution config main passive trace.drive
    le_rfl (by rw [readyPulse_initial]) bound
  refine ⟨trace.final, run, ⟨trace.time_eq, ?_, by simp [trace.queue]⟩, noFire⟩
  have readyFinal := trace.execution.allStates_final main
  intro v
  refine ⟨?_⟩
  intro j
  cases j with
  | fire i _ hit =>
    rw [Subsingleton.elim i 0, config] at hit
    exact (ne_of_lt charge) hit
  | fastEnd i mode _ => rw [Subsingleton.elim i 0, readyFinal] at mode; cases mode
  | reopen i mode _ => rw [Subsingleton.elim i 0, readyFinal] at mode; cases mode
  | mark i p _ hit =>
    rw [Subsingleton.elim i 0, config] at hit
    exact (ne_of_lt (trace.sensor 0 p)) hit
  | silent i p mode _ => rw [trace.aux] at mode; cases mode
  | error i p mode _ => rw [trace.aux] at mode; cases mode
  | auxReady i p mode _ => rw [trace.aux] at mode; cases mode
  | arrive d before after queue due free => simp [trace.queue] at queue
  | rawEnd i p origin active due => simp [trace.raw] at active

/-- For a read on an untrained port, construct an actual complete run
from birth through the observation horizon. Its report list is empty. -/
theorem TrainingRead.wrong_port_complete {θ ε gains trained tested upper lower level readTime T}
    (run : TrainingRead θ 0 gains trained upper lower level readTime)
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds trained upper lower level)
    (wrong : tested ≠ trained) (fireFloor : 97 / 100 ≤ level)
    (positive : 0 < readTime) (gain : Real.exp (gains tested) ≤ 6 / 5)
    (horizon : readTime + 419 / 300 ≤ T) :
    ∃ u, ∃ e : ParameterExecution θ (fun _ _ => [])
      (coincidenceTrialStart gains trained tested readTime) u,
      ParameterCompleteThrough e T ∧ e.emissionTimes 0 = [] := by
  obtain ⟨prepared⟩ := run.prepare_coincidence config positive tested
  obtain ⟨u, tail, done, reports⟩ := quiet_read_complete (T := T) box config wrong fireFloor prepared.ready
    prepared.physical (by rw [prepared.other_gain wrong]; exact gain)
    (by rw [prepared.time_eq]; exact horizon)
  refine ⟨u, prepared.execution.append tail, done, ?_⟩
  simp [ParameterExecution.emissionTimes, parameter_emissions_append, prepared.emissions, reports]

/-- Wrong-port trials of the registered 0.01 benchmark have an actual
complete execution through time 20 with an empty FIRE list. -/
theorem wrong_port_exit_001_benchmark {θ ε gains trained tested readTime e f}
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds trained ((θ 0).thresholds.error trained)
      ((θ 0).thresholds.auxReady trained) (θ 0).thresholds.fire)
    (errors : Exit001TimingBox e f)
    (hi : |(θ 0).thresholds.error trained - 1 / 10| ≤ e / 10)
    (lo : |(θ 0).thresholds.auxReady trained - 1 / 100| ≤ e / 40)
    (fire : |(θ 0).thresholds.fire - 1| ≤ f)
    (read : readTime ∈ Icc (333 / 20 : ℝ) (347 / 20))
    (trainGain : Real.exp (gains trained) = 6 / 5)
    (testGain : Real.exp (gains tested) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) (wrong : tested ≠ trained) :
    ∃ u, ∃ run : ParameterExecution θ (fun _ _ => [])
      (coincidenceTrialStart gains trained tested readTime) u,
      ParameterCompleteThrough run 20 ∧ run.emissionTimes 0 = [] := by
  obtain ⟨certificate, _⟩ := training_read_exit_001_certificate (time := 0) box errors hi lo fire
    read.1 trainGain caps
  have fMax : f ≤ 3 / 100 := by rcases errors with h | h | h <;> linarith [h.2]
  have fireFloor : 97 / 100 ≤ (θ 0).thresholds.fire := by linarith [(abs_le.mp fire).1]
  exact certificate.wrong_port_complete box config wrong fireFloor (by linarith [read.1])
    testGain (by linarith [read.2])

end RecursiveLearning.Native
