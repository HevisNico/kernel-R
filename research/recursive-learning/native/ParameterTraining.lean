import TrainingRead
import ParameterFuturePort
import KernelR.HybridParameterUniversalExecution

/-! The existing estimates construct a trajectory of the fixed-parameter
kernel. The realized thresholds are read from the cell's parameters. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set MeasureTheory

/-- The experiment varies FIRE and the selected port's two ERROR
thresholds. The other guards retain their nominal levels. -/
noncomputable def trainingThresholds (p : Port) (upper lower level : ℝ) : Thresholds :=
  { Thresholds.nominal with
    fire := level
    error := Function.update Thresholds.nominal.error p upper
    auxReady := Function.update Thresholds.nominal.auxReady p lower }

theorem guards_ready {θ : Fin 1 → Parameters} {s : Snapshot 1} {x : Values 1}
    {p upper lower level} (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (main : s.main 0 = .ready) (charge : x 0 .q < level)
    (sensor : ∀ q, match s.aux 0 q with
      | .ready => x 0 (.m q) < 1
      | .mark => 4 / 5 < x 0 (.m q)
      | .silent => (if q = p then upper else 1 / 10) < x 0 (.m q)
      | .error => (if q = p then lower else 1 / 40) < x 0 (.m q)) :
    ThresholdGuards (fun i => (θ i).thresholds) s x := by
  constructor
  · intro i
    rw [Subsingleton.elim i 0]
    simpa [main, config, trainingThresholds] using charge
  · intro i q
    rw [Subsingleton.elim i 0]
    have h := sensor q
    cases mode : s.aux 0 q <;>
      simpa [mode, config, trainingThresholds, Thresholds.nominal, Function.update_apply] using h

theorem native_aux_guards {s : Snapshot 1} {x : Values 1} {p : Port} {upper lower : ℝ}
    (stock : BeforeGuards s x)
    (silent : s.aux 0 p = .silent → upper < x 0 (.m p))
    (error : s.aux 0 p = .error → lower < x 0 (.m p)) :
    ∀ q, match s.aux 0 q with
      | .ready => x 0 (.m q) < 1
      | .mark => 4 / 5 < x 0 (.m q)
      | .silent => (if q = p then upper else 1 / 10) < x 0 (.m q)
      | .error => (if q = p then lower else 1 / 40) < x 0 (.m q) := by
  intro q
  have h := stock.2 0 q
  by_cases hq : q = p
  · subst q
    cases mode : s.aux 0 p <;> simp_all
  · cases mode : s.aux 0 q <;> simpa [mode, hq] using h

noncomputable def parameterMarkSilent {θ : Fin 1 → Parameters} {s : Snapshot 1}
    {p upper lower level}
    {f : FirstInputMark θ s 0 p} (g : FirstInputSilent f)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (first : ∀ t ∈ Ico s.time (s.time + f.latency), f.flow.path t 0 .q < level)
    (second : ∀ t ∈ Ico f.final.time g.final.time, g.flow.path t 0 .q < level) :
    ParameterExecution θ (fun _ _ => []) s g.final := by
  let f₁ : ParameterFlow θ s (readyInputEnd θ s 0 p (s.time + f.latency)) := {
    toFlowDynamics := f.flow.toFlowDynamics
    guards := fun t ht => guards_ready config (f.main_ready 0) (first t ht)
      (native_aux_guards (f.flow.guards t ht)
        (by rw [f.aux_ready]; simp) (by rw [f.aux_ready]; simp))
  }
  have mode : f.final.aux 0 p = .mark := by simp [FirstInputMark.final, setAux]
  let f₂ : ParameterFlow θ f.final f.silentBefore := {
    toFlowDynamics := g.flow.toFlowDynamics
    guards := fun t ht => guards_ready config (f.main_ready 0) (second t ht)
      (native_aux_guards (g.flow.guards t ht) (by rw [mode]; simp) (by rw [mode]; simp))
  }
  have mark : ParameterJump θ (fun _ _ => [])
      (readyInputEnd θ s 0 p (s.time + f.latency)) f.final :=
    .mark _ 0 p (f.aux_ready 0 p) (by rw [config]; exact f.sensor_threshold)
  have silent : ParameterJump θ (fun _ _ => []) f.silentBefore g.final :=
    .silent _ 0 p mode (by rw [config]; exact g.threshold)
  exact .cons (.flow f₁) (.cons (.jump mark) (.cons (.flow f₂) (.cons (.jump silent) (.nil _))))

noncomputable def parameterSilentLeg {θ s p origin upper level stop}
    (leg : TrainingSilentLeg θ s p origin upper level stop) {lower}
    (config : (θ 0).thresholds = trainingThresholds p upper lower level) :
    ParameterFlow θ s (readyProtectedEnd θ s 0 p .silent origin stop) where
  positive := leg.positive
  path := readyProtectedValues θ s 0 p .silent origin
  initial := readyProtectedValues_initial _ _ _ _ _
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := leg.continuous
  integrable := leg.integrable
  integral_eq := leg.integral
  mark_integrable := by intro i q; simp [markAct, leg.main]
  guards := by
    intro t ht
    apply guards_ready config (leg.main 0) (leg.main_guard t ht)
    intro q
    by_cases hq : q = p
    · subst q
      simpa [leg.mode] using leg.sensor_guard t ht
    · simpa [leg.other_modes q hq] using leg.other_guard t ht q hq
  raw_support := by
    intro i q o h
    by_cases address : i = 0 ∧ q = p
    · obtain ⟨rfl, rfl⟩ := address
      exact leg.raw_support o (leg.raw.symm.trans h)
    · rw [leg.other_raw i q (by tauto)] at h
      cases h
  pending_urgent := leg.pending

noncomputable def parameterTrainingTrace {θ p upper lower level s u}
    (trace : TrainingTrace θ p upper lower level s u)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level) :
    ParameterExecution θ (fun _ _ => []) s u := by
  induction trace with
  | nil s => exact .nil s
  | silent leg _ ih => exact .cons (.flow (parameterSilentLeg leg config)) ih
  | enter mode contact _ ih =>
    exact .cons (.jump (.error _ 0 p mode (by rw [config]; simpa [trainingThresholds] using contact))) ih
  | expire active due _ ih => exact .cons (.jump (.rawEnd _ 0 p _ active due)) ih
  | liveError leg _ ih =>
    let f : ParameterFlow θ _ _ := {
      toFlowDynamics := leg.flow.toFlowDynamics
      guards := fun t ht => guards_ready config leg.main (leg.main_guard t ht)
        (native_aux_guards (leg.flow.guards t ht) (by rw [leg.mode]; simp)
          (fun _ => leg.sensor_guard t ht))
    }
    exact .cons (.flow f) ih

private noncomputable def parameterRead {θ s p upper lower level}
    (read : TolerantSnapshotDecision θ s p true level)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (silent : ∀ t ∈ Icc read.silent.final.time read.stop,
      upper < readyProtectedValues θ read.silent.final 0 p .silent (some s.time) t 0 (.m p)) :
    ParameterExecution θ (fun _ _ => []) s read.final := by
  let g := read.silent
  let last := readyProtectedEnd θ g.final 0 p .silent (some s.time) read.stop
  let f : ParameterFlow θ g.final last := {
    positive := read.leg.positive
    path := readyProtectedValues θ g.final 0 p .silent (some s.time)
    initial := readyProtectedValues_initial _ _ _ _ _
    final := rfl
    main_fixed := rfl
    aux_fixed := rfl
    raw_fixed := rfl
    queue_fixed := rfl
    continuous := fun i c => (read.leg.continuous i c).continuousOn
    integrable := read.leg.integrable
    mark_integrable := by intro i q; simp [markAct, g.main_ready]
    integral_eq := read.leg.integral
    guards := by
      intro t ht
      apply guards_ready config (g.main_ready 0) (read.leg.main_guard t ht)
      intro q
      by_cases hq : q = p
      · subst q
        simpa [g.aux_silent] using silent t ⟨ht.1, ht.2.le⟩
      · have h := read.leg.aux_guards t ⟨ht.1, ht.2.le⟩ 0 q
        rw [g.aux_other 0 q (Or.inr hq)] at h ⊢
        exact h
    raw_support := by
      intro i q o h
      by_cases address : i = 0 ∧ q = p
      · obtain ⟨rfl, rfl⟩ := address
        rw [g.raw_active, Option.some.injEq] at h
        subst o
        exact ⟨read.leg.live.1, read.leg.live.2.le⟩
      · rw [g.raw_other i q (by tauto)] at h
        cases h
    pending_urgent := by
      intro d hd
      change d ∈ g.final.pending at hd
      rw [read.leg.empty] at hd
      cases hd
  }
  have fire : ParameterJump θ (fun _ _ => []) last read.final := by
    have hit : last.x 0 .q = (θ 0).thresholds.fire := by rw [config]; exact read.outcome.2.2.1
    simpa [TolerantSnapshotDecision.final, last, setMain] using
      (ParameterJump.fire (route := fun _ _ => []) last 0 (g.main_ready 0) hit)
  exact (parameterMarkSilent g config read.before_mark read.before_silent).append
    (.cons (.flow f) (.cons (.jump fire) (.nil _)))

/-- Snapshot immediately before the scheduled read admission. -/
noncomputable def ErrorReadHandoff.beforeRead {θ s p m lower level readTime}
    (run : ErrorReadHandoff θ s p m lower level readTime) : Snapshot 1 :=
  quietAt (setAux {s with time := run.span.stop, x := run.span.path run.span.stop}
    0 p .ready) readTime

private def parameterReadArrival {θ s p m lower level readTime}
    (run : ErrorReadHandoff θ s p m lower level readTime) :
    ParameterJump θ (fun _ _ => [])
      run.beforeRead run.readStart := by
  rw [run.read_start_eq]
  exact .arrive _ (errorReadDelivery p readTime) [] [] run.queued rfl (run.error_raw_empty p)

private noncomputable def parameterHandoffPrefix {θ s p m upper lower level readTime}
    (run : ErrorReadHandoff θ s p m lower level readTime)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level) :
    ParameterExecution θ (fun _ _ => []) s run.beforeRead := by
  let span := run.span
  let boundary : Snapshot 1 := {s with time := span.stop, x := span.path span.stop}
  let reopened := setAux boundary 0 p .ready
  have same : span.start = s := run.start_eq
  have main : s.main 0 = .ready := same ▸ span.ready
  have mode : s.aux 0 p = .error := same ▸ span.error
  let flow : ParameterFlow θ s boundary := {
    positive := same ▸ span.positive
    path := span.path
    initial := by simpa only [same] using span.initial
    final := rfl
    main_fixed := rfl
    aux_fixed := rfl
    raw_fixed := rfl
    queue_fixed := rfl
    continuous := by simpa only [same] using span.continuous
    integrable := by simpa only [same] using span.integrable
    mark_integrable := by intro i q; rw [Subsingleton.elim i 0]; simp [markAct, main]
    integral_eq := by simpa only [same] using span.integral_eq
    guards := by
      intro t ht
      apply guards_ready config main (run.error_main_guard t ht)
      intro q
      by_cases eq : q = p
      · subst q
        have h := span.sensor_guard t (same.symm ▸ ht)
        simpa [mode] using h
      · obtain ⟨hm, hq⟩ := run.error_other_guards t ht q eq
        simpa [hm] using hq
    raw_support := by intro i q o h; rw [Subsingleton.elim i 0, run.error_raw_empty] at h; cases h
    pending_urgent := fun d hd => (run.error_pending_later d hd).le
  }
  have rMain : reopened.main 0 = .ready := main
  have rAux (q : Port) : reopened.aux 0 q = .ready := by
    by_cases eq : q = p
    · subst q; simp [reopened, setAux]
    · have hm := (run.error_other_guards s.time ⟨le_rfl, flow.positive⟩ q eq).1
      simpa [reopened, setAux, eq] using hm
  let wait : ParameterFlow θ reopened (quietAt reopened readTime) := {
    toFlowDynamics := run.quiet.toFlowDynamics
    guards := fun t ht => guards_ready config rMain (run.quiet_main_guard t ht)
      (native_aux_guards (run.quiet.guards t ht) (by rw [rAux]; simp) (by rw [rAux]; simp))
  }
  have reopen : ParameterJump θ (fun _ _ => []) boundary reopened :=
    .auxReady _ 0 p mode (by rw [config]; simpa [trainingThresholds] using span.charge_out)
  exact .cons (.flow flow) (.cons (.jump reopen) (.cons (.flow wait) (.nil _)))

private noncomputable def parameterHandoff {θ s p m upper lower level readTime}
    (run : ErrorReadHandoff θ s p m lower level readTime)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (silent : ∀ t ∈ Icc run.decision.silent.final.time run.decision.stop,
      upper < readyProtectedValues θ run.decision.silent.final 0 p .silent
        (some run.readStart.time) t 0 (.m p)) :
    ParameterExecution θ (fun _ _ => []) s run.decision.final := by
  exact (parameterHandoffPrefix run config).append
    (.cons (.jump (parameterReadArrival run)) (parameterRead run.decision config silent))

/-- The estimates in the training certificate produce an execution of
the realized-parameter semantics itself. -/
noncomputable def TrainingRead.parameterExecution {θ time gains p upper lower level delay}
    (run : TrainingRead θ time gains p upper lower level delay)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level) :
    ParameterExecution θ (fun _ _ => []) (trainingStart time gains p delay) run.handoff.decision.final := by
  let train : ParameterJump θ (fun _ _ => []) (trainingStart time gains p delay) (trainingAdmitted time gains p delay) :=
    .arrive _ (errorReadDelivery p time) [] [errorReadDelivery p (time + delay)] rfl rfl rfl
  exact .cons (.jump train) ((parameterMarkSilent run.silent config run.pre_mark run.pre_silent).append
    ((parameterTrainingTrace run.trace config).append
      (parameterHandoff run.handoff config run.read_silent_guard)))

/-- Training and the quiet wait, ending just before the read delivery. -/
noncomputable def TrainingRead.parameterPrefix {θ time gains p upper lower level delay}
    (run : TrainingRead θ time gains p upper lower level delay)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level) :
    ParameterExecution θ (fun _ _ => []) (trainingStart time gains p delay) run.handoff.beforeRead := by
  let train : ParameterJump θ (fun _ _ => []) (trainingStart time gains p delay) (trainingAdmitted time gains p delay) :=
    .arrive _ (errorReadDelivery p time) [] [errorReadDelivery p (time + delay)] rfl rfl rfl
  exact .cons (.jump train) ((parameterMarkSilent run.silent config run.pre_mark run.pre_silent).append
    ((parameterTrainingTrace run.trace config).append (parameterHandoffPrefix run.handoff config)))

/-- The first read FIRE is a complete horizon of the parameterized run.
The sensor and raw pulse remain strictly between their adjacent events. -/
theorem TrainingRead.parameterComplete {θ time gains p upper lower level delay}
    (run : TrainingRead θ time gains p upper lower level delay)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (fireFloor : 19 / 20 ≤ level) :
    ParameterCompleteThrough (run.parameterExecution config) run.handoff.decision.stop := by
  let read := run.handoff.decision
  let g := read.silent
  let t := read.stop
  let last := readyProtectedEnd θ g.final 0 p .silent (some run.handoff.readStart.time) t
  let final := setMain last 0 .fast
  have htime : final.time = t := rfl
  have pending : final.pending = [] := read.leg.empty
  have sensorBound := run.read_silent_guard t ⟨read.leg.positive.le, le_rfl⟩
  have guards : ThresholdGuards (fun i => (θ i).thresholds) final final.x := by
    constructor
    · intro i
      rw [Subsingleton.elim i 0]
      have mode : final.main 0 = .fast := by simp [final, setMain]
      have hit : final.x 0 .q = level := read.outcome.2.2.1
      have lower : (1 / 4 : ℝ) < final.x 0 .q := by linarith
      simpa [mode, config, trainingThresholds] using lower
    · intro i q
      rw [Subsingleton.elim i 0]
      by_cases hq : q = p
      · subst q
        have mode : final.aux 0 p = .silent := g.aux_silent
        rw [mode]
        change (θ 0).thresholds.error p < final.x 0 (.m p)
        rw [config]
        simpa only [trainingThresholds, Function.update_self] using
          (show upper < final.x 0 (.m p) from sensorBound)
      · have mode : final.aux 0 q = .ready := g.aux_other 0 q (Or.inr hq)
        have h := read.leg.aux_guards t ⟨read.leg.positive.le, le_rfl⟩ 0 q
        rw [g.aux_other 0 q (Or.inr hq)] at h
        rw [mode]
        change final.x 0 (.m q) < (θ 0).thresholds.mark q
        rw [config]
        exact h
  have future : ∀ d ∈ final.pending, t < d.due := by simp [pending]
  refine ⟨htime, final.no_parameter_jump guards (by simpa only [htime] using future) ?_, future⟩
  intro i q origin h
  rw [Subsingleton.elim i 0] at h
  by_cases hq : q = p
  · subst q
    change g.final.raw 0 p = some origin at h
    rw [g.raw_active, Option.some.injEq] at h
    rw [htime, ← h]
    exact read.leg.live.2
  · change g.final.raw 0 q = some origin at h
    rw [g.raw_other 0 q (Or.inr hq)] at h
    cases h

/-- The two-pulse experiment has a complete parameterized execution
for either full fabrication box, using the realized threshold fields. -/
theorem training_read_in_parameters {θ ε time gains p}
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds p ((θ 0).thresholds.error p)
      ((θ 0).thresholds.auxReady p) (θ 0).thresholds.fire)
    (threshold : 19 / 20 ≤ (θ 0).thresholds.fire ∧ (θ 0).thresholds.fire ≤ 21 / 20)
    (hi : |(θ 0).thresholds.error p - 1 / 10| ≤ 1 / 200)
    (lo : |(θ 0).thresholds.auxReady p - 1 / 40| ≤ 1 / 800)
    (gain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    ∃ run : TrainingRead θ time gains p ((θ 0).thresholds.error p)
        ((θ 0).thresholds.auxReady p) (θ 0).thresholds.fire,
      ParameterCompleteThrough (run.parameterExecution config) run.handoff.decision.stop := by
  obtain ⟨run⟩ := training_read_exists box threshold hi lo gain caps
  exact ⟨run, run.parameterComplete config threshold.1⟩

theorem training_threshold_bounds {θ : Fin 1 → Parameters} {p upper lower level}
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (threshold : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (hi : |upper - 1 / 10| ≤ 1 / 200) (lo : 0 ≤ lower) :
    ParameterThresholdBounds θ := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp hi
  constructor
  · intro i
    rw [Subsingleton.elim i 0, config]
    change level ≤ 11 / 10
    linarith [threshold.2]
  · intro i
    rw [Subsingleton.elim i 0, config]
    norm_num [trainingThresholds]
  · intro i
    rw [Subsingleton.elim i 0, config]
    change (1 / 4 : ℝ) < level
    linarith [threshold.1]
  · intro i
    rw [Subsingleton.elim i 0, config]
    norm_num [trainingThresholds]
  · intro i q
    rw [Subsingleton.elim i 0, config]
    norm_num [trainingThresholds]
  · intro i q
    rw [Subsingleton.elim i 0, config]
    norm_num [trainingThresholds]
  · intro i q
    rw [Subsingleton.elim i 0, config]
    by_cases h : q = p
    · subst q
      simp only [trainingThresholds, Function.update_self]
      linarith
    · norm_num [trainingThresholds, Function.update_of_ne h]
  · intro i q
    rw [Subsingleton.elim i 0, config]
    by_cases h : q = p
    · subst q
      simp only [trainingThresholds, Function.update_self]
      linarith
    · norm_num [trainingThresholds, Function.update_of_ne h]

theorem training_initial_invariant {θ time gains p delay}
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    ParameterPhysicalInvariant θ (trainingStart time gains p delay) := by
  constructor
  · intro i
    norm_num [trainingStart, toleranceStartOn]
  · intro i q
    norm_num [trainingStart, toleranceStartOn]
  · intro i q
    rw [Subsingleton.elim i 0]
    exact caps q
  · intro i
    norm_num [trainingStart, toleranceStartOn]
  · intro i
    norm_num [trainingStart, toleranceStartOn]

theorem parameter_emissions_append {n θ route s u v}
    (e : @ParameterExecution n θ route s u) (f : ParameterExecution θ route u v) :
    (e.append f).emissions = e.emissions ++ f.emissions := by
  induction e with
  | nil => rfl
  | cons m rest ih =>
    simp only [ParameterExecution.append, ParameterExecution.emissions_cons, ih, List.append_assoc]

private theorem parameterMarkSilent_emissions {θ : Fin 1 → Parameters} {s : Snapshot 1}
    {p upper lower level} {f : FirstInputMark θ s 0 p} (g : FirstInputSilent f)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (first : ∀ t ∈ Ico s.time (s.time + f.latency), f.flow.path t 0 .q < level)
    (second : ∀ t ∈ Ico f.final.time g.final.time, g.flow.path t 0 .q < level) :
    (parameterMarkSilent g config first second).emissions = [] := by
  rfl

private theorem parameterTrace_emissions {θ s u p upper lower level}
    (trace : TrainingTrace θ p upper lower level s u)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level) :
    (parameterTrainingTrace trace config).emissions = [] := by
  induction trace with
  | nil => rfl
  | silent leg rest ih => exact ih
  | enter mode hit rest ih => exact ih
  | expire active due rest ih => exact ih
  | liveError leg rest ih => exact ih

private theorem emissions_of_ready_to_fast {θ route s u}
    (j : @ParameterJump 1 θ route s u)
    (before : s.main 0 = .ready) (after : u.main 0 = .fast) :
    j.emissions = [(0, s.time)] := by
  cases j with
  | fire i _ _ =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  | fastEnd i _ _ =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [setMain] at after
  | reopen i _ _ =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [setMain] at after
  | _ => simp_all [setRaw, setAux]

private theorem emissions_if_main_fixed {θ route s u}
    (j : @ParameterJump 1 θ route s u) (fixed : u.main 0 = s.main 0) :
    j.emissions = [] := by
  cases j with
  | fire i mode _ =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [setMain, mode] at fixed
  | _ => rfl

private theorem parameterRead_emissions {θ s p upper lower level}
    (read : TolerantSnapshotDecision θ s p true level)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (silent : ∀ t ∈ Icc read.silent.final.time read.stop,
      upper < readyProtectedValues θ read.silent.final 0 p .silent (some s.time) t 0 (.m p)) :
    (parameterRead read config silent).emissions = [(0, read.stop)] := by
  unfold parameterRead
  simp only [parameter_emissions_append, parameterMarkSilent_emissions, List.nil_append,
    ParameterExecution.emissions,
    List.append_nil]
  apply emissions_of_ready_to_fast
  · exact read.silent.main_ready 0
  · simp [TolerantSnapshotDecision.final, setMain]

private theorem parameterHandoff_emissions {θ s p m upper lower level readTime}
    (run : ErrorReadHandoff θ s p m lower level readTime)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (silent : ∀ t ∈ Icc run.decision.silent.final.time run.decision.stop,
      upper < readyProtectedValues θ run.decision.silent.final 0 p .silent
        (some run.readStart.time) t 0 (.m p)) :
    (parameterHandoff run config silent).emissions = [(0, run.decision.stop)] := by
  have labels : (parameterReadArrival run).emissions = [] := by
    apply emissions_if_main_fixed
    rw [run.read_start_eq]
    rfl
  unfold parameterHandoff
  rw [parameter_emissions_append,
    show (parameterHandoffPrefix run config).emissions = [] from rfl]
  simp only [List.nil_append, ParameterExecution.emissions_cons, ParameterMove.emissions,
    parameterRead_emissions]
  rw [labels]
  rfl

private theorem parameterTrace_inputs {θ s u p upper lower level}
    (trace : TrainingTrace θ p upper lower level s u)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level) :
    executionInputs (parameterTrainingTrace trace config) = [] := by
  induction trace with
  | nil => rfl
  | silent leg rest ih => exact ih
  | enter mode hit rest ih => exact ih
  | expire active due rest ih => exact ih
  | liveError leg rest ih => exact ih

/-- Only the training input has been delivered at the end of the prefix. -/
theorem TrainingRead.parameterPrefix_inputs {θ time gains p upper lower level delay}
    (run : TrainingRead θ time gains p upper lower level delay)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level) :
    executionInputs (run.parameterPrefix config) = [errorReadDelivery p time] := by
  simp only [TrainingRead.parameterPrefix, executionInputs, jumpInputs, executionInputs_append,
    parameterTrace_inputs, parameterHandoffPrefix, parameterMarkSilent]
  rfl

theorem TrainingRead.parameterPrefix_emissions {θ time gains p upper lower level delay}
    (run : TrainingRead θ time gains p upper lower level delay)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level) :
    (run.parameterPrefix config).emissions = [] := by
  have labels := parameterMarkSilent_emissions run.silent config run.pre_mark run.pre_silent
  simp only [TrainingRead.parameterPrefix, ParameterExecution.emissions_cons, ParameterMove.emissions,
    parameter_emissions_append, labels, parameterTrace_emissions, parameterHandoffPrefix, List.nil_append]
  rfl

/-- The constructed execution records one actual FIRE, at the read's
first upward contact. -/
theorem TrainingRead.parameterEmissionTimes {θ time gains p upper lower level delay}
    (run : TrainingRead θ time gains p upper lower level delay)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level) :
    (run.parameterExecution config).emissionTimes 0 = [run.handoff.decision.stop] := by
  have prefixLabels := parameterMarkSilent_emissions run.silent config run.pre_mark run.pre_silent
  unfold ParameterExecution.emissionTimes TrainingRead.parameterExecution
  simp only [ParameterExecution.emissions_cons, ParameterMove.emissions, ParameterJump.emissions,
    parameter_emissions_append, List.nil_append, prefixLabels, parameterTrace_emissions,
    parameterHandoff_emissions, List.filter_cons, decide_true, List.filter_nil]
  rfl

/-- Every execution of the two-pulse task that is complete through the
constructed read horizon has the same endpoint and the same single FIRE.
The result uses the realized guards and the two full fabrication boxes. -/
theorem TrainingRead.every_complete_run {θ ε time gains p upper lower level u delay}
    (run : TrainingRead θ time gains p upper lower level delay)
    (config : (θ 0).thresholds = trainingThresholds p upper lower level)
    (box : @PhysicalBox 1 θ ε)
    (threshold : 19 / 20 ≤ level ∧ level ≤ 21 / 20)
    (hi : |upper - 1 / 10| ≤ 1 / 200) (lo : 0 ≤ lower)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q))
    (e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p delay) u)
    (complete : ParameterCompleteThrough e run.handoff.decision.stop) :
    u.ObservationalEq run.handoff.decision.final ∧
      e.emissionTimes 0 = [run.handoff.decision.stop] := by
  have bounds := training_threshold_bounds config threshold hi lo
  have initial := training_initial_invariant (time := time) (p := p) (delay := delay) caps
  have reference := run.parameterComplete config threshold.1
  refine ⟨(ParameterExecution.observational_unique box bounds e
    (run.parameterExecution config) initial complete reference).1, ?_⟩
  exact (e.emissionTimes_unique (run.parameterExecution config) box bounds initial
    complete reference 0).trans (run.parameterEmissionTimes config)

/-- Existence and every-complete-run correctness of one training pulse
followed by one read with a variable delay and ERROR exit. The bounds
ensure gain headroom and that the sensor settles before the read. Every competing complete run is compared at the same horizon. -/
theorem training_read_every_complete_in_band {θ ε time gains p delay}
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds p ((θ 0).thresholds.error p)
      ((θ 0).thresholds.auxReady p) (θ 0).thresholds.fire)
    (threshold : 19 / 20 ≤ (θ 0).thresholds.fire ∧ (θ 0).thresholds.fire ≤ 21 / 20)
    (hi : |(θ 0).thresholds.error p - 1 / 10| ≤ 1 / 200)
    (lo : 7 / 800 ≤ (θ 0).thresholds.auxReady p)
    (dose : 11 / 20 ≤ 8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) ∧
      8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) ≤ 77 / 100)
    (delayMin : 16 ≤ delay)
    (settled : |(θ 0).thresholds.auxReady p - 1 / 40| *
      Real.exp (-(1 / 2) * (delay - 3)) ≤ 1 / 100000)
    (gain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    ∃ T final,
      time + delay + 3 / 10 < T ∧ T < time + delay + 9 / 10 ∧
      (∃ e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p delay) final,
        ParameterCompleteThrough e T) ∧
      ∀ {u} (e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p delay) u),
        ParameterCompleteThrough e T →
        u.ObservationalEq final ∧ e.emissionTimes 0 = [T] ∧
        u.x 0 (.z p) = gains p + 8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) := by
  have rest : |(θ 0).thresholds.auxReady p - 1 / 40| *
      Real.exp (-(1 / 2) * (delay - 159 / 100)) ≤ 1 / 100000 :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (abs_nonneg _)).trans settled
  obtain ⟨run⟩ := training_read_exists_in_band (time := time) box threshold hi lo dose delayMin rest gain caps
  have complete := run.parameterComplete config threshold.1
  let decision := run.handoff.decision
  have after := decision.outcome.1
  have before := decision.outcome.2.1
  rw [run.read_date] at after before
  refine ⟨decision.stop, decision.final, after, before,
    ⟨run.parameterExecution config, complete⟩, ?_⟩
  intro u e done
  obtain ⟨same, times⟩ := run.every_complete_run config box threshold hi (by linarith) caps e done
  refine ⟨same, times, ?_⟩
  rw [same.values]
  change decision.silent.final.x 0 (.z p) = _
  rw [decision.silent.gain_preserved, run.handoff.learned_at_read, run.dose_from_birth]

/-- Existence and every-complete-run correctness of one training pulse
followed by one read, for either fabrication box and the realized guard
errors. Every competing complete run is compared at the same horizon. -/
theorem training_read_every_complete {θ ε time gains p}
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds p ((θ 0).thresholds.error p)
      ((θ 0).thresholds.auxReady p) (θ 0).thresholds.fire)
    (threshold : 19 / 20 ≤ (θ 0).thresholds.fire ∧ (θ 0).thresholds.fire ≤ 21 / 20)
    (hi : |(θ 0).thresholds.error p - 1 / 10| ≤ 1 / 200)
    (lo : |(θ 0).thresholds.auxReady p - 1 / 40| ≤ 1 / 800)
    (gain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    ∃ T final,
      time + 16 + 3 / 10 < T ∧ T < time + 16 + 9 / 10 ∧
      (∃ e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p) final,
        ParameterCompleteThrough e T) ∧
      ∀ {u} (e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p) u),
        ParameterCompleteThrough e T →
        u.ObservationalEq final ∧ e.emissionTimes 0 = [T] ∧
        u.x 0 (.z p) = gains p + 8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) := by
  obtain ⟨run, complete⟩ := training_read_in_parameters (time := time) box config threshold hi lo gain caps
  let decision := run.handoff.decision
  have after := decision.outcome.1
  have before := decision.outcome.2.1
  rw [run.read_date] at after before
  refine ⟨decision.stop, decision.final, after, before,
    ⟨run.parameterExecution config, complete⟩, ?_⟩
  intro u e done
  obtain ⟨same, times⟩ := run.every_complete_run config box threshold hi (by linarith [(abs_le.mp lo).1]) caps e done
  refine ⟨same, times, ?_⟩
  rw [same.values]
  change decision.silent.final.x 0 (.z p) = _
  rw [decision.silent.gain_preserved, run.handoff.learned_at_read, run.dose_from_birth]

/-- Training and readout with the ERROR exit within 0.00125 of 0.01.
The extra wait allows the sensor to return to the original rest band.
The FIRE and ERROR entry thresholds still have their original 5% bands. -/
theorem training_read_exit_001_every_complete {θ ε time gains p}
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds p ((θ 0).thresholds.error p)
      ((θ 0).thresholds.auxReady p) (θ 0).thresholds.fire)
    (threshold : 19 / 20 ≤ (θ 0).thresholds.fire ∧ (θ 0).thresholds.fire ≤ 21 / 20)
    (hi : |(θ 0).thresholds.error p - 1 / 10| ≤ 1 / 200)
    (lo : |(θ 0).thresholds.auxReady p - 1 / 100| ≤ 1 / 800)
    (gain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    ∃ T final,
      time + 18 + 3 / 10 < T ∧ T < time + 18 + 9 / 10 ∧
      (∃ e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p 18) final,
        ParameterCompleteThrough e T) ∧
      ∀ {u} (e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p 18) u),
        ParameterCompleteThrough e T →
        u.ObservationalEq final ∧ e.emissionTimes 0 = [T] ∧
        u.x 0 (.z p) = gains p + 8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) ∧
        u.x 0 (.z p) - gains p ∈ Set.Icc (67 / 100) (77 / 100) := by
  obtain ⟨hi₁, hi₂⟩ := abs_le.mp hi
  obtain ⟨lo₁, lo₂⟩ := abs_le.mp lo
  have series := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 15 / 2 by norm_num) 15
  norm_num [Finset.sum_range_succ] at series
  have decay : Real.exp (-(1 / 2) * (18 - 3 : ℝ)) ≤ 1 / 1625 := by
    rw [show -(1 / 2) * (18 - 3 : ℝ) = -(15 / 2) by norm_num, Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) (show (1625 : ℝ) ≤ Real.exp (15 / 2) by linarith)
  have offset : |(θ 0).thresholds.auxReady p - 1 / 40| ≤ 13 / 800 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have rest : |(θ 0).thresholds.auxReady p - 1 / 40| *
      Real.exp (-(1 / 2) * (18 - 3)) ≤ 1 / 100000 :=
    (mul_le_mul offset decay (Real.exp_pos _).le (by norm_num)).trans (by norm_num)
  obtain ⟨T, final, early, late, existsRun, allRuns⟩ :=
    training_read_every_complete_in_band (time := time) box config threshold hi (by linarith)
      ⟨by linarith, by linarith⟩ (by norm_num : (16 : ℝ) ≤ 18) rest gain caps
  refine ⟨T, final, early, late, existsRun, ?_⟩
  intro u e complete
  obtain ⟨same, fire, learned⟩ := allRuns e complete
  exact ⟨same, fire, learned, ⟨by linarith, by linarith⟩⟩

end RecursiveLearning.Native
