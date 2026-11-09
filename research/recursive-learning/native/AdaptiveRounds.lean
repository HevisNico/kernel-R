import ScheduledProgram

/-! A later learner receives its training pulses and read pulse from an
earlier report. A round may add logic, new trials, or guarded actions.
Everything is laid out as a finite causal network with fixed clocks. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

/-- A trial includes a calibrated birth gain for its read port. Its
certificate identifies the physical report with the declared retention test. -/
structure AdaptiveTrial where
  lesson : Lesson
  testPractice : Bool
  passes : Bool
  needs : Learner
  birthGain : ℝ
  nonpositive : birthGain ≤ 0
  capacity : lesson.preparation ≤ 4 ∧ lesson.practice ≤ 4
  gainTest : let gain := birthGain + (3 / 5 : ℝ) * (lessonPorts lesson).count (trialPort testPractice)
    if passes then gain = 3 / 5 else gain ≤ 0
  correct : (lesson.train needs).retained = passes

noncomputable def AdaptiveTrial.standard (practice passes : Bool) : AdaptiveTrial where
  lesson := trialLesson practice passes
  testPractice := practice
  passes := passes
  needs := ⟨3, 3⟩
  birthGain := -(6 / 5)
  nonpositive := by norm_num
  capacity := by cases practice <;> cases passes <;> decide
  gainTest := by
    have count : (lessonPorts (trialLesson practice passes)).count (trialPort practice) =
        if passes then 3 else 2 := by
      cases practice
      · exact (lessonPorts_count (preparationTrial passes)).1
      · exact (lessonPorts_count (practiceTrial passes)).2.1
    dsimp only
    rw [count]
    cases passes <;> norm_num
  correct := by cases practice <;> cases passes <;> decide

noncomputable def AdaptiveTrial.tokens (trial : AdaptiveTrial) (clock : ℝ) : List (Delivery 1) :=
  (scheduledTrial clock trial.lesson (trialPort trial.testPractice)).pending

private noncomputable def AdaptiveTrial.receiver (trial : AdaptiveTrial) (origin clock : ℝ)
    (launched : Bool) : Snapshot 1 :=
  { scheduledTrial clock trial.lesson (trialPort trial.testPractice) trial.birthGain with
    time := origin
    pending := if launched then trial.tokens clock else [] }

private noncomputable def trialWindow (clock : ℝ) : ReportWindow := ⟨clock + 65, clock + 66⟩

private theorem trial_window_report {θ T clock origin} (trial : AdaptiveTrial) (launched : Bool)
    (box : @PhysicalBox 1 θ ε) (start : origin < clock) (finish : clock + 96 < T) :
    ∃ run : LocalRun θ (trial.receiver origin clock launched) T,
      Reports run.execution 0 (trialWindow clock) (launched && trial.passes) ∧
      run.execution.deliveries.length = (if launched then trial.lesson.cost + 1 else 0) := by
  cases launched with
  | false =>
    let s := trial.receiver origin clock false
    have ready (i : Fin 1) : ReadyCoordinates s i :=
      ⟨rfl, by norm_num [s, AdaptiveTrial.receiver, scheduledTrial, withFuture, readoutLearner,
          nativeLessonStart, preparedTeacher],
        fun _ => ⟨rfl, by norm_num [s, AdaptiveTrial.receiver, scheduledTrial, withFuture,
          readoutLearner, nativeLessonStart, preparedTeacher, RestBand]⟩⟩
    obtain ⟨wait, done, positive, silent, deliveries⟩ := quiet_ready_tail_exists (θ := θ)
      (s := s) (T := T) (by change origin < T; linarith) ready (fun _ _ => rfl) rfl
    exact ⟨⟨_, wait, done, positive⟩, by simp [Reports, ReportWindow.dates, Execution.emissionTimes, silent],
      by rw [deliveries]; rfl⟩
  | true =>
    obtain ⟨run, fire, flag, window, dates, count⟩ := staged_lesson_read_exists_of_gain box start.le finish
      trial.lesson (trialPort trial.testPractice) trial.passes trial.capacity trial.birthGain
      trial.nonpositive trial.gainTest
    have reports : Reports run.execution 0 (trialWindow clock) trial.passes := by
      unfold Reports ReportWindow.dates
      rw [dates]
      cases h : fire with
      | none =>
        have eq : trial.passes = false := by simpa [h] using flag.symm
        simp [eq]
      | some F =>
        have eq : trial.passes = true := by simpa [h] using flag.symm
        obtain ⟨early, late⟩ := window F h
        simp [eq, ReportWindow.accepts, trialWindow, early.le, late]
    exact ⟨run, reports, count⟩

noncomputable def ReportLayout.appendTrial {n} (layout : ReportLayout n) (source : Fin n)
    (trial : AdaptiveTrial) : ReportLayout (n + 1) :=
  let clock := layout.last + 1
  ⟨queueHead layout.start (trial.receiver layout.start.time clock false),
    prependRouted layout.route (forwardReport source (layout.windows source) (trial.tokens clock)),
    Fin.cases (trialWindow clock) layout.windows, clock + 66⟩

/-- The later learner contributes no source token at birth. -/
theorem ReportLayout.appendTrial_source_queue {n} (layout : ReportLayout n)
    (source : Fin n) (trial : AdaptiveTrial) :
    (layout.appendTrial source trial).start.pending = layout.start.pending.map Delivery.succ := rfl

theorem append_trial_timed {n} {layout : ReportLayout n} (timed : layout.WellTimed)
    (source : Fin n) (trial : AdaptiveTrial) :
    (layout.appendTrial source trial).WellTimed := by
  have later : layout.last < (layout.appendTrial source trial).last := by
    change layout.last < layout.last + 1 + 66
    linarith
  refine ⟨timed.1.trans later, ?_⟩
  intro i
  cases i using Fin.cases with
  | zero => exact le_rfl
  | succ i => exact (timed.2 i).trans later.le

private theorem append_trial_run {n θ θH ε T} {layout : ReportLayout n} {bits : Fin n → Bool}
    (prior : CompiledRun θ layout T bits) (box : @PhysicalBox 1 θH ε)
    (source : Fin n) (trial : AdaptiveTrial) (timed : layout.WellTimed)
    (horizon : (layout.appendTrial source trial).last + 75 < T) :
    ∃ run : CompiledRun (prependParameters θH θ) (layout.appendTrial source trial) T
      (Fin.cases (bits source && trial.passes) bits),
      lessonReceipts run.execution.deliveries 0 = (if bits source then trial.lesson.cost + 1 else 0) ∧
      (∀ i, run.final.x i.succ = prior.final.x i) ∧
      (∀ i, lessonReceipts run.execution.deliveries i.succ = lessonReceipts prior.execution.deliveries i) := by
  let clock := layout.last + 1
  let origin := layout.start.time
  let window := layout.windows source
  let contacts := forwardReport source window (trial.tokens clock)
  have future : origin < clock := by dsimp [origin, clock]; linarith [timed.1]
  have endTime : clock + 96 < T := by
    change clock + 66 + 75 < T at horizon
    linarith
  obtain ⟨localRun, report, count⟩ := trial_window_report trial (bits source) box future endTime
  have causal : StrictHeadRoutes contacts := forward_report_strict source window (by
    intro d hd
    have early := scheduled_trial_future hd
    change (layout.windows source).stop ≤ d.due
    dsimp [clock] at early
    linarith [timed.2 source])
  have queue : prior.execution.headInputQueue contacts = (trial.receiver origin clock (bits source)).pending :=
    forward_report_inputs prior.execution source window (trial.tokens clock) (bits source) (prior.reports source)
  obtain ⟨weave⟩ := compose_scheduled_receiver prior.execution localRun.execution prior.complete
    localRun.complete rfl [] contacts causal (List.Perm.of_eq queue)
  let e : Execution (prependParameters θH θ) (layout.appendTrial source trial).route
      (layout.appendTrial source trial).start _ := weave.execution
  have hp := readout_learner_physical_of_gain box clock trial.lesson (trialPort trial.testPractice)
    trial.birthGain trial.nonpositive
  have hi : InitiallyBelowReady (trial.receiver origin clock false) := by
    intro i c ready
    cases c with
    | q => change (1 / 10 : ℝ) < 1; norm_num
    | m p => change (1 / 40 : ℝ) < 1; norm_num
    | z _ => exact False.elim ready
    | b => exact False.elim ready
    | energy => exact False.elim ready
  have reports (i : Fin (n + 1)) :
      Reports e i ((layout.appendTrial source trial).windows i)
        (Fin.cases (bits source && trial.passes) bits i) := by
    cases i using Fin.cases with
    | zero =>
      unfold Reports ReportWindow.dates
      rw [show e.emissionTimes 0 = localRun.execution.emissionTimes 0 from weave.head_emission_times]
      exact report
    | succ i =>
      unfold Reports ReportWindow.dates
      rw [show e.emissionTimes i.succ = prior.execution.emissionTimes i from weave.tail_emission_times i]
      exact prior.reports i
  let run : CompiledRun (prependParameters θH θ) (layout.appendTrial source trial) T
      (Fin.cases (bits source && trial.passes) bits) :=
    ⟨_, e, weave.complete prior.complete localRun.complete,
      weave.contacts_transversal prior.positive localRun.positive, reports,
      prepend_physical prior.physical ⟨hp.region, hp.gain_cap, hp.recovery_cap, hp.reserve⟩ _,
      prepend_initial_ready prior.initial hi, prepend_routed_causal prior.causal causal⟩
  exact ⟨run, (CausalTraceBalance.head_receipts weave.trace).trans count, fun _ => rfl,
    CausalTraceBalance.tail_receipts weave.trace⟩


/-- Topologically ordered instructions over available reports. A guarded
trial sends the lesson and its read pulse to the same new physical learner. -/
inductive AdaptiveProgram (inputs : ℕ) : ℕ → Type
  | inputs : AdaptiveProgram inputs inputs
  | andGate {n} (prior : AdaptiveProgram inputs n) (first : Fin n) (rest : List (Fin n)) :
      AdaptiveProgram inputs (n + 1)
  | notGate {n} (prior : AdaptiveProgram inputs n) (source : Fin n) :
      AdaptiveProgram inputs (n + 1)
  | trial {n} (prior : AdaptiveProgram inputs n) (source : Fin n) (spec : AdaptiveTrial) :
      AdaptiveProgram inputs (n + 1)
  | commit {n} (prior : AdaptiveProgram inputs n) (source : Fin n) (port : Port) (lesson : Lesson)
      (capacity : lesson.preparation ≤ 4 ∧ lesson.practice ≤ 4) : AdaptiveProgram inputs (n + 1 + 1)

def AdaptiveProgram.appendCircuit {n m k} (prior : AdaptiveProgram n m) :
    ReportCircuit m k → AdaptiveProgram n k
  | .inputs => prior
  | .andGate rest first others => .andGate (prior.appendCircuit rest) first others
  | .notGate rest source => .notGate (prior.appendCircuit rest) source

def AdaptiveProgram.appendActions {n m k} (prior : AdaptiveProgram n m) :
    CommitPlan m k → AdaptiveProgram n k
  | .none => prior
  | .add rest source port lesson cap => .commit (prior.appendActions rest) source port lesson cap

noncomputable def AdaptiveProgram.compile {n m} (p : AdaptiveProgram n m)
    (input : ReportLayout n) : ReportLayout m :=
  match p with
  | .inputs => input
  | .andGate prior first rest => (prior.compile input).appendAnd (first :: rest)
  | .notGate prior source => (prior.compile input).appendNot source
  | .trial prior source spec => (prior.compile input).appendTrial source spec
  | .commit prior source port lesson _ => (prior.compile input).appendBranch source port lesson

def AdaptiveProgram.eval {n m} (p : AdaptiveProgram n m)
    (input : Fin n → Bool) : Fin m → Bool :=
  match p with
  | .inputs => input
  | .andGate prior first rest =>
    let bits := prior.eval input
    Fin.cases ((first :: rest).all bits) bits
  | .notGate prior source =>
    let bits := prior.eval input
    Fin.cases (!bits source) bits
  | .trial prior source spec =>
    let bits := prior.eval input
    Fin.cases (bits source && spec.passes) bits
  | .commit prior _ _ _ _ => noActionReports (prior.eval input)

theorem AdaptiveProgram.trial_reports_retention {n m} (prior : AdaptiveProgram n m)
    (source : Fin m) (trial : AdaptiveTrial) (input : Fin n → Bool) :
    (prior.trial source trial).eval input 0 =
      (prior.eval input source && (trial.lesson.train trial.needs).retained) := by
  rw [trial.correct]
  rfl

def AdaptiveProgram.initialParameters {n m} : AdaptiveProgram n m → (Fin m → Parameters) → Fin n → Parameters
  | .inputs, θ => θ
  | .andGate prior _ _, θ => prior.initialParameters (fun i => θ i.succ)
  | .notGate prior _, θ => prior.initialParameters (fun i => θ i.succ)
  | .trial prior _ _, θ => prior.initialParameters (fun i => θ i.succ)
  | .commit prior _ _ _ _, θ => prior.initialParameters (fun i => θ i.succ.succ)

def GainsRetain (gain : Port → ℝ) (needs : Learner) : Prop :=
  -(12 / 5 : ℝ) + (3 / 5 : ℝ) * needs.preparationLeft ≤ gain 0 ∧
  -(12 / 5 : ℝ) + (3 / 5 : ℝ) * needs.practiceLeft ≤ gain 1

/-- Observe every guarded action and later trial in the final execution.
A launched trial receives its complete lesson plus one physical read.
A skipped trial receives zero inputs. -/
def AdaptiveProgram.Effects {n m} (p : AdaptiveProgram n m) (input : Fin n → Bool)
    (gains : Fin m → Port → ℝ) (receipts : Fin m → ℕ) : Prop :=
  match p with
  | .inputs => True
  | .andGate prior _ _ => prior.Effects input (fun i => gains i.succ) (fun i => receipts i.succ)
  | .notGate prior _ => prior.Effects input (fun i => gains i.succ) (fun i => receipts i.succ)
  | .trial prior source spec =>
    receipts 0 = (if prior.eval input source then spec.lesson.cost + 1 else 0) ∧
    prior.Effects input (fun i => gains i.succ) (fun i => receipts i.succ)
  | @AdaptiveProgram.commit _ k prior source port lesson _ =>
    let accepted := prior.eval input source
    receipts 0 = (if accepted then lesson.cost else 0) ∧
    receipts (0 : Fin (k + 1)).succ = (if accepted then 1 else 0) ∧
    (∀ p, gains (0 : Fin (k + 1)).succ p = if p = port ∧ accepted then 3 / 5 else 0) ∧
    (∀ needs, GainsRetain (gains 0) needs ↔
      ((if accepted then lesson else ⟨0, 0⟩).train needs).retained = true) ∧
    prior.Effects input (fun i => gains i.succ.succ) (fun i => receipts i.succ.succ)

theorem AdaptiveProgram.initial_box {n m θ ε} (p : AdaptiveProgram n m)
    (box : @PhysicalBox m θ ε) : PhysicalBox (p.initialParameters θ) ε := by
  induction p with
  | inputs => exact box
  | andGate _ _ _ ih => exact ih ⟨box.1, fun i => box.2 i.succ⟩
  | notGate _ _ ih => exact ih ⟨box.1, fun i => box.2 i.succ⟩
  | trial _ _ _ ih => exact ih ⟨box.1, fun i => box.2 i.succ⟩
  | commit _ _ _ _ _ ih => exact ih ⟨box.1, fun i => box.2 i.succ.succ⟩

theorem AdaptiveProgram.compile_timed {n m} (p : AdaptiveProgram n m) {layout : ReportLayout n}
    (timed : layout.WellTimed) : (p.compile layout).WellTimed := by
  induction p with
  | inputs => exact timed
  | andGate _ first rest ih => exact append_and_timed ih (first :: rest)
  | notGate _ source ih => exact append_not_timed ih source
  | trial _ source spec ih => exact append_trial_timed ih source spec
  | commit _ source port lesson _ ih => exact append_branch_timed ih source port lesson

theorem AdaptiveProgram.layout_last_mono {n m} (p : AdaptiveProgram n m) (layout : ReportLayout n) :
    layout.last ≤ (p.compile layout).last := by
  induction p with
  | inputs => exact le_rfl
  | andGate prior first rest ih =>
    change _ ≤ (prior.compile layout).last + 1 + 8 * ((first :: rest).length : ℝ) + 1
    linarith [show (0 : ℝ) ≤ ((first :: rest).length : ℝ) by positivity]
  | notGate prior source ih =>
    change _ ≤ (prior.compile layout).last + 1 + 18
    linarith
  | trial prior source spec ih =>
    change _ ≤ (prior.compile layout).last + 1 + 66
    linarith
  | commit _ _ _ _ _ ih => exact ih

private theorem carries_effects {n m k} (p : AdaptiveProgram n m) {bits : Fin n → Bool}
    {values : Fin m → Coord → ℝ} {receipts : Fin m → ℕ}
    {newValues : Fin k → Coord → ℝ} {newReceipts : Fin k → ℕ}
    (embed : Fin m → Fin k)
    (carryValues : ∀ i, newValues (embed i) = values i)
    (carryReceipts : ∀ i, newReceipts (embed i) = receipts i)
    (effects : p.Effects bits (fun i q => values i (.z q)) receipts) :
    p.Effects bits (fun i q => newValues (embed i) (.z q)) (fun i => newReceipts (embed i)) := by
  have valuesEq : (fun i q => newValues (embed i) (.z q)) = (fun i q => values i (.z q)) := by
    funext i q
    rw [carryValues]
  rw [valuesEq, funext carryReceipts]
  exact effects

/-- Build an arbitrary finite sequence of stages at one common horizon,
including stages whose input reports come from newly launched learners. -/
theorem AdaptiveProgram.run {n m θ ε T} (p : AdaptiveProgram n m) {layout : ReportLayout n}
    {bits : Fin n → Bool} (input : CompiledRun (p.initialParameters θ) layout T bits)
    (box : @PhysicalBox m θ ε) (timed : layout.WellTimed) (horizon : (p.compile layout).last + 75 < T) :
    ∃ run : CompiledRun θ (p.compile layout) T (p.eval bits),
      p.Effects bits (fun i q => run.final.x i (.z q)) (lessonReceipts run.execution.deliveries) := by
  induction p with
  | inputs => exact ⟨input, trivial⟩
  | andGate prior first rest ih =>
    rename_i k
    have tailBox : PhysicalBox (fun i : Fin k => θ i.succ) ε := ⟨box.1, fun i => box.2 i.succ⟩
    have headBox : @PhysicalBox 1 (fun _ => θ 0) ε := ⟨box.1, fun _ => box.2 0⟩
    have limit : (prior.compile layout).last + 75 < T := by
      change (prior.compile layout).last + 1 + 8 * ((first :: rest).length : ℝ) + 1 + 75 < T at horizon
      linarith [show (0 : ℝ) ≤ ((first :: rest).length : ℝ) by positivity]
    obtain ⟨tail, effects⟩ := ih input tailBox limit
    obtain ⟨head, values, receipts⟩ := append_and_run tail headBox (first :: rest) (by simp)
      (prior.compile_timed timed) (by
        change ((prior.andGate first rest).compile layout).last + 45 < T
        linarith)
    let parameters := prependParameters (fun _ => θ 0) (fun i : Fin k => θ i.succ)
    let oldBits := prior.eval bits
    have gateBit : decide (∀ i ∈ first :: rest, oldBits i = true) =
        (first :: rest).all oldBits := by
      apply Bool.eq_iff_iff.mpr
      simp [List.all_eq_true]
    have result : ∃ run : CompiledRun parameters ((prior.andGate first rest).compile layout) T
        (Fin.cases (decide (∀ i ∈ first :: rest, oldBits i = true)) oldBits),
        (prior.andGate first rest).Effects bits (fun i q => run.final.x i (.z q))
          (lessonReceipts run.execution.deliveries) :=
      ⟨head, carries_effects prior Fin.succ values receipts effects⟩
    rw [show parameters = θ from prepend_parameters_all θ, gateBit] at result
    exact result
  | notGate prior source ih =>
    rename_i k
    have tailBox : PhysicalBox (fun i : Fin k => θ i.succ) ε := ⟨box.1, fun i => box.2 i.succ⟩
    have headBox : @PhysicalBox 1 (fun _ => θ 0) ε := ⟨box.1, fun _ => box.2 0⟩
    have limit : (prior.compile layout).last + 75 < T := by
      change (prior.compile layout).last + 1 + 18 + 75 < T at horizon
      linarith
    obtain ⟨tail, effects⟩ := ih input tailBox limit
    obtain ⟨head, values, receipts⟩ := append_not_run tail headBox source (prior.compile_timed timed)
      (by change ((prior.notGate source).compile layout).last + 45 < T; linarith)
    have result : ∃ run : CompiledRun _ ((prior.notGate source).compile layout) T _,
        (prior.notGate source).Effects bits (fun i q => run.final.x i (.z q))
          (lessonReceipts run.execution.deliveries) :=
      ⟨head, carries_effects prior Fin.succ values receipts effects⟩
    rw [prepend_parameters_all θ] at result
    exact result
  | trial prior source spec ih =>
    rename_i k
    have tailBox : PhysicalBox (fun i : Fin k => θ i.succ) ε := ⟨box.1, fun i => box.2 i.succ⟩
    have headBox : @PhysicalBox 1 (fun _ => θ 0) ε := ⟨box.1, fun _ => box.2 0⟩
    have limit : (prior.compile layout).last + 75 < T := by
      change (prior.compile layout).last + 1 + 66 + 75 < T at horizon
      linarith
    obtain ⟨tail, effects⟩ := ih input tailBox limit
    obtain ⟨head, count, values, receipts⟩ := append_trial_run tail headBox source spec
      (prior.compile_timed timed) horizon
    have result : ∃ run : CompiledRun _ ((prior.trial source spec).compile layout) T _,
        (prior.trial source spec).Effects bits (fun i q => run.final.x i (.z q))
          (lessonReceipts run.execution.deliveries) :=
      ⟨head, count, carries_effects prior Fin.succ values receipts effects⟩
    rw [prepend_parameters_all θ] at result
    exact result
  | commit prior source port lesson capacity ih =>
    rename_i k
    have tailBox : PhysicalBox (fun i : Fin k => θ i.succ.succ) ε := ⟨box.1, fun i => box.2 i.succ.succ⟩
    have creditBox : @PhysicalBox 1 (fun _ => θ (0 : Fin (k + 1)).succ) ε :=
      ⟨box.1, fun _ => box.2 (0 : Fin (k + 1)).succ⟩
    have lessonBox : @PhysicalBox 1 (fun _ => θ 0) ε := ⟨box.1, fun _ => box.2 0⟩
    obtain ⟨tail, effects⟩ := ih input tailBox horizon
    obtain ⟨action, head, same, lessonCount, creditCount, receipts⟩ :=
      append_branch_run tail creditBox lessonBox source port lesson capacity (prior.compile_timed timed) horizon
    have values (i : Fin k) : head.final.x i.succ.succ = tail.final.x i := by
      rw [same, action.previousValues]
    let parameters := prependParameters (fun _ => θ 0)
      (prependParameters (fun _ => θ (0 : Fin (k + 1)).succ) (fun i : Fin k => θ i.succ.succ))
    have result : ∃ run : CompiledRun parameters ((prior.commit source port lesson capacity).compile layout)
        T (noActionReports (prior.eval bits)),
        (prior.commit source port lesson capacity).Effects bits (fun i q => run.final.x i (.z q))
          (lessonReceipts run.execution.deliveries) := by
      refine ⟨head, lessonCount, creditCount, ?_, ?_,
        carries_effects prior (fun i => i.succ.succ) values receipts effects⟩
      · intro q
        rw [same]
        exact action.credit q
      · intro needs
        rw [same]
        exact action.lessonRetention needs
    rw [show parameters = θ from split_branch_parameters θ] at result
    exact result

def ReportLayout.SameSources {n} (a b : ReportLayout n) : Prop :=
  a.SameWiring b ∧ a.start.pending = b.start.pending

private theorem same_trial_sources {n} {a b : ReportLayout n} (same : a.SameSources b)
    (source : Fin n) (trialA trialB : AdaptiveTrial)
    (tokens : ∀ t, trialA.tokens t = trialB.tokens t) :
    (a.appendTrial source trialA).SameSources (b.appendTrial source trialB) := by
  obtain ⟨⟨routes, windows, times⟩, pending⟩ := same
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change prependRouted a.route (forwardReport source (a.windows source) (trialA.tokens (a.last + 1))) =
      prependRouted b.route (forwardReport source (b.windows source) (trialB.tokens (b.last + 1)))
    rw [routes, windows, times, tokens]
  · simp only [ReportLayout.appendTrial, windows, times]
  · simp only [ReportLayout.appendTrial, times]
  · rw [ReportLayout.appendTrial_source_queue, ReportLayout.appendTrial_source_queue, pending]

private theorem same_not_sources {n} {a b : ReportLayout n} (same : a.SameSources b)
    (source : Fin n) : (a.appendNot source).SameSources (b.appendNot source) := by
  obtain ⟨⟨routes, windows, times⟩, pending⟩ := same
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [ReportLayout.appendNot, routes, windows, times]
  · simp only [ReportLayout.appendNot, windows, times]
  · simp only [ReportLayout.appendNot, times]
  · change (notExternal (a.last + 1)).map Delivery.head ++ a.start.pending.map Delivery.succ =
      (notExternal (b.last + 1)).map Delivery.head ++ b.start.pending.map Delivery.succ
    rw [times, pending]

private theorem same_and_sources {n} {a b : ReportLayout n} (same : a.SameSources b)
    (sources : List (Fin n)) : (a.appendAnd sources).SameSources (b.appendAnd sources) := by
  obtain ⟨⟨routes, windows, times⟩, pending⟩ := same
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [ReportLayout.appendAnd, routes, windows, times]
  · simp only [ReportLayout.appendAnd, windows, times]
  · simp only [ReportLayout.appendAnd, times]
  · change ([conjunctionProbe (a.last + 1 + 8 * sources.length)] : List (Delivery 1)).map Delivery.head ++
      a.start.pending.map Delivery.succ =
        ([conjunctionProbe (b.last + 1 + 8 * sources.length)] : List (Delivery 1)).map Delivery.head ++
          b.start.pending.map Delivery.succ
    rw [times, pending]

private theorem same_commit_sources {n} {a b : ReportLayout n} (same : a.SameSources b)
    (source : Fin n) (port : Port) (lesson : Lesson) :
    (a.appendBranch source port lesson).SameSources (b.appendBranch source port lesson) := by
  obtain ⟨⟨routes, windows, times⟩, pending⟩ := same
  refine ⟨⟨?_, ?_, times⟩, ?_⟩
  · simp only [ReportLayout.appendBranch, routes, windows, times]
  · simp only [ReportLayout.appendBranch, windows, times]
  · change (a.start.pending.map Delivery.succ).map Delivery.succ =
      (b.start.pending.map Delivery.succ).map Delivery.succ
    rw [pending]

/-- Two programs share a plan if every node has the same predecessors,
logic and pulse packet. The trial calibration and expected bit may vary. -/
inductive AdaptiveProgram.SamePlan {inputs : ℕ} :
    {n : ℕ} → AdaptiveProgram inputs n → AdaptiveProgram inputs n → Prop
  | inputs : SamePlan .inputs .inputs
  | andGate {n} {a b : AdaptiveProgram inputs n} {first rest} (prior : SamePlan a b) :
      SamePlan (.andGate a first rest) (.andGate b first rest)
  | notGate {n} {a b : AdaptiveProgram inputs n} {source} (prior : SamePlan a b) :
      SamePlan (.notGate a source) (.notGate b source)
  | trial {n} {a b : AdaptiveProgram inputs n} {source ta tb} (prior : SamePlan a b)
      (tokens : ∀ t, ta.tokens t = tb.tokens t) :
      SamePlan (.trial a source ta) (.trial b source tb)
  | commit {n} {a b : AdaptiveProgram inputs n} {source port lesson capA capB}
      (prior : SamePlan a b) :
      SamePlan (.commit a source port lesson capA) (.commit b source port lesson capB)

theorem AdaptiveProgram.SamePlan.compile_same_sources {n m} {a b : AdaptiveProgram n m}
    (plan : a.SamePlan b) {x y : ReportLayout n} (same : x.SameSources y) :
    (a.compile x).SameSources (b.compile y) := by
  induction plan with
  | inputs => exact same
  | @andGate _ _ _ first rest _ ih => exact same_and_sources ih (first :: rest)
  | @notGate _ _ _ source _ ih => exact same_not_sources ih source
  | @trial _ _ _ source ta tb _ tokens ih => exact same_trial_sources ih source ta tb tokens
  | @commit _ _ _ source port lesson _ _ _ ih => exact same_commit_sources ih source port lesson

theorem AdaptiveProgram.compile_same_wiring {n m} (p : AdaptiveProgram n m)
    {a b : ReportLayout n} (same : a.SameWiring b) :
    (p.compile a).SameWiring (p.compile b) := by
  induction p with
  | inputs => exact same
  | andGate prior first rest ih =>
    obtain ⟨route, windows, clock⟩ := ih
    simp [AdaptiveProgram.compile, ReportLayout.SameWiring, ReportLayout.appendAnd, route, windows, clock]
  | notGate prior source ih =>
    obtain ⟨route, windows, clock⟩ := ih
    simp [AdaptiveProgram.compile, ReportLayout.SameWiring, ReportLayout.appendNot, route, windows, clock]
  | trial prior source spec ih =>
    obtain ⟨route, windows, clock⟩ := ih
    simp [AdaptiveProgram.compile, ReportLayout.SameWiring, ReportLayout.appendTrial, route, windows, clock]
  | commit prior source port lesson capacity ih =>
    obtain ⟨route, windows, clock⟩ := ih
    simp [AdaptiveProgram.compile, ReportLayout.SameWiring, ReportLayout.appendBranch, route, windows, clock]

theorem adaptive_program_fixed_wiring {n m} (p : AdaptiveProgram n m)
    (time : ℝ) (kinds first second : Fin n → Bool) :
    (p.compile (learnerReportLayout time kinds first)).SameWiring
      (p.compile (learnerReportLayout time kinds second)) :=
  p.compile_same_wiring ⟨rfl, rfl, rfl⟩

/-- Compile a finite adaptive program. Every later trial is launched by
an earlier physical report. Its own physical read supplies the next
report. Each complete crossing run has the same state, dates and
delivery multiset for its declared initial trials. -/
theorem compile_finite_adaptive_program {n m θ ε} (p : AdaptiveProgram n m)
    (box : @PhysicalBox m θ ε) (time : ℝ) (kinds passed : Fin n → Bool) :
    let layout := p.compile (learnerReportLayout time kinds passed)
    let T := layout.last + 76
    ∃ (run : CompiledRun θ layout T (p.eval passed))
      (crossing : CrossingExecution θ layout.route layout.start run.final),
      crossing.execution = run.execution.toWeak ∧ CrossingCompleteThrough crossing T ∧
      p.Effects passed (fun i q => run.final.x i (.z q)) (lessonReceipts run.execution.deliveries) ∧
      ∀ v (other : CrossingExecution θ layout.route layout.start v), CrossingCompleteThrough other T →
        ∃ native : Execution θ layout.route layout.start v, native.toWeak = other.execution ∧
          v.ObservationalEq run.final ∧ native.deliveries.Perm run.execution.deliveries ∧
          ∀ i, other.execution.emissionTimes i = run.execution.emissionTimes i := by
  let initial := learnerReportLayout time kinds passed
  let layout := p.compile initial
  let T := layout.last + 76
  have later : time + 96 < T := by
    have low := p.layout_last_mono initial
    change time + 66 ≤ layout.last at low
    dsimp [T]
    linarith
  obtain ⟨input⟩ := learner_report_run (p.initial_box box) time kinds passed later
  obtain ⟨run, effects⟩ := p.run input box (learner_report_layout_timed time kinds passed)
    (by change layout.last + 75 < layout.last + 76; linarith)
  obtain ⟨crossing, same, complete, every⟩ := complete_crossing_accounting run.execution run.complete
    run.positive box run.physical run.initial run.causal
  exact ⟨run, crossing, same, complete, effects, every⟩

/-- The second learner is triggered only by the first new learner's own
readout. In particular an attempted first trial can fail and prevent
the entire second trial from being delivered. -/
def twoAdaptiveTrials (first second : AdaptiveTrial) : AdaptiveProgram 1 3 :=
  ((AdaptiveProgram.inputs : AdaptiveProgram 1 1).trial 0 first).trial 0 second

theorem two_adaptive_trials_effects {θ ε} (box : @PhysicalBox 3 θ ε)
    (time : ℝ) (seedKind seedPasses : Bool) (first second : AdaptiveTrial) :
    let p := twoAdaptiveTrials first second
    let layout := p.compile (learnerReportLayout time (fun _ => seedKind) (fun _ => seedPasses))
    ∃ run : CompiledRun θ layout (layout.last + 76) (p.eval (fun _ => seedPasses)),
      lessonReceipts run.execution.deliveries 1 = (if seedPasses then first.lesson.cost + 1 else 0) ∧
      lessonReceipts run.execution.deliveries 0 =
        (if seedPasses && first.passes then second.lesson.cost + 1 else 0) ∧
      Reports run.execution 0 (layout.windows 0) (seedPasses && first.passes && second.passes) := by
  obtain ⟨run, _, _, _, effects, _⟩ := compile_finite_adaptive_program (twoAdaptiveTrials first second)
    box time (fun _ => seedKind) (fun _ => seedPasses)
  exact ⟨run, effects.2.1, effects.1, run.reports 0⟩

end RecursiveLearning.Native
