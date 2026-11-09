import NativeLearning
import KernelR.HybridPortSourceWire
import KernelR.HybridUniversalExecution

/-! One native feedback link. The learner's actual FIRE creates the only
delivery to the teacher. This stage starts at an admitted learner probe. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

/-- Only learner 0 can schedule feedback, on selector port 2 of teacher 1. -/
def feedbackRouter (delay : ℝ → ℝ) : Router 2 :=
  fun sender time => if sender = 0 then [⟨1, 2, time + delay time⟩] else []

structure RoutedFeedback (learner : Fin 1 → Parameters) (teacher : Parameters)
    (delay : ℝ → ℝ) (start : Snapshot 2) where
  final : Snapshot 2
  execution : Execution (extendParameters learner teacher) (feedbackRouter delay) start final
  fire : ℝ
  complete : CompleteThrough execution (fire + delay fire + 15 / 2)
  emissions : execution.ledger.emissions = [(0, fire)]
  deliveries : execution.deliveries = [⟨1, 2, fire + delay fire⟩]
  pendingEmpty : final.pending = []
  selectorDose : final.x 1 (.z 2) = start.x 1 (.z 2) + 3 / 5
  otherGains : ∀ p, p ≠ 2 → final.x 1 (.z p) = start.x 1 (.z p)

/-- Every complete execution through the witness horizon has its one FIRE,
    its one delivery, and the same teacher gain changes. -/
theorem RoutedFeedback.every_complete {learner teacher ε delay start final}
    (feedback : RoutedFeedback learner teacher delay start)
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε)
    (physical : PhysicalInvariant (extendParameters learner teacher) start)
    (queue : start.pending = [])
    (execution : Execution (extendParameters learner teacher) (feedbackRouter delay) start final)
    (complete : CompleteThrough execution (feedback.fire + delay feedback.fire + 15 / 2)) :
    execution.ledger.emissions = [(0, feedback.fire)] ∧
      execution.deliveries = [⟨1, 2, feedback.fire + delay feedback.fire⟩] ∧
      final.pending = [] ∧
      final.x 1 (.z 2) = start.x 1 (.z 2) + 3 / 5 ∧
      (∀ p, p ≠ 2 → final.x 1 (.z p) = start.x 1 (.z p)) := by
  obtain ⟨endpoint, emissions⟩ :=
    execution.observational_unique feedback.execution box physical complete feedback.complete
  rw [feedback.emissions] at emissions
  have fire := List.perm_singleton.mp emissions
  have empty := List.perm_nil.mp (feedback.pendingEmpty ▸ endpoint.pending)
  have balance := execution.token_balance
  rw [empty, queue, fire] at balance
  have delivery : execution.deliveries.Perm [⟨1, 2, feedback.fire + delay feedback.fire⟩] := by
    apply Multiset.coe_eq_coe.mp
    simpa [feedbackRouter] using balance
  refine ⟨fire, List.perm_singleton.mp delivery, empty, ?_, ?_⟩
  · rw [endpoint.values, feedback.selectorDose]
  · intro p other
    rw [endpoint.values, feedback.otherGains p other]

private theorem projected_physical {learner : Fin 1 → Parameters} {teacher : Parameters}
    {s : Snapshot 2} (physical : PhysicalInvariant (extendParameters learner teacher) s)
    (i : Fin 2) (parameters : Fin 1 → Parameters)
    (parameter : parameters 0 = extendParameters learner teacher i) :
    PhysicalInvariant parameters (s.cellProjection i []) := by
  refine ⟨fun _ => physical.region i, ?_, fun _ => physical.recovery_cap i,
    fun _ => physical.reserve i⟩
  intro j p
  have same : j = 0 := Subsingleton.elim _ _
  subst j
  change s.x i (.z p) ≤ Real.log ((parameters 0).cap p)
  rw [parameter]
  exact physical.gain_cap i p

private theorem receipt_product {learner teacher route source p cycle delay}
    (wire : @PortSourceWire learner teacher route source p cycle 2 delay)
    (queue : source.pending = []) :
    wire.cutH.state.product (portSourceReceiver wire.final) [] = wire.final := by
  have extensionality (s u : Snapshot 2) (ht : s.time = u.time) (hx : s.x = u.x)
      (hm : s.main = u.main) (ha : s.aux = u.aux) (hr : s.raw = u.raw)
      (hp : s.pending = u.pending) : s = u := by
    cases s
    cases u
    simp_all only
  apply extensionality
  · exact wire.cutH.date.trans wire.date.symm
  · funext j
    fin_cases j
    · exact wire.sender_values.symm
    · rfl
  · funext j
    fin_cases j
    · exact wire.sender_main.symm
    · rfl
  · funext j p
    fin_cases j
    · exact (wire.sender_aux p).symm
    · rfl
  · funext j p
    fin_cases j
    · exact (wire.sender_raw p).symm
    · rfl
  · exact (wire.pending.trans queue).symm

/-- From the learner's admitted probe and an empty queue, construct a real
FIRE, its routed arrival, and the teacher's full ERROR dose. The FIRE date
is determined by the learner's flow and is not an input to the theorem. -/
theorem routed_feedback_exists {learner : Fin 1 → Parameters} {teacher ε delay start}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε)
    (physical : PhysicalInvariant (extendParameters learner teacher) start)
    (rawValid : RawValid start) (prepared : PreparedSection start 0)
    (teacherReady : ReadyCoordinates start 1)
    (strong : 9 / 5 ≤ Real.exp (start.x 0 (.z 0)) ∧
      Real.exp (start.x 0 (.z 0)) ≤ 11 / 5)
    (probe : start.raw 0 0 = some start.time)
    (rawOther : ∀ i p, i ≠ 0 ∨ p ≠ 0 → start.raw i p = none)
    (queue : start.pending = [])
    (delayBounds : ∀ t, (3 / 10 : ℝ) ≤ delay t ∧ delay t ≤ 2 / 5)
    (weak : Real.exp (start.x 1 (.z 2)) ≤ 7 / 6)
    (small : start.x 1 (.z 2) ≤ Real.log (6 / 5) + 1 / 1000) :
    Nonempty (RoutedFeedback learner teacher delay start) := by
  obtain ⟨student⟩ := short_learned_cycle_exists box.extend_old (portSourceSender start) 0
    (projected_physical physical 0 learner rfl)
    (fun _ p origin active => rawValid 0 p origin active)
    ⟨prepared.ready, prepared.charge, prepared.recovery, prepared.auxiliary⟩ strong probe
    (fun p hp => rawOther 0 p (Or.inr hp)) (by simp [portSourceSender, Snapshot.cellProjection])
  obtain ⟨wire⟩ := port_source_wire_exists (θR := fun _ => teacher) (route := feedbackRouter delay)
    (pR := 2) (delay := delay) start student box physical rawValid teacherReady
    (fun p => rawOther 1 p (Or.inl (by decide))) (by simp [queue]) delayBounds
    (by intro time _ _; simp [feedbackRouter])
  obtain ⟨learn⟩ := weak_input_cycle_exists (route := fun _ _ => [])
    (portSourceReceiver wire.final) box.extend_new
    (projected_physical wire.physical 1 (fun _ => teacher) rfl)
    (fun _ p origin active => wire.raw_valid 1 p origin active)
    0 2 (fun _ => ⟨wire.receiver_ready.ready, wire.receiver_ready.charge,
      wire.receiver_ready.auxiliary⟩)
    (by
      change Real.exp (wire.final.x 1 (.z 2)) ≤ _
      rw [wire.gains]
      exact weak)
    (by
      change wire.final.x 1 (.z 2) ≤ _
      rw [wire.gains]
      exact small)
    wire.raw_active
    (fun i p h => wire.raw_other p (by simpa only [Subsingleton.elim i 0, ne_self_iff_false,
      false_or] using h))
    (by simp [portSourceReceiver, Snapshot.cellProjection])
  let studentTail : Execution learner (fun _ _ => []) wire.cutH.state student.fast.final :=
    .cons (.flow wire.cutH.flow) wire.cutH.rest
  have tailEmissions : studentTail.ledger.emissions = [] :=
    (List.append_eq_nil_iff.mp (wire.cutH.emissions.symm.trans student.fast.emissions)).2
  have tailDeliveries : studentTail.deliveries = [] :=
    (List.append_eq_nil_iff.mp (wire.cutH.deliveries.symm.trans student.fast.deliveries)).2
  let finish := learn.final.time
  have finishDate : finish = wire.final.time + 15 / 2 := learn.date
  have quietTime : student.returned.final.time < finish := by
    rw [student.date, finishDate]
    change start.time + 69 / 10 < _
    linarith [wire.window.1]
  have studentQueue : student.returned.final.pending = [] := student.pending
  let studentFinal := quietAt student.returned.final finish
  let waitFlow : Flow learner student.returned.final studentFinal :=
    quietFlow student.returned.final quietTime (fun i => (student.ready i).ready)
      (fun i p => ((student.ready i).auxiliary p).1) student.raw_none
      (fun i => by linarith [(student.ready i).charge.2])
      (fun i p => by linarith [((student.ready i).auxiliary p).2.2])
      (by simp [studentQueue])
  let wait : Execution learner (fun _ _ => []) student.returned.final studentFinal :=
    .cons (.flow waitFlow) (.nil _)
  let studentRest := studentTail.append (student.returned.execution.append wait)
  have studentEmissions : studentRest.ledger.emissions = [] := by
    rw [Execution.emissions_append, tailEmissions, Execution.emissions_append,
      student.returned.emissions]
    rfl
  have studentDeliveries : studentRest.deliveries = [] := by
    rw [Execution.deliveries_append, tailDeliveries, Execution.deliveries_append,
      student.returned.deliveries]
    rfl
  obtain ⟨woven, wovenEmissions, wovenDeliveries⟩ := studentRest.product_neutral
    learn.execution (wire.cutH.date.trans wire.date.symm) rfl
    studentEmissions studentDeliveries learn.emissions learn.deliveries [] (by simp)
    (feedbackRouter delay)
  let final := studentFinal.product learn.final []
  let rest : Execution (extendParameters learner teacher) (feedbackRouter delay) wire.final final :=
    woven.cast_source (receipt_product wire queue).symm
  have restEmissions : rest.ledger.emissions = [] := by
    rw [Execution.cast_source_ledger]
    exact wovenEmissions
  have restDeliveries : rest.deliveries = [] := by
    rw [Execution.cast_source_deliveries]
    exact wovenDeliveries
  let execution := wire.execution.append rest
  have readyFinal (i : Fin 2) : ReadyCoordinates final i := by
    fin_cases i
    · have ready := quietAt_ready_coordinates student.returned.final 0 (student.ready 0) quietTime.le
      exact ⟨ready.ready, ready.charge, ready.auxiliary⟩
    · exact ⟨learn.pulse.coordinates.ready, learn.pulse.coordinates.charge,
        learn.pulse.coordinates.auxiliary⟩
  have rawFinal (i : Fin 2) (p : Port) : final.raw i p = none := by
    fin_cases i
    · exact student.raw_none 0 p
    · exact learn.pulse.raw_finished p
  have htime : final.time = student.fire.final.time + delay student.fire.final.time + 15 / 2 := by
    change finish = _
    rw [finishDate, wire.date]
  refine ⟨{
    final := final
    execution := execution
    fire := student.fire.final.time
    complete := ⟨htime, ?_, by simp [final, Snapshot.product]⟩
    emissions := ?_
    deliveries := ?_
    pendingEmpty := rfl
    selectorDose := ?_
    otherGains := ?_
  }⟩
  · apply ready_no_jump final (fun i => (readyFinal i).ready)
      (fun i p => ((readyFinal i).auxiliary p).1) rawFinal
      (fun i => by linarith [(readyFinal i).charge.2])
      (fun i p => by linarith [((readyFinal i).auxiliary p).2.2])
    simp [final, Snapshot.product]
  · rw [Execution.emissions_append, wire.emissions, restEmissions, List.append_nil]
  · rw [Execution.deliveries_append, wire.deliveries, restDeliveries, List.append_nil, wire.date]
  · change learn.final.x 0 (.z 2) = _
    rw [learn.pulse.gain_target]
    change wire.final.x 1 (.z 2) + 3 / 5 = _
    rw [wire.gains]
  · intro p other
    change learn.final.x 0 (.z p) = _
    rw [learn.pulse.gain_other p other]
    exact wire.gains 1 p

/-- On this router a quiet learner cannot affect the initially resting
selector sensor, even if other events occur in the supplied execution. -/
theorem selector_unchanged_without_learner_fire {learner teacher delay start final}
    (execution : Execution (extendParameters learner teacher) (feedbackRouter delay) start final)
    (queue : start.pending = [])
    (ready : start.aux 1 2 = .ready) (rest : RestBand (start.x 1 (.m 2)))
    (noRaw : start.raw 1 2 = none)
    (silent : ∀ time, (0, time) ∉ execution.ledger.emissions) :
    final.x 1 (.z 2) = start.x 1 (.z 2) := by
  apply (execution.aux_no_input_rest_band 1 2 ready rest noRaw ?_).2
  intro d delivered
  rcases execution.delivery_provenance d delivered with initial | ⟨event, emitted, routed⟩
  · simp [queue] at initial
  · rcases event with ⟨sender, time⟩
    by_cases learnerFired : sender = 0
    · subst sender
      exact False.elim (silent time emitted)
    · simp [feedbackRouter, learnerFired] at routed

/-- A routed dose sets the selector while preserving both teaching credits. -/
theorem RoutedFeedback.sets_selector {learner teacher delay start origin}
    (feedback : RoutedFeedback learner teacher delay start)
    (before : Encodes origin start 1 Example.frozenFirst) :
    Encodes origin feedback.final 1 Example.first := by
  intro p
  by_cases target : p = 2
  · subst p
    rw [feedback.selectorDose, before 2]
    norm_num [Memory.portCredit, Example.frozenFirst, Example.first]
  · rw [feedback.otherGains p target, before p]
    fin_cases p
    · norm_num [Memory.portCredit, Example.frozenFirst, Example.first]
    · norm_num [Memory.portCredit, Example.frozenFirst, Example.first]
    · exact False.elim (target rfl)

/-- Two prepared READY cells with just the learner's probe admitted. Varying
    its input gain lets us construct both a firing and a silent response. -/
noncomputable def probeStart (gain time : ℝ) : Snapshot 2 where
  time := time
  x := fun i c => match c with
    | .q => 1 / 10
    | .m _ => 1 / 40
    | .z p => if i = 0 ∧ p = 0 then Real.log gain else 0
    | .b => 9 / 50
    | .energy => 100
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun i p => if i = 0 ∧ p = 0 then some time else none
  pending := []

private theorem probe_physical {learner teacher ε gain time}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε)
    (positive : 0 < gain) (upper : gain ≤ 11 / 5) :
    PhysicalInvariant (extendParameters learner teacher) (probeStart gain time) := by
  have caps (i : Fin 2) (p : Port) : 11 / 5 ≤ (extendParameters learner teacher i).cap p := by
    have lower := (box.2 i p).1.1
    rcases box.1 with hε | hε
    all_goals rw [hε] at lower
    all_goals norm_num at lower
    all_goals linarith
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    norm_num [UpperRegion, probeStart, auxUpper]
  · intro i p
    change (if i = 0 ∧ p = 0 then Real.log gain else 0) ≤ _
    split
    · exact Real.log_le_log positive (upper.trans (caps i p))
    · exact Real.log_nonneg (by linarith [caps i p])
  · intro i
    norm_num [probeStart]
  · intro i
    norm_num [probeStart]

private theorem probe_ready (gain time : ℝ) (i : Fin 2) : ReadyCoordinates (probeStart gain time) i :=
  ⟨rfl, by norm_num [probeStart], fun _ => ⟨rfl, by norm_num [probeStart, RestBand]⟩⟩

private theorem probe_raw_valid (gain time : ℝ) : RawValid (probeStart gain time) := by
  intro i p origin active
  by_cases atProbe : i = 0 ∧ p = 0
  · have same : time = origin := by simpa [probeStart, atProbe] using active
    subst origin
    change time ≤ time ∧ time ≤ time + 1
    exact ⟨le_rfl, by linarith⟩
  · simp [probeStart, atProbe] at active

private theorem probe_raw_other (gain time : ℝ) (i : Fin 2) (p : Port)
    (other : i ≠ 0 ∨ p ≠ 0) : (probeStart gain time).raw i p = none := by
  have notProbe : ¬ (i = 0 ∧ p = 0) := by tauto
  simp [probeStart, notProbe]

/-- The entire certified high-gain band produces a routed selector dose. -/
theorem prepared_routed_feedback_of_strong_gain {learner teacher ε delay gain}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε) (time : ℝ)
    (strong : 9 / 5 ≤ gain ∧ gain ≤ 11 / 5)
    (delayBounds : ∀ t, (3 / 10 : ℝ) ≤ delay t ∧ delay t ≤ 2 / 5) :
    Nonempty (RoutedFeedback learner teacher delay (probeStart gain time)) := by
  have positive : 0 < gain := by linarith [strong.1]
  have ready := probe_ready gain time 0
  have prepared : PreparedSection (probeStart gain time) 0 :=
    ⟨ready.ready, ready.charge, by norm_num [probeStart], ready.auxiliary⟩
  have logPos : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  exact routed_feedback_exists box (probe_physical box positive strong.2)
    (probe_raw_valid gain time) prepared (probe_ready gain time 1)
    (by simpa [probeStart, Real.exp_log positive] using strong)
    rfl (probe_raw_other gain time) rfl delayBounds
    (by norm_num [probeStart]) (by
      change 0 ≤ Real.log (6 / 5 : ℝ) + 1 / 1000
      linarith)

/-- The original gain-two example is an instance of the strong band. -/
theorem prepared_routed_feedback_exists {learner teacher ε delay}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε) (time : ℝ)
    (delayBounds : ∀ t, (3 / 10 : ℝ) ≤ delay t ∧ delay t ≤ 2 / 5) :
    Nonempty (RoutedFeedback learner teacher delay (probeStart 2 time)) :=
  prepared_routed_feedback_of_strong_gain box time (by norm_num) delayBounds

private theorem prepared_weak_probe_cycle {learner teacher ε delay gain}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε) (time : ℝ)
    (positive : 0 < gain) (weak : gain ≤ 7 / 6) :
    Nonempty (WeakInputCycle (extendParameters learner teacher) (feedbackRouter delay)
      (probeStart gain time) 0 0) := by
  have small : Real.log gain ≤ Real.log (6 / 5 : ℝ) :=
    Real.log_le_log positive (by linarith)
  exact weak_input_cycle_exists (route := feedbackRouter delay)
    (probeStart gain time) box (probe_physical box positive (by linarith))
    (probe_raw_valid gain time) 0 0 (probe_ready gain time)
    (by simpa [probeStart, Real.exp_log positive] using weak)
    (by simpa [probeStart] using le_trans small (by linarith :
      Real.log (6 / 5 : ℝ) ≤ Real.log (6 / 5) + 1 / 1000))
    rfl (probe_raw_other gain time) (by simp [probeStart])

private theorem prepared_probe_initially_below (gain time : ℝ) :
    InitiallyBelowReady (probeStart gain time) := by
  intro i coordinate ready
  cases coordinate with
  | q => norm_num [probeStart]
  | m _ => norm_num [probeStart]
  | z _ => exact False.elim ready
  | b => exact False.elim ready
  | energy => exact False.elim ready

/-- The weak-gain case also admits a complete upward-crossing execution. -/
theorem prepared_weak_probe_crossing_exists {learner teacher ε delay gain}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε) (time : ℝ)
    (positive : 0 < gain) (weak : gain ≤ 7 / 6) :
    ∃ (final : Snapshot 2) (crossing : CrossingExecution (extendParameters learner teacher)
      (feedbackRouter delay) (probeStart gain time) final),
      CrossingCompleteThrough crossing (time + 15 / 2) ∧
      crossing.execution.ledger.emissions = [] ∧
      final.x 1 (.z 2) = (probeStart gain time).x 1 (.z 2) := by
  obtain ⟨response⟩ := prepared_weak_probe_cycle (delay := delay) box time positive weak
  have physical := probe_physical box (time := time) positive (by linarith)
  let crossing := response.execution.toCrossing (prepared_probe_initially_below gain time)
    box physical response.contacts_transversal
  refine ⟨response.final, crossing, ?_, ?_, ?_⟩
  · exact CompleteThrough.toCrossing response.execution response.complete
      (prepared_probe_initially_below gain time) box physical response.contacts_transversal
  · change response.execution.toWeak.ledger.emissions = []
    simpa using response.emissions
  · exact selector_unchanged_without_learner_fire response.execution rfl rfl
      ((probe_ready gain time 1).auxiliary 2).2 rfl (by simp [response.emissions])

/-- With the same probe, router and unit learner gain, there is a complete
silent response with no delivery and no selector change. -/
theorem prepared_silent_probe_exists {learner teacher ε delay}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε) (time : ℝ) :
    ∃ (final : Snapshot 2) (execution : Execution (extendParameters learner teacher) (feedbackRouter delay)
      (probeStart 1 time) final),
      CompleteThrough execution (time + 15 / 2) ∧ execution.ledger.emissions = [] ∧
        execution.deliveries = [] ∧ final.x 1 (.z 2) = (probeStart 1 time).x 1 (.z 2) := by
  obtain ⟨response⟩ := prepared_weak_probe_cycle (delay := delay) box time
    (gain := 1) (by norm_num) (by norm_num)
  refine ⟨response.final, response.execution, response.complete, response.emissions,
    response.deliveries, ?_⟩
  exact selector_unchanged_without_learner_fire response.execution rfl rfl
    ((probe_ready 1 time 1).auxiliary 2).2 rfl (by simp [response.emissions])

/-- If the lesson outcome is supplied by the corresponding gain band, the
    learner's FIRE reports failure, and the same failure sets the teacher's
    selector. All complete executions through the witness horizon agree.
    The gain encoding is an input; this theorem supplies its physical readout. -/
theorem prepared_probe_reports_failure {learner teacher ε delay gain}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε) (time : ℝ)
    (experiment : Experiment) (trial : Memory)
    (delayBounds : ∀ t, (3 / 10 : ℝ) ≤ delay t ∧ delay t ≤ 2 / 5)
    (unselected : trial.focusOnPractice = false)
    (failedGain : experiment.preparationProbePasses trial = false →
      9 / 5 ≤ gain ∧ gain ≤ 11 / 5)
    (passedGain : experiment.preparationProbePasses trial = true →
      0 < gain ∧ gain ≤ 7 / 6) :
    ∃ (T : ℝ) (witnessFinal : Snapshot 2) (witness : Execution (extendParameters learner teacher)
      (feedbackRouter delay) (probeStart gain time) witnessFinal),
      CompleteThrough witness T ∧
      ∀ (final : Snapshot 2) (execution : Execution (extendParameters learner teacher)
        (feedbackRouter delay) (probeStart gain time) final), CompleteThrough execution T →
        ((∃ fire, (0, fire) ∈ execution.ledger.emissions) ↔
          experiment.preparationProbePasses trial = false) ∧
        final.x 1 (.z 2) = (probeStart gain time).x 1 (.z 2) +
          (if experiment.preparationProbePasses trial then 0 else 3 / 5) ∧
        ((probeStart gain time).x 1 (.z 2) + 3 / 10 < final.x 1 (.z 2) ↔
          (experiment.commit true trial).focusOnPractice = true) := by
  cases result : experiment.preparationProbePasses trial with
  | false =>
    have strong := failedGain result
    have physical := probe_physical box (time := time) (by linarith [strong.1]) strong.2
    obtain ⟨feedback⟩ := prepared_routed_feedback_of_strong_gain box time strong delayBounds
    refine ⟨_, feedback.final, feedback.execution, feedback.complete, ?_⟩
    intro final execution complete
    obtain ⟨fires, _, _, dose, _⟩ := feedback.every_complete box physical rfl execution complete
    simp [fires, dose, Experiment.commit, result, unselected]
    linarith
  | true =>
    obtain ⟨positive, weak⟩ := passedGain result
    have physical := probe_physical box (time := time) positive (by linarith)
    obtain ⟨response⟩ := prepared_weak_probe_cycle (delay := delay) box time positive weak
    refine ⟨_, response.final, response.execution, response.complete, ?_⟩
    intro final execution complete
    have same := execution.observational_unique response.execution box physical complete
      response.complete
    have fires : execution.ledger.emissions = [] :=
      List.perm_nil.mp (response.emissions ▸ same.2)
    have unchanged := selector_unchanged_without_learner_fire execution rfl rfl
      ((probe_ready gain time 1).auxiliary 2).2 rfl (by simp [fires])
    simp [fires, unchanged, Experiment.commit, result, unselected]
    linarith

end RecursiveLearning.Native
