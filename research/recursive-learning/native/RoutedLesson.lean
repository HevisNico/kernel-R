import LessonProbe
import KernelR.HybridCausalHeadSignals

/-! The actual lesson and readout drive the teacher in one causal execution.
    Only learner FIREs at or after readout admission can send feedback. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid

noncomputable def lessonSelectorContacts (time : ℝ) (delay : ℝ → ℝ) : HeadRoutes 1 :=
  fun i t => if time + 17 ≤ t then selectorContacts delay i t else []

noncomputable abbrev lessonSelectorRouter (time : ℝ) (delay : ℝ → ℝ) : Router 2 :=
  prependRouted (fun _ _ => []) (lessonSelectorContacts time delay)

noncomputable def routedLessonStart (prepared : Bool) (time : ℝ) : Snapshot 2 :=
  let learner := lessonProbeStart prepared time
  learner.prependQueued (preparedTeacher time) (learner.pending.map Delivery.succ)

private def selectorQueue (delay : ℝ → ℝ) (fire : Option ℝ) : List (Delivery 1) :=
  fire.toList.map (fun t => ⟨0, 2, t + delay t⟩)

private theorem lesson_contacts_strict {time : ℝ} {delay : ℝ → ℝ}
    (positive : ∀ t, 0 < delay t) : StrictHeadRoutes (lessonSelectorContacts time delay) := by
  intro i t d member
  by_cases after : time + 17 ≤ t
  · simp [lessonSelectorContacts, after, selectorContacts] at member
    subst d
    exact lt_add_of_pos_right t (positive t)
  · simp [lessonSelectorContacts, after] at member

theorem lesson_router_strict {time : ℝ} {delay : ℝ → ℝ}
    (positive : ∀ t, 0 < delay t) : StrictCausalRouter (lessonSelectorRouter time delay) := by
  intro i t d member
  cases i using Fin.cases with
  | zero => exact False.elim (List.not_mem_nil member)
  | succ i =>
    change d ∈ (lessonSelectorContacts time delay i t).map (Delivery.head (n := 1)) at member
    obtain ⟨token, present, rfl⟩ := List.mem_map.mp member
    exact lesson_contacts_strict positive i t token present

private theorem readout_label {θ prepared time finish}
    (run : LessonProbeRun θ prepared time finish) (delay : ℝ → ℝ) :
    ∃ fire : Option ℝ,
      fire.isSome = !prepared ∧
      (∀ f, fire = some f → time + 17 ≤ f ∧ f < time + 18) ∧
      (∀ f, time + 17 ≤ f → (f ∈ run.execution.emissionTimes 0 ↔ fire = some f)) ∧
      run.execution.headInputQueue (lessonSelectorContacts time delay) = selectorQueue delay fire := by
  have prior : run.admission.execution.headInputQueue (lessonSelectorContacts time delay) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro event member
    have before := run.admission.earlyEmissions event member
    simp [lessonSelectorContacts, not_le.mpr before]
  have actual :
      ∃ fire : Option ℝ, fire.isSome = !prepared ∧
        run.readout.ledger.emissions = fire.toList.map (fun t => ((0 : Fin 1), t)) := by
    cases prepared with
    | false =>
      obtain ⟨fire, emissions⟩ := run.emissions
      exact ⟨some fire, rfl, emissions⟩
    | true => exact ⟨none, rfl, run.emissions⟩
  obtain ⟨fire, reported, emissions⟩ := actual
  have window (f : ℝ) (same : fire = some f) : time + 17 ≤ f ∧ f < time + 18 := by
    have member : (0, f) ∈ run.readout.ledger.emissions := by simp [emissions, same]
    refine ⟨?_, run.earlyReadout _ member⟩
    rw [← run.admission.complete.1]
    exact (run.readout.emission_time_bounds _ member).1
  refine ⟨fire, reported, window, ?_, ?_⟩
  · intro f after
    have same : f ∈ run.execution.emissionTimes 0 ↔ (0, f) ∈ run.execution.ledger.emissions := by
      constructor
      · intro member
        obtain ⟨⟨i, t⟩, present, rfl⟩ := List.mem_map.mp member
        have h := List.mem_filter.mp present
        have index : i = 0 := Subsingleton.elim _ _
        simpa [index] using h.1
      · intro member
        exact List.mem_map.mpr ⟨(0, f), List.mem_filter.mpr ⟨member, by simp⟩, rfl⟩
    rw [same, LessonProbeRun.execution, Execution.emissions_append, List.mem_append]
    have absent : (0, f) ∉ run.admission.execution.ledger.emissions :=
      fun member => (not_lt_of_ge after) (run.admission.earlyEmissions _ member)
    cases fire <;> simp [absent, emissions, eq_comm]
  · rw [Execution.headInputQueue, LessonProbeRun.execution, Execution.emissions_append, List.flatMap_append]
    change run.admission.execution.headInputQueue (lessonSelectorContacts time delay) ++ _ = _
    rw [prior, List.nil_append, emissions]
    cases fire with
    | none => rfl
    | some f => simp [lessonSelectorContacts, (window f rfl).1, selectorContacts, selectorQueue]

private structure SelectorResponse (θ : Fin 1 → Parameters) (time : ℝ)
    (delay : ℝ → ℝ) (fire : Option ℝ) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => [])
    {(preparedTeacher time) with pending := selectorQueue delay fire} final
  complete : CompleteThrough execution (time + 26)
  transversal : execution.ContactsTransversal
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = selectorQueue delay fire
  empty : final.pending = []
  gains : ∀ p, final.x 0 (.z p) = if p = 2 ∧ fire.isSome then 3 / 5 else 0
  ready : ReadyCoordinates final 0
  rawNone : ∀ p, final.raw 0 p = none

private theorem selector_response_exists {θ ε time delay fire}
    (box : @PhysicalBox 1 θ ε)
    (window : ∀ f, fire = some f → time + 17 ≤ f ∧ f < time + 18)
    (bounds : ∀ f, (3 / 10 : ℝ) ≤ delay f ∧ delay f ≤ 2 / 5) :
    Nonempty (SelectorResponse θ time delay fire) := by
  let start : Snapshot 1 := {preparedTeacher time with pending := selectorQueue delay fire}
  have ready (i : Fin 1) : ReadyCoordinates start i :=
    ⟨rfl, by norm_num [start, preparedTeacher],
      fun _ => ⟨rfl, by norm_num [start, preparedTeacher, RestBand]⟩⟩
  have rawNone (i : Fin 1) (p : Port) : start.raw i p = none := rfl
  cases fire with
  | none =>
    have later : start.time < time + 26 := by change time < time + 26; linarith
    obtain ⟨wait, complete, transverse, silent, noDeliveries⟩ := quiet_ready_tail_exists (θ := θ)
      (s := start) (T := time + 26) later ready rawNone rfl
    exact ⟨⟨_, wait, complete, transverse, silent, noDeliveries, rfl, fun p => by simp [quietAt,
      quietValues, start, preparedTeacher],
      quietAt_ready_coordinates start 0 (ready 0) later.le, rawNone 0⟩⟩
  | some f =>
    let due := f + delay f
    have positiveLog := Real.log_nonneg (show (1 : ℝ) ≤ 6 / 5 by norm_num)
    have after := window f rfl
    obtain ⟨dose⟩ := port_dose_exists (route := fun _ _ => []) (start := start)
      (port := 2) (due := due) (later := []) box
      (preparedTeacher_physical box time _) (by simp [RawValid, start, preparedTeacher])
      (ready 0) (rawNone 0) (by change time < f + delay f; linarith [(bounds f).1])
      rfl (by simp) (by change Real.exp 0 ≤ _; norm_num) (by change 0 ≤ _; linarith)
    have later : dose.final.time < time + 26 := by
      rw [dose.complete.1]
      dsimp [due]
      linarith [after.2, (bounds f).2]
    obtain ⟨wait, complete, transverse, silent, noDeliveries⟩ := quiet_ready_tail_exists (θ := θ)
      (T := time + 26) later
      (fun i => by simpa only [Subsingleton.elim i 0] using dose.ready)
      (fun i p => by simpa only [Subsingleton.elim i 0] using dose.rawNone p) dose.pending
    refine ⟨⟨_, dose.execution.append wait, complete,
      (Execution.contactsTransversal_append _ _).2 ⟨dose.transversal, transverse⟩,
      by rw [Execution.emissions_append, dose.emissions, silent]; rfl,
      by rw [Execution.deliveries_append, dose.deliveries, noDeliveries]; rfl,
      dose.pending, ?_, quietAt_ready_coordinates dose.final 0 dose.ready later.le, dose.rawNone⟩⟩
    intro p
    change dose.final.x 0 (.z p) = _
    rw [dose.gain]
    simp [start, preparedTeacher]

structure RoutedLessonRun (learner : Fin 1 → Parameters) (teacher : Parameters)
    (prepared : Bool) (time : ℝ) (delay : ℝ → ℝ) where
  final : Snapshot 2
  execution : Execution (prependParameters (fun _ => teacher) learner)
    (lessonSelectorRouter time delay) (routedLessonStart prepared time) final
  complete : CompleteThrough execution (time + 26)
  transversal : execution.ContactsTransversal
  fire : Option ℝ
  reported : fire.isSome = !prepared
  readout : ∀ f, time + 17 ≤ f → (f ∈ execution.emissionTimes 1 ↔ fire = some f)
  fireWindow : ∀ f, fire = some f → time + 17 ≤ f ∧ f < time + 18
  deliveries : execution.deliveries.Perm
    ((lessonProbeQueue prepared time).map Delivery.succ ++
      fire.toList.map (fun f => ⟨0, 2, f + delay f⟩))
  pendingEmpty : final.pending = []
  teacherGains : ∀ p, final.x 0 (.z p) = if p = 2 ∧ prepared = false then 3 / 5 else 0
  teacherReady : ReadyCoordinates final 0
  teacherRawNone : ∀ p, final.raw 0 p = none
  learnerDispatch : LearnerDispatchState (final.cellProjection 1 [])

/-- There is one complete network history. The teacher's local input
    calendar comes from the actual learner trace. Only the external lesson
    inputs are present in the initial operational queue. -/
theorem routed_lesson_run_exists {learner teacher ε delay}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε)
    (prepared : Bool) (time : ℝ)
    (bounds : ∀ f, (3 / 10 : ℝ) ≤ delay f ∧ delay f ≤ 2 / 5) :
    Nonempty (RoutedLessonRun learner teacher prepared time delay) := by
  obtain ⟨run, learnerDispatch⟩ := lesson_probe_dispatch_state_exists box.extend_old prepared time
  obtain ⟨fire, reported, window, readout, queue⟩ := readout_label run delay
  obtain ⟨response⟩ := selector_response_exists box.extend_new (delay := delay) window bounds
  let head := {preparedTeacher time with pending := selectorQueue delay fire}
  have balance := HeadQueueBalance.initial run.execution head (lessonSelectorContacts time delay) queue.symm
  have strict := lesson_contacts_strict (time := time) (fun f => by linarith [(bounds f).1])
  obtain ⟨weave⟩ := run.execution.prepend_causal_result response.execution rfl
    (run.complete_execution.1.trans response.complete.1.symm) (lessonSelectorContacts time delay) strict
    ((lessonProbeQueue prepared time).map Delivery.succ) balance
  refine ⟨{
    final := _
    execution := weave.execution
    complete := weave.complete run.complete_execution response.complete
    transversal := weave.contacts_transversal run.contacts_transversal response.transversal
    fire := fire
    reported := reported
    readout := ?_
    fireWindow := window
    deliveries := ?_
    pendingEmpty := weave.pending_empty run.pendingEmpty response.empty
    teacherGains := ?_
    teacherReady := ⟨response.ready.ready,response.ready.charge,response.ready.auxiliary⟩
    teacherRawNone := response.rawNone
    learnerDispatch := ⟨
      fun i p => learnerDispatch.rawNone 0 p, learnerDispatch.auxiliary, ?_⟩
  }⟩
  · intro f after
    change f ∈ weave.execution.emissionTimes ((0 : Fin 1).succ) ↔ fire = some f
    rw [weave.tail_emission_times 0]
    exact readout f after
  · have learnerDeliveries : run.execution.deliveries = lessonProbeQueue prepared time := by
      rw [LessonProbeRun.execution, Execution.deliveries_append, run.admission.deliveries]
      have none := run.readout.deliveries_perm_sources _ run.complete
        (by simp [run.admission.queue]) (fun _ _ => rfl)
      rw [run.admission.queue] at none
      rw [List.perm_nil.mp none, List.append_nil]
    apply Multiset.coe_eq_coe.mp
    refine weave.trace.deliveries.trans ?_
    rw [learnerDeliveries, response.deliveries, ← Multiset.coe_add]
    simp [selectorQueue, List.map_map, Function.comp_def, Delivery.head]
  · intro p
    change response.final.x 0 (.z p) = _
    rw [response.gains, reported]
    cases prepared <;> simp
  · rcases learnerDispatch.main with ready | slow
    · exact Or.inl ⟨ready.ready,ready.charge,ready.auxiliary⟩
    · exact Or.inr slow

/-- The selector's native readout agrees with the discrete validation at the
    last preparation slot. Half a dose separates its two physical values. -/
theorem RoutedLessonRun.selector_reports_failure {learner teacher prepared time delay}
    (run : RoutedLessonRun learner teacher prepared time delay) :
    3 / 10 < run.final.x 0 (.z 2) ↔
      (lastPreparationLesson prepared).passes Example.experiment.validation = false := by
  rw [run.teacherGains, lastPreparationLesson_passes]
  cases prepared <;> norm_num

theorem routed_lesson_physical {learner teacher ε prepared time}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε) :
    PhysicalBox (prependParameters (fun _ => teacher) learner) ε ∧
      PhysicalInvariant (prependParameters (fun _ => teacher) learner) (routedLessonStart prepared time) ∧
      InitiallyBelowReady (routedLessonStart prepared time) := by
  have head := preparedTeacher_physical box.extend_new time []
  have tail := lessonProbe_physical (prepared := prepared) (time := time) box.extend_old
  refine ⟨⟨box.1, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i p
    fin_cases i
    · exact box.2 1 p
    · exact box.2 0 p
  · intro i
    fin_cases i
    · exact head.region 0
    · exact tail.region 0
  · intro i p
    fin_cases i
    · exact head.gain_cap 0 p
    · exact tail.gain_cap 0 p
  · intro i
    fin_cases i
    · exact head.recovery_cap 0
    · exact tail.recovery_cap 0
  · intro i
    fin_cases i
    · exact head.reserve 0
    · exact tail.reserve 0
  · intro i c ready
    fin_cases i
    · cases c with
      | q => norm_num [routedLessonStart, Snapshot.prependQueued, Snapshot.prependQuiet,
          Snapshot.requeue, preparedTeacher]
      | m _ => norm_num [routedLessonStart, Snapshot.prependQueued, Snapshot.prependQuiet,
          Snapshot.requeue, preparedTeacher]
      | z _ => exact False.elim ready
      | b => exact False.elim ready
      | energy => exact False.elim ready
    · exact lessonProbe_initial prepared time 0 c ready

/-- A single geometric history covers the lesson, the readout FIRE when
    preparation is omitted, the delivery and the teacher memory update. -/
theorem routed_lesson_crossing_exists {learner teacher ε delay}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε)
    (prepared : Bool) (time : ℝ)
    (bounds : ∀ f, (3 / 10 : ℝ) ≤ delay f ∧ delay f ≤ 2 / 5) :
    ∃ (run : RoutedLessonRun learner teacher prepared time delay)
      (crossing : CrossingExecution (prependParameters (fun _ => teacher) learner)
        (lessonSelectorRouter time delay) (routedLessonStart prepared time) run.final),
      crossing.execution = run.execution.toWeak ∧ CrossingCompleteThrough crossing (time + 26) := by
  obtain ⟨run⟩ := routed_lesson_run_exists box prepared time bounds
  obtain ⟨orderedBox, physical, initial⟩ := routed_lesson_physical (prepared := prepared) (time := time) box
  exact ⟨run, run.execution.toCrossing initial orderedBox physical run.transversal, rfl,
    run.complete.toCrossing run.execution initial orderedBox physical run.transversal⟩

private theorem deliveries_of_agreement {learner teacher prepared time delay final}
    (run : RoutedLessonRun learner teacher prepared time delay)
    (execution : Execution (prependParameters (fun _ => teacher) learner) (lessonSelectorRouter time delay)
      (routedLessonStart prepared time) final)
    (endpoint : run.final.ObservationalEq final)
    (fires : run.execution.ledger.emissions.Perm execution.ledger.emissions) :
    run.execution.deliveries.Perm execution.deliveries := by
  have empty := List.perm_nil.mp (run.pendingEmpty ▸ endpoint.pending.symm)
  have left := run.execution.token_balance
  have right := execution.token_balance
  rw [run.pendingEmpty, Multiset.coe_nil, zero_add] at left
  rw [empty, Multiset.coe_nil, zero_add] at right
  have issued := Multiset.coe_eq_coe.mpr
    (fires.flatMap_right (fun event => lessonSelectorRouter time delay event.1 event.2))
  exact Multiset.coe_eq_coe.mp (left.trans ((congrArg (_ + ·) issued).trans right.symm))

/-- All complete first-contact executions have the same endpoint, FIREs and
    deliveries as the constructed lesson and selector update. -/
theorem RoutedLessonRun.every_complete {learner teacher ε prepared time delay final}
    (run : RoutedLessonRun learner teacher prepared time delay)
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε)
    (execution : Execution (prependParameters (fun _ => teacher) learner) (lessonSelectorRouter time delay)
      (routedLessonStart prepared time) final)
    (complete : CompleteThrough execution (time + 26)) :
    run.final.ObservationalEq final ∧ run.execution.ledger.emissions.Perm execution.ledger.emissions ∧
      run.execution.deliveries.Perm execution.deliveries := by
  obtain ⟨orderedBox, physical, _⟩ := routed_lesson_physical (prepared := prepared) (time := time) box
  obtain ⟨endpoint, fires⟩ :=
    run.execution.observational_unique execution orderedBox physical run.complete complete
  exact ⟨endpoint, fires, deliveries_of_agreement run execution endpoint fires⟩

/-- Every complete crossing history has the same endpoint, FIREs and deliveries.
    Refinement retains each of its actual paths and delivery jumps. -/
theorem RoutedLessonRun.every_crossing_complete {learner teacher ε prepared time delay final}
    (run : RoutedLessonRun learner teacher prepared time delay)
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε)
    (positive : ∀ t, 0 < delay t)
    (crossing : CrossingExecution (prependParameters (fun _ => teacher) learner)
      (lessonSelectorRouter time delay) (routedLessonStart prepared time) final)
    (complete : CrossingCompleteThrough crossing (time + 26)) :
    ∃ native : Execution (prependParameters (fun _ => teacher) learner) (lessonSelectorRouter time delay)
        (routedLessonStart prepared time) final,
      native.toWeak = crossing.execution ∧ run.final.ObservationalEq final ∧
      run.execution.ledger.emissions.Perm crossing.execution.ledger.emissions ∧
      run.execution.deliveries.Perm native.deliveries := by
  obtain ⟨orderedBox, physical, initial⟩ := routed_lesson_physical (prepared := prepared) (time := time) box
  obtain ⟨native, same⟩ := crossing.execution.toNative_of_transverse_completion run.execution
    (lesson_router_strict positive) orderedBox physical run.complete run.transversal (le_of_eq complete.1)
  have weakComplete := complete.toWeak_of_native crossing native same initial orderedBox physical
  obtain ⟨endpoint, fires⟩ := run.execution.observational_unique_weak orderedBox crossing.execution physical
    run.complete run.transversal weakComplete
  refine ⟨native, same, endpoint, fires, deliveries_of_agreement run native endpoint ?_⟩
  simpa only [← same, Execution.toWeak_ledger] using fires

end RecursiveLearning.Native
