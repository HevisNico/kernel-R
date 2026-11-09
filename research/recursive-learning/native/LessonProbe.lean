import Feedback
import KernelR.HybridContactTransversalityCuts
import KernelR.HybridLowRecoverySlowSpan
import KernelR.HybridProtectedInputShortCycle

/-! The last preparation pulse controls exposure to a common diagnostic pulse.
    Both runs start with the same gains. The later probe reads the learned gain. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

def lessonProbeQueue (prepared : Bool) (time : ℝ) : List (Delivery 1) :=
  (if prepared then [⟨0, 1, time + 1⟩] else []) ++
    [⟨0, 0, time + 9⟩, ⟨0, 0, time + 17⟩]

noncomputable def lessonProbeStart (prepared : Bool) (time : ℝ) : Snapshot 1 where
  time := time
  x := fun _ c => match c with
    | .q => 1 / 10
    | .m _ => 1 / 40
    | .z p => if p = 1 then Real.log 2 else 0
    | .b => 2 / 25
    | .energy => 100
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ _ => none
  pending := lessonProbeQueue prepared time

private theorem lessonProbe_physical {θ ε prepared time} (box : @PhysicalBox 1 θ ε) :
    PhysicalInvariant θ (lessonProbeStart prepared time) := by
  have cap (i : Fin 1) (p : Port) : 2 ≤ (θ i).cap p := by
    have lower := (box.2 i p).1.1
    rcases box.1 with h | h
    all_goals rw [h] at lower
    all_goals norm_num at lower
    all_goals linarith
  refine ⟨fun i => by norm_num [UpperRegion, lessonProbeStart, auxUpper], ?_,
    fun i => by norm_num [lessonProbeStart], fun i => by norm_num [lessonProbeStart]⟩
  intro i p
  change (if p = 1 then Real.log 2 else 0) ≤ Real.log ((θ i).cap p)
  split
  · exact Real.log_le_log (by norm_num) (cap i p)
  · exact Real.log_nonneg (by linarith [cap i p])

private theorem lessonProbe_ready (prepared : Bool) (time : ℝ) (i : Fin 1) :
    ReadyCoordinates (lessonProbeStart prepared time) i :=
  ⟨rfl, by norm_num [lessonProbeStart], fun _ => ⟨rfl, by norm_num [lessonProbeStart, RestBand]⟩⟩

private theorem lessonProbe_initial (prepared : Bool) (time : ℝ) :
    InitiallyBelowReady (lessonProbeStart prepared time) := by
  intro i c ready
  cases c with
  | q => norm_num [lessonProbeStart]
  | m _ => norm_num [lessonProbeStart]
  | z _ => exact False.elim ready
  | b => exact False.elim ready
  | energy => exact False.elim ready

structure LessonProbeAdmission (θ : Fin 1 → Parameters) (prepared : Bool) (time : ℝ) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) (lessonProbeStart prepared time) final
  complete : CompleteThrough execution (time + 17)
  transversal : execution.ContactsTransversal
  ready : ∀ i, ReadyCoordinates final i
  rawValid : RawValid final
  active : final.raw 0 0 = some final.time
  otherRaw : ∀ i p, i ≠ 0 ∨ p ≠ 0 → final.raw i p = none
  queue : final.pending = []
  deliveries : execution.deliveries = lessonProbeQueue prepared time
  earlyEmissions : ∀ e ∈ execution.ledger.emissions, e.2 < time + 17
  logGain : final.x 0 (.z 0) = if prepared then 0 else 3 / 5

private theorem unprepared_admission_exists {θ ε} (box : @PhysicalBox 1 θ ε) (time : ℝ) :
    Nonempty (LessonProbeAdmission θ false time) := by
  let start := lessonProbeStart false time
  let readout : Delivery 1 := ⟨0, 0, time + 17⟩
  have logPos : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨dose⟩ := port_dose_exists (θ := θ) (route := fun _ _ => []) (start := start)
    (port := 0) (due := time + 9) (later := [readout]) box
    (lessonProbe_physical box) (by simp [RawValid, start, lessonProbeStart])
    (lessonProbe_ready false time 0) (fun _ => rfl)
    (by change time < time + 9; linarith) rfl (by simp [readout]; linarith)
    (by change Real.exp 0 ≤ _; norm_num) (by change 0 ≤ _; linarith)
  have later : dose.final.time < readout.due := by
    rw [dose.complete.1]
    dsimp [readout]
    linarith
  obtain ⟨probe⟩ := quiet_source_arrival_exists (route := fun _ _ => []) box dose.final readout []
    dose.physical dose.rawValid (fun i => by simpa only [Subsingleton.elim i 0] using dose.ready)
    (fun i p => by simpa only [Subsingleton.elim i 0] using dose.rawNone p) later dose.pending (by simp)
  refine ⟨{
    final := probe.final
    execution := dose.execution.append probe.execution
    complete := probe.complete (by simp)
    transversal := (dose.execution.contactsTransversal_append _).2 ⟨dose.transversal, probe.contacts_transversal⟩
    ready := probe.ready
    rawValid := probe.raw_valid
    active := probe.raw_active
    otherRaw := probe.raw_other
    queue := probe.pending
    deliveries := ?_
    earlyEmissions := ?_
    logGain := ?_
  }⟩
  · rw [Execution.deliveries_append, dose.deliveries, probe.deliveries]
    rfl
  · rw [Execution.emissions_append, dose.emissions, probe.emissions]
    simp
  · rw [probe.gain_preserved, dose.gain 0]
    norm_num [start, lessonProbeStart]

private theorem prepared_admission_exists {θ ε} (box : @PhysicalBox 1 θ ε) (time : ℝ) :
    Nonempty (LessonProbeAdmission θ true time) := by
  let start := lessonProbeStart true time
  let prep : Delivery 1 := ⟨0, 1, time + 1⟩
  let diagnostic : Delivery 1 := ⟨0, 0, time + 9⟩
  let readout : Delivery 1 := ⟨0, 0, time + 17⟩
  obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := fun _ _ => []) box start prep [diagnostic, readout]
    (lessonProbe_physical box) (by simp [RawValid, start, lessonProbeStart])
    (lessonProbe_ready true time) (fun _ _ => rfl) (by change time < time + 1; linarith) rfl
    (by simp [diagnostic, readout, prep])
  have strong : 9 / 5 ≤ Real.exp (arrival.final.x 0 (.z 1)) ∧
      Real.exp (arrival.final.x 0 (.z 1)) ≤ 11 / 5 := by
    rw [arrival.gain_preserved]
    change 9 / 5 ≤ Real.exp (Real.log 2) ∧ Real.exp (Real.log 2) ≤ 11 / 5
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have future : ∀ d ∈ arrival.final.pending, arrival.final.time + 31 / 4 ≤ d.due := by
    rw [arrival.pending, arrival.date]
    simp [diagnostic, readout, prep]
    constructor <;> linarith
  have low : 7999 / 100000 ≤ arrival.final.x 0 .b ∧ arrival.final.x 0 .b ≤ 8001 / 100000 := by
    rw [arrival.recovery_preserved]
    change 7999 / 100000 ≤ (2 / 25 : ℝ) ∧ 2 / 25 ≤ (8001 / 100000 : ℝ)
    norm_num
  obtain ⟨fire⟩ := first_mid_learned_fire_exists arrival.final box arrival.physical arrival.raw_valid 0 1
    arrival.ready strong arrival.raw_active arrival.raw_other future
  obtain ⟨fast⟩ := fire.mid_learned_fast_end_exists box (arrival.ready 0) strong.2
    (fun p hp => arrival.raw_other 0 p (Or.inr hp)) future
  have fastQueue : fast.final.pending = [diagnostic, readout] := by
    rw [fast.pending, fire.pending, arrival.pending]
    rfl
  have fastBefore : fast.final.time ≤ diagnostic.due := by
    rw [fast.date, fire.date, arrival.date]
    dsimp [diagnostic, prep]
    linarith [fire.deadline]
  obtain ⟨slow⟩ := fire.low_recovery_slow_span_exists box fast (arrival.ready 0) strong.2 low diagnostic.due
    fastBefore (by rw [arrival.date]; dsimp [diagnostic, prep]; linarith)
    (by rw [fastQueue]; norm_num [diagnostic, readout])
  have near : arrival.final.time + 79 / 10 ≤ diagnostic.due := by
    rw [arrival.date]
    dsimp [diagnostic, prep]
    linarith
  let active : Snapshot 1 :=
    {(setRaw slow.final 0 0 (some slow.final.time)) with pending := [readout]}
  let admitDiagnostic : Jump (fun _ _ => []) slow.final active :=
    .arrive slow.final diagnostic [] [readout] (slow.pending.trans fastQueue) slow.date.symm (slow.raw_none 0 0)
  let diagnosticMove : Execution θ (fun _ _ => []) slow.final active :=
    .cons (.jump admitDiagnostic) (.nil _)
  have activePhysical := diagnosticMove.physical_invariant box slow.physical
  have activeRaw := diagnosticMove.raw_valid slow.raw_valid
  have activeLow : 7999 / 100000 ≤ active.x 0 .b ∧ active.x 0 .b ≤ 8001 / 100000 := by
    change 7999 / 100000 ≤ slow.final.x 0 .b ∧ slow.final.x 0 .b ≤ 8001 / 100000
    rw [slow.recovery, fast.recovery, fire.recovery_preserved]
    exact low
  have activeOther (p : Port) (other : p ≠ 0) : active.raw 0 p = none := by
    change (setRaw slow.final 0 0 (some slow.final.time)).raw 0 p = none
    rw [raw_update_other _ _ _ _ _ _ (Or.inr other)]
    exact slow.raw_none 0 p
  obtain ⟨cycle⟩ := protected_input_short_cycle_exists (route := fun _ _ => []) box active 0
    activePhysical activeRaw slow.main_slow ⟨(slow.near_charge near).1.le,(slow.near_charge near).2.le⟩
    activeLow (fun p => ⟨slow.auxiliary 0 p, slow.rest p⟩)
    (by simp [active, setRaw]) activeOther (by
      intro d hd
      have same : d = readout := List.mem_singleton.mp hd
      subst d
      change slow.final.time + 31 / 4 ≤ readout.due
      rw [slow.date]
      dsimp [diagnostic, readout]
      linarith)
  have later : cycle.final.time < readout.due := by
    rw [cycle.date]
    change slow.final.time + 13 / 2 < readout.due
    rw [slow.date]
    dsimp [diagnostic, readout]
    linarith
  obtain ⟨probe⟩ := quiet_source_arrival_exists (route := fun _ _ => []) box cycle.final readout []
    (cycle.execution.physical_invariant box activePhysical) (cycle.execution.raw_valid activeRaw)
    cycle.ready cycle.raw_none later cycle.pending (by simp)
  let head := ((arrival.execution.append fire.execution).append fast.execution).append slow.execution
  let tail := (diagnosticMove.append cycle.execution).append probe.execution
  have headEmissions : head.ledger.emissions = [(0, fire.final.time)] := by
    simp [head, Execution.emissions_append, arrival.emissions, fire.emissions, fast.emissions, slow.emissions]
    exact fire.date.symm
  have tailEmissions : tail.ledger.emissions = [] := by
    simp [tail, Execution.emissions_append, cycle.emissions, probe.emissions]
    rfl
  refine ⟨{
    final := probe.final
    execution := head.append tail
    complete := probe.complete (by simp)
    transversal := ?_
    ready := probe.ready
    rawValid := probe.raw_valid
    active := probe.raw_active
    otherRaw := probe.raw_other
    queue := probe.pending
    deliveries := ?_
    earlyEmissions := ?_
    logGain := ?_
  }⟩
  · simp only [head, tail, Execution.contactsTransversal_append, arrival.contacts_transversal,
      fire.contacts_transversal, fast.contacts_transversal, slow.contacts_transversal,
      cycle.contacts_transversal, probe.contacts_transversal, true_and, and_true]
    change admitDiagnostic.ContactTransversal θ ∧ True
    exact ⟨trivial, trivial⟩
  · have diagnosticDelivery : diagnosticMove.deliveries = [diagnostic] := rfl
    simp only [head, tail, Execution.deliveries_append, arrival.deliveries, fire.deliveries,
      fast.deliveries, slow.deliveries, diagnosticDelivery, cycle.deliveries, probe.deliveries,
      List.append_nil]
    rfl
  · rw [Execution.emissions_append, headEmissions, tailEmissions]
    intro e member
    have same : e = (0, fire.final.time) := List.mem_singleton.mp member
    subst e
    rw [fire.date, arrival.date]
    dsimp [prep]
    linarith [fire.deadline]
  · rw [probe.gain_preserved, cycle.gains]
    change slow.final.x 0 (.z 0) = 0
    rw [slow.gains, fast.gains, fire.gain_preserved, arrival.gain_preserved]
    rfl

/-- From the same physical state, a different preparation calendar generates
    the two probe gains. No outcome or initial gain is selected by an oracle. -/
theorem lesson_probe_admission_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (prepared : Bool) (time : ℝ) :
    Nonempty (LessonProbeAdmission θ prepared time) := by
  cases prepared
  · exact unprepared_admission_exists box time
  · exact prepared_admission_exists box time

theorem LessonProbeAdmission.gain_every_complete {θ ε prepared time final}
    (admission : LessonProbeAdmission θ prepared time) (box : @PhysicalBox 1 θ ε)
    (execution : Execution θ (fun _ _ => []) (lessonProbeStart prepared time) final)
    (complete : CompleteThrough execution (time + 17)) :
    final.x 0 (.z 0) = if prepared then 0 else 3 / 5 := by
  have same := (execution.observational_unique admission.execution box (lessonProbe_physical box)
    complete admission.complete).1
  rw [same.values, admission.logGain]

private theorem learnedProbe_gain :
    9 / 5 ≤ Real.exp (3 / 5 : ℝ) ∧ Real.exp (3 / 5 : ℝ) ≤ 11 / 5 := by
  constructor
  · have bound := Real.sum_le_exp_of_nonneg (x := (3 / 5 : ℝ)) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at bound
    linarith
  · have bound := Real.exp_le_exp.mpr (show (3 / 5 : ℝ) ≤ Real.log 2 by
      linarith [Real.log_two_gt_d9])
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at bound
    linarith

structure LessonProbeRun (θ : Fin 1 → Parameters) (prepared : Bool) (time : ℝ) where
  admission : LessonProbeAdmission θ prepared time
  final : Snapshot 1
  readout : Execution θ (fun _ _ => []) admission.final final
  complete : CompleteThrough readout (time + 18)
  transversal : readout.ContactsTransversal
  emissions : if prepared then readout.ledger.emissions = []
    else ∃ fire, readout.ledger.emissions = [(0, fire)]

noncomputable def LessonProbeRun.execution {θ prepared time} (run : LessonProbeRun θ prepared time) :
    Execution θ (fun _ _ => []) (lessonProbeStart prepared time) run.final :=
  run.admission.execution.append run.readout

theorem LessonProbeRun.complete_execution {θ prepared time} (run : LessonProbeRun θ prepared time) :
    CompleteThrough run.execution (time + 18) := run.complete

theorem LessonProbeRun.contacts_transversal {θ prepared time} (run : LessonProbeRun θ prepared time) :
    run.execution.ContactsTransversal :=
  (run.admission.execution.contactsTransversal_append run.readout).2
    ⟨run.admission.transversal, run.transversal⟩

theorem LessonProbeRun.fires {θ prepared time} (run : LessonProbeRun θ prepared time) :
    (∃ fire, (0, fire) ∈ run.readout.ledger.emissions) ↔ prepared = false := by
  cases prepared with
  | false =>
    obtain ⟨fire, emissions⟩ := run.emissions
    simp [emissions]
  | true =>
    have emissions : run.readout.ledger.emissions = [] := run.emissions
    simp [emissions]

/-- A full run reports failure by a FIRE after the common readout delivery.
    Any earlier FIRE came from the preparation, before the readout window. -/
theorem LessonProbeRun.reports_failure {θ prepared time} (run : LessonProbeRun θ prepared time) :
    (∃ fire, time + 17 ≤ fire ∧ (0, fire) ∈ run.execution.ledger.emissions) ↔ prepared = false := by
  constructor
  · rintro ⟨fire, after, emitted⟩
    rw [LessonProbeRun.execution, Execution.emissions_append, List.mem_append] at emitted
    rcases emitted with earlier | readout
    · exact False.elim ((not_lt_of_ge after) (run.admission.earlyEmissions _ earlier))
    · exact run.fires.mp ⟨fire, readout⟩
  · intro omitted
    obtain ⟨fire, emitted⟩ := run.fires.mpr omitted
    refine ⟨fire, ?_, ?_⟩
    · rw [← run.admission.complete.1]
      exact (run.readout.emission_time_bounds _ emitted).1
    · rw [LessonProbeRun.execution, Execution.emissions_append]
      exact List.mem_append_right _ emitted

/-- Build the complete readout through a common horizon in both cases, using
    the actual carried gain, charge, and recovery at admission. -/
theorem lesson_probe_run_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (prepared : Bool) (time : ℝ) : Nonempty (LessonProbeRun θ prepared time) := by
  obtain ⟨admission⟩ := lesson_probe_admission_exists box prepared time
  have physical := admission.execution.physical_invariant box (lessonProbe_physical box)
  have date := admission.complete.1
  cases prepared with
  | false =>
    have gain : admission.final.x 0 (.z 0) = 3 / 5 := admission.logGain
    have strong : 9 / 5 ≤ Real.exp (admission.final.x 0 (.z 0)) ∧
        Real.exp (admission.final.x 0 (.z 0)) ≤ 11 / 5 := by
      rw [gain]
      exact learnedProbe_gain
    have noInput : ∀ d ∈ admission.final.pending, admission.final.time + 31 / 4 ≤ d.due := by
      simp [admission.queue]
    obtain ⟨fire⟩ := first_mid_learned_fire_exists admission.final box physical admission.rawValid
      0 0 admission.ready strong admission.active admission.otherRaw noInput
    obtain ⟨fast⟩ := fire.mid_learned_fast_end_exists box (admission.ready 0) strong.2
      (fun p hp => admission.otherRaw 0 p (Or.inr hp)) noInput
    obtain ⟨cut⟩ := fast.execution.before_flow_cut_exists (time + 18)
      (by rw [fire.date, date]; linarith [fire.deadline])
      (by rw [fast.date, fire.date, date]; linarith [fire.early])
    have cutSilent := (List.append_eq_nil_iff.mp (cut.emissions.symm.trans fast.emissions)).1
    refine ⟨⟨admission, cut.state, fire.execution.append cut.cut, cut.complete,
      (Execution.contactsTransversal_append _ _).2
        ⟨fire.contacts_transversal, cut.isPrefix.contacts_transversal fast.contacts_transversal⟩, ?_⟩⟩
    refine ⟨fire.final.time, ?_⟩
    rw [Execution.emissions_append, fire.emissions, cutSilent, List.append_nil]
    exact congrArg (fun t => [(0, t)]) fire.date.symm
  | true =>
    have gain : admission.final.x 0 (.z 0) = 0 := admission.logGain
    have logPos := Real.log_nonneg (show (1 : ℝ) ≤ 6 / 5 by norm_num)
    obtain ⟨response⟩ := weak_input_cycle_exists (route := fun _ _ => []) admission.final box
      physical admission.rawValid 0 0 admission.ready (by rw [gain]; norm_num)
      (by rw [gain]; linarith) admission.active admission.otherRaw (by simp [admission.queue])
    obtain ⟨cut⟩ := response.execution.before_flow_cut_exists (time + 18)
      (by rw [date]; linarith) (by rw [response.date, date]; linarith)
    have silent := (List.append_eq_nil_iff.mp (cut.emissions.symm.trans response.emissions)).1
    exact ⟨⟨admission, cut.state, cut.cut, cut.complete,
      cut.isPrefix.contacts_transversal response.contacts_transversal, silent⟩⟩

/-- The two discrete lessons at the final preparation decision. The physical
    assay implements the varying slot and its readout. -/
def lastPreparationLesson (prepared : Bool) : Lesson :=
  let accepted := Example.experiment.lesson Example.frozenFirst
  { accepted with preparation :=
      if prepared then accepted.preparation else accepted.preparation - 1 }

theorem lastPreparationLesson_passes (prepared : Bool) :
    (lastPreparationLesson prepared).passes Example.experiment.validation = prepared := by
  cases prepared <;> decide

theorem LessonProbeRun.reports_example_failure {θ prepared time} (run : LessonProbeRun θ prepared time) :
    (∃ fire, time + 17 ≤ fire ∧ (0, fire) ∈ run.execution.ledger.emissions) ↔
      (lastPreparationLesson prepared).passes Example.experiment.validation = false := by
  rw [lastPreparationLesson_passes]
  exact run.reports_failure

/-- The result at the readout horizon applies to every complete first-contact
    execution of the same lesson calendar. -/
theorem LessonProbeRun.every_complete {θ ε prepared time final}
    (run : LessonProbeRun θ prepared time) (box : @PhysicalBox 1 θ ε)
    (execution : Execution θ (fun _ _ => []) (lessonProbeStart prepared time) final)
    (complete : CompleteThrough execution (time + 18)) :
    (∃ fire, time + 17 ≤ fire ∧ (0, fire) ∈ execution.ledger.emissions) ↔ prepared = false := by
  have same := (execution.observational_unique run.execution box (lessonProbe_physical box)
    complete run.complete_execution).2
  simp only [same.mem_iff]
  exact run.reports_failure

/-- The complete preparation and readout histories also realize the
    written model's upward-crossing rule. -/
theorem lesson_probe_crossing_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (prepared : Bool) (time : ℝ) :
    ∃ (run : LessonProbeRun θ prepared time)
      (crossing : CrossingExecution θ (fun _ _ => []) (lessonProbeStart prepared time) run.final),
      crossing.execution = run.execution.toWeak ∧
      CrossingCompleteThrough crossing (time + 18) := by
  obtain ⟨run⟩ := lesson_probe_run_exists box prepared time
  have initial := lessonProbe_initial prepared time
  have physical := lessonProbe_physical (prepared := prepared) (time := time) box
  exact ⟨run, run.execution.toCrossing initial box physical run.contacts_transversal, rfl,
    run.complete_execution.toCrossing run.execution initial box physical run.contacts_transversal⟩

/-- The same failure signal is forced in every complete crossing execution
    of this calendar, with the candidate's exact paths and jumps retained. -/
theorem LessonProbeRun.every_crossing_complete {θ ε prepared time final}
    (run : LessonProbeRun θ prepared time) (box : @PhysicalBox 1 θ ε)
    (crossing : CrossingExecution θ (fun _ _ => []) (lessonProbeStart prepared time) final)
    (complete : CrossingCompleteThrough crossing (time + 18)) :
    (∃ fire, time + 17 ≤ fire ∧ (0, fire) ∈ crossing.execution.ledger.emissions) ↔
      prepared = false := by
  have physical := lessonProbe_physical (prepared := prepared) (time := time) box
  have routing : StrictCausalRouter (fun (_ : Fin 1) _ => []) :=
    fun _ _ _ member => False.elim (List.not_mem_nil member)
  obtain ⟨native, same⟩ := crossing.execution.toNative_of_transverse_completion run.execution
    routing box physical run.complete_execution run.contacts_transversal (le_of_eq complete.1)
  have weakComplete := complete.toWeak_of_native crossing native same
    (lessonProbe_initial prepared time) box physical
  have fires := (run.execution.observational_unique_weak box crossing.execution physical
    run.complete_execution run.contacts_transversal weakComplete).2
  simp only [← fires.mem_iff]
  exact run.reports_failure

end RecursiveLearning.Native
