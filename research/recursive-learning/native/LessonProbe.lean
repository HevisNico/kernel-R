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

theorem lessonProbe_physical {θ ε prepared time} (box : @PhysicalBox 1 θ ε) :
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

theorem lessonProbe_initial (prepared : Bool) (time : ℝ) :
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
  recovery : final.x 0 .b = if prepared then 9 / 50 else 2 / 25

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
    recovery := (probe.recovery_preserved 0).trans dose.recovery
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
    recovery := ?_
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
  · rw [probe.recovery_preserved, cycle.recovery_gain]
    change slow.final.x 0 .b + 1 / 10 = 9 / 50
    rw [slow.recovery, fast.recovery, fire.recovery_preserved, arrival.recovery_preserved]
    norm_num [start, lessonProbeStart]

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

theorem learnedProbe_gain :
    9 / 5 ≤ Real.exp (3 / 5 : ℝ) ∧ Real.exp (3 / 5 : ℝ) ≤ 11 / 5 := by
  constructor
  · have bound := Real.sum_le_exp_of_nonneg (x := (3 / 5 : ℝ)) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at bound
    linarith
  · have bound := Real.exp_le_exp.mpr (show (3 / 5 : ℝ) ≤ Real.log 2 by
      linarith [Real.log_two_gt_d9])
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at bound
    linarith

structure LessonProbeRun (θ : Fin 1 → Parameters) (prepared : Bool) (time : ℝ)
    (finish : ℝ := time + 18) where
  admission : LessonProbeAdmission θ prepared time
  final : Snapshot 1
  readout : Execution θ (fun _ _ => []) admission.final final
  complete : CompleteThrough readout finish
  transversal : readout.ContactsTransversal
  emissions : if prepared then readout.ledger.emissions = []
    else ∃ fire, readout.ledger.emissions = [(0, fire)]
  earlyReadout : ∀ e ∈ readout.ledger.emissions, e.2 < time + 18
  pendingEmpty : final.pending = []

noncomputable def LessonProbeRun.execution {θ prepared time finish}
    (run : LessonProbeRun θ prepared time finish) :
    Execution θ (fun _ _ => []) (lessonProbeStart prepared time) run.final :=
  run.admission.execution.append run.readout

theorem LessonProbeRun.complete_execution {θ prepared time finish} (run : LessonProbeRun θ prepared time finish) :
    CompleteThrough run.execution finish := run.complete

theorem LessonProbeRun.contacts_transversal {θ prepared time finish} (run : LessonProbeRun θ prepared time finish) :
    run.execution.ContactsTransversal :=
  (run.admission.execution.contactsTransversal_append run.readout).2
    ⟨run.admission.transversal, run.transversal⟩

theorem LessonProbeRun.fires {θ prepared time finish} (run : LessonProbeRun θ prepared time finish) :
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
theorem LessonProbeRun.reports_failure {θ prepared time finish} (run : LessonProbeRun θ prepared time finish) :
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

/-- A quiet extension starts from the carried charge and energy and
    preserves the current physical memories. -/
theorem quiet_ready_tail_exists {θ : Fin 1 → Parameters} {s : Snapshot 1} {T : ℝ}
    (later : s.time < T) (ready : ∀ i, ReadyCoordinates s i)
    (rawNone : ∀ i p, s.raw i p = none) (empty : s.pending = []) :
    ∃ e : Execution θ (fun _ _ => []) s (quietAt s T),
      CompleteThrough e T ∧ e.ContactsTransversal ∧ e.ledger.emissions = [] ∧ e.deliveries = [] := by
  have charge (i : Fin 1) : s.x i .q < 1 := by linarith [(ready i).charge.2]
  have sensor (i : Fin 1) (p : Port) : s.x i (.m p) < 1 := by
    linarith [((ready i).auxiliary p).2.2]
  have noDue : ∀ d ∈ s.pending, T < d.due := by simp [empty]
  let flow : Flow θ s (quietAt s T) :=
    quietFlow s later (fun i => (ready i).ready) (fun i p => ((ready i).auxiliary p).1)
      rawNone charge sensor (fun d hd => (noDue d hd).le)
  obtain ⟨_, complete⟩ := quiet_complete_exists (θ := θ) (route := fun _ _ => []) s later
    (fun i => (ready i).ready) (fun i p => ((ready i).auxiliary p).1) rawNone charge sensor noDue
  exact ⟨.cons (.flow flow) (.nil _), complete, by simp, rfl, rfl⟩

structure LearnerDispatchState (s : Snapshot 1) : Prop where
  rawNone : ∀ i p, s.raw i p = none
  auxiliary : ∀ p, s.aux 0 p = .ready ∧ RestBand (s.x 0 (.m p))
  main : ReadyCoordinates s 0 ∨
    (s.main 0 = .slow ∧ 1 / 10 < s.x 0 .q ∧ s.x 0 .q ≤ 1 / 4 ∧ s.x 0 .b = 2 / 25)

private theorem slow_readout_tail_exists {θ : Fin 1 → Parameters} {s : Snapshot 1} {T : ℝ}
    (later : s.time < T) (short : T + 1 / 10 - s.time ≤ 8)
    (slow : s.main 0 = .slow) (charge : s.x 0 .q = 1 / 4) (recovery : s.x 0 .b = 2 / 25)
    (aux : ∀ i p, s.aux i p = .ready) (rest : ∀ p, RestBand (s.x 0 (.m p)))
    (rawNone : ∀ i p, s.raw i p = none) (empty : s.pending = []) :
    ∃ (final : Snapshot 1) (e : Execution θ (fun _ _ => []) s final),
      CompleteThrough e T ∧ e.ContactsTransversal ∧ e.ledger.emissions = [] ∧
        LearnerDispatchState final := by
  let finish := T + 1 / 10
  have positive : s.time < finish := by dsimp [finish]; linarith
  have mainGuard (t : ℝ) (ht : t ∈ Set.Ico s.time finish) :
      1 / 10 < s.x 0 .q * Real.exp (-s.x 0 .b * (t - s.time)) := by
    rw [charge, recovery]
    have attenuation : (1 / 2 : ℝ) ≤ Real.exp (-(2 / 25 : ℝ) * (t - s.time)) := by
      have bound : Real.exp (-Real.log 2) ≤ Real.exp (-(2 / 25 : ℝ) * (t - s.time)) :=
        Real.exp_le_exp.mpr (by
          have elapsed : t - s.time ≤ 8 := by dsimp [finish] at ht; linarith [ht.2]
          linarith [Real.log_two_gt_d9])
      simpa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using bound
    linarith
  have otherSensor (i : Fin 1) (p : Port) : s.x i (.m p) < 1 := by
    rw [Subsingleton.elim i 0]
    linarith [(rest p).2]
  let flow : Flow θ s (protectedMainEnd θ s 0 0 .slow .ready none finish) :=
    protectedMainFlow s 0 0 .slow .ready none positive (Or.inr rfl) (Or.inl rfl)
      slow (fun i hi => False.elim (hi (Subsingleton.elim i 0))) (aux 0 0) (fun i p _ => aux i p)
      (rawNone 0 0) (fun i p _ => rawNone i p) (by simp)
      (fun i hi => False.elim (hi (Subsingleton.elim i 0))) (fun i p _ => otherSensor i p)
      (by intro t ht; simpa [protectedMainRate] using mainGuard t ht)
      (by intro t ht
          simp only [ite_true, rawInputScale, mul_zero, auxPulse_zero_eq_relax]
          exact relax_lt (by norm_num) ht.1 (otherSensor 0 0) (by norm_num))
      (by simp [empty])
  have before : T < finish := by dsimp [finish]; linarith
  let final := flow.at T
  let next := flow.suffix later.le before
  let trace : Execution θ (fun _ _ => []) s final := .cons (.flow (flow.prefix later before.le)) (.nil _)
  have complete : CompleteThrough trace T :=
    ⟨rfl, fun _ => next.initial_before_guards.no_jump
      (fun i p origin active => next.initial_raw_strict i p origin active)
      next.initial_pending_strict _, next.initial_pending_strict⟩
  refine ⟨final, trace, complete, by simp [trace], rfl, ⟨rawNone, ?_, ?_⟩⟩
  · intro p
    refine ⟨aux 0 p, ?_⟩
    have band := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) later.le (rest p)
      (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Set.Icc
        (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
    change RestBand (protectedMainValues θ s 0 0 .slow .ready none T 0 (.m p))
    by_cases hp : p = 0
    · subst p
      simpa [protectedMainValues, rawInputScale, auxPulse_zero_eq_relax, RestBand] using band
    · simpa [protectedMainValues, hp, RestBand] using band
  · refine Or.inr ⟨slow, ?_, ?_, recovery⟩
    · exact mainGuard T ⟨later.le, before⟩
    · change s.x 0 .q * Real.exp (-s.x 0 .b * (T - s.time)) ≤ 1 / 4
      rw [charge, recovery]
      have decay : Real.exp (-(2 / 25 : ℝ) * (T - s.time)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      linarith

/-- The learner remains complete until after the routed teacher dose can
    finish. Its readout still reports only the original offset-17 probe. -/
theorem lesson_probe_dispatch_state_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (prepared : Bool) (time : ℝ) :
    ∃ run : LessonProbeRun θ prepared time (time + 26), LearnerDispatchState run.final := by
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
    have fastDate : fast.final.time = time + 17 + fire.latency + 1 := by rw [fast.date, fire.date, date]
    have fastRecovery : fast.final.x 0 .b = 2 / 25 := by
      rw [fast.recovery, fire.recovery_preserved]
      exact admission.recovery
    have fastEmpty : fast.final.pending = [] := by
      rw [fast.pending, fire.pending, admission.queue]
      rfl
    obtain ⟨final, slow, complete, slowTransverse, slowSilent, dispatch⟩ :=
      slow_readout_tail_exists (θ := θ) (T := time + 26)
        (by rw [fastDate]; linarith [fire.deadline]) (by rw [fastDate]; linarith [fire.early])
        fast.main_slow fast.charge fastRecovery fast.auxiliary fast.rest fast.raw_none fastEmpty
    let readout := (fire.execution.append fast.execution).append slow
    have emissions : readout.ledger.emissions = [(0, fire.final.time)] := by
      simp [readout, Execution.emissions_append, fire.emissions, fast.emissions, slowSilent, fire.date]
    refine ⟨⟨admission, final, readout, complete, ?_, ⟨_, emissions⟩, ?_,
      readout.pending_empty_of_sources_due _ complete (by simp [admission.queue]) (fun _ _ => rfl)⟩,
      dispatch⟩
    · simp [readout, fire.contacts_transversal, fast.contacts_transversal, slowTransverse]
    · intro e member
      rw [emissions] at member
      obtain rfl := List.mem_singleton.mp member
      rw [fire.date, date]
      linarith [fire.deadline]
  | true =>
    have gain : admission.final.x 0 (.z 0) = 0 := admission.logGain
    have logPos := Real.log_nonneg (show (1 : ℝ) ≤ 6 / 5 by norm_num)
    obtain ⟨response⟩ := weak_input_cycle_exists (route := fun _ _ => []) admission.final box
      physical admission.rawValid 0 0 admission.ready (by rw [gain]; norm_num)
      (by rw [gain]; linarith) admission.active admission.otherRaw (by simp [admission.queue])
    have empty := response.pending.trans admission.queue
    obtain ⟨wait, complete, transverse, silent, _⟩ := quiet_ready_tail_exists (θ := θ)
      (T := time + 26) (by rw [response.date, date]; linarith)
      (fun i => by simpa only [Subsingleton.elim i 0] using response.pulse.coordinates)
      (fun i p => by simpa only [Subsingleton.elim i 0] using response.pulse.raw_finished p) empty
    let readout := response.execution.append wait
    have emissions : readout.ledger.emissions = [] := by
      simp [readout, Execution.emissions_append, response.emissions, silent]
    have later : response.final.time ≤ time + 26 := by rw [response.date, date]; linarith
    have ready := quietAt_ready_coordinates response.final 0 response.pulse.coordinates later
    exact ⟨⟨admission, _, readout, complete,
      (Execution.contactsTransversal_append _ _).2 ⟨response.contacts_transversal, transverse⟩,
      emissions, by simp [emissions], empty⟩, ⟨
      fun i p => by
        change response.final.raw i p = none
        rw [Subsingleton.elim i 0]
        exact response.pulse.raw_finished p,
      ready.auxiliary, Or.inl ready⟩⟩

theorem lesson_probe_late_run_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (prepared : Bool) (time : ℝ) : Nonempty (LessonProbeRun θ prepared time (time + 26)) := by
  obtain ⟨run, _⟩ := lesson_probe_dispatch_state_exists box prepared time
  exact ⟨run⟩

/-- Recover the original probe horizon as a saturated prefix of the longer
    run. Every readout FIRE is strictly before that cut. -/
theorem lesson_probe_run_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (prepared : Bool) (time : ℝ) : Nonempty (LessonProbeRun θ prepared time) := by
  obtain ⟨run⟩ := lesson_probe_late_run_exists box prepared time
  obtain ⟨cut⟩ := run.readout.before_flow_cut_exists (time + 18)
    (by rw [run.admission.complete.1]; linarith)
    (by rw [run.complete.1]; linarith)
  have restSilent : cut.rest.ledger.emissions = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro event member
    have emitted : event ∈ run.readout.ledger.emissions := by
      rw [cut.emissions]
      exact List.mem_append_right _ member
    have after := (cut.rest.emission_time_bounds _ member).1
    have clock := cut.flow.positive
    rw [cut.date] at clock
    linarith [run.earlyReadout event emitted]
  have same : cut.cut.ledger.emissions = run.readout.ledger.emissions := by
    rw [cut.emissions, restSilent, List.append_nil]
  refine ⟨⟨run.admission, cut.state, cut.cut, cut.complete,
    cut.isPrefix.contacts_transversal run.transversal, ?_, ?_,
    cut.cut.pending_empty_of_sources_due _ cut.complete (by simp [run.admission.queue])
      (fun _ _ => rfl)⟩⟩
  · simpa only [same] using run.emissions
  · rw [same]
    exact run.earlyReadout

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
