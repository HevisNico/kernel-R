import NativeLesson
import Dispatch
import TeacherReopen

/-! A lesson counter produces an actual acceptance FIRE. That FIRE can
write one credit on a separate R cell. The probe is a supplied test pulse,
separate from the counted lesson inputs. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid

def thresholdPorts (third : Bool) : List Port := if third then [0, 0, 0] else [0, 0]

noncomputable def acceptanceProbe (time : ℝ) : Delivery 1 := ⟨0, 0, time + 25⟩

noncomputable def acceptanceCounter (time : ℝ) (third : Bool) : Snapshot 1 :=
  { preparedTeacher time with
    x := fun i c => match c with
      | .z _ => -(6 / 5 : ℝ)
      | other => (preparedTeacher time).x i other
    pending := lessonDeliveries time (thresholdPorts third) }

noncomputable def acceptanceStart (time : ℝ) (third : Bool) : Snapshot 1 :=
  withFuture (acceptanceCounter time third) [acceptanceProbe time]

theorem acceptance_counter_physical {θ ε} (box : @PhysicalBox 1 θ ε) (time : ℝ) (third : Bool) :
    PhysicalInvariant θ (acceptanceCounter time third) := by
  let prepared := preparedTeacher_physical box time []
  refine ⟨prepared.region, ?_, prepared.recovery_cap, prepared.reserve⟩
  intro i p
  have cap := prepared.gain_cap i p
  change (0 : ℝ) ≤ Real.log ((θ i).cap p) at cap
  change -(6 / 5 : ℝ) ≤ Real.log ((θ i).cap p)
  linarith

structure AcceptanceSignal (θ : Fin 1 → Parameters) (time : ℝ) (third : Bool) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) (acceptanceStart time third) final
  complete : CompleteThrough execution (time + 48)
  transverse : execution.ContactsTransversal
  empty : final.pending = []
  ready : ∀ i, ReadyCoordinates final i
  rawNone : ∀ i p, final.raw i p = none
  fire : Option ℝ
  reports : fire.isSome = third
  window : ∀ F, fire = some F → time + 25 < F ∧ F < time + 26
  emissions : execution.ledger.emissions = fire.toList.map (fun F => (0, F))

private theorem lesson_prefix_append {n θ route s v u}
    (e : @Execution n θ route s v) (tail : Execution θ route v u) :
    (e.append tail).IsPrefix e := by
  induction e with
  | nil => exact .nil _
  | cons move rest ih => exact .step move _ rest (ih tail)

/-- A silent sequence of dose deliveries, with its exact physical gain balance. -/
structure CalendarDoseRun (θ : Fin 1 → Parameters) (start : Snapshot 1)
    (calendar : List (Delivery 1)) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) start final
  transverse : execution.ContactsTransversal
  silent : execution.ledger.emissions = []
  deliveries : execution.deliveries = calendar
  gains : ∀ p, final.x 0 (.z p) =
    start.x 0 (.z p) + (3 / 5 : ℝ) * (calendar.map Delivery.port).count p
  recovery : final.x 0 .b = start.x 0 .b
  ready : ReadyCoordinates final 0
  rawNone : ∀ p, final.raw 0 p = none
  empty : final.pending = []

structure CalendarDoseReadout (θ : Fin 1 → Parameters) (start : Snapshot 1) (calendar : List (Delivery 1))
    (probe : Delivery 1) (T : ℝ) (third : Bool) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) (withFuture start [probe]) final
  complete : CompleteThrough execution T
  transverse : execution.ContactsTransversal
  empty : final.pending = []
  ready : ∀ i, ReadyCoordinates final i
  rawNone : ∀ i p, final.raw i p = none
  fire : Option ℝ
  reports : fire.isSome = third
  window : ∀ F, fire = some F → probe.due < F ∧ F < probe.due + 1
  emissions : execution.ledger.emissions = fire.toList.map (fun F => (0, F))
  deliveries : execution.deliveries = calendar ++ [probe]
  observed : Snapshot 1
  observation : Execution θ (fun _ _ => []) (withFuture start [probe]) observed
  observationPrefix : execution.IsPrefix observation
  observedRaw : observed.raw 0 probe.port = some observed.time
  measured : ∀ p, observed.x 0 (.z p) = start.x 0 (.z p) + (3 / 5 : ℝ) * (calendar.map Delivery.port).count p

/-- Add the common read pulse to an existing lesson. Nonpositive log-gain produces
no spike. A gain of 0.6 produces a transverse FIRE before raw expiry. -/
theorem calendar_dose_readout_exists {θ ε start calendar probe T third} (box : @PhysicalBox 1 θ ε)
    (lesson : CalendarDoseRun θ start calendar) (phys : PhysicalInvariant θ start)
    (before : lesson.final.time < probe.due) (horizon : probe.due + 23 ≤ T)
    (recovery : start.x 0 .b = 2 / 25)
    (readGain : let gain := start.x 0 (.z probe.port) +
        (3 / 5 : ℝ) * (calendar.map Delivery.port).count probe.port
      if third then gain = 3 / 5 else gain ≤ 0) :
    Nonempty (CalendarDoseReadout θ start calendar probe T third) := by
  let framed := lesson.execution.withFuture [probe] (by
    intro d hd; obtain rfl := List.mem_singleton.mp hd; exact before.le)
  have framedTransverse : framed.ContactsTransversal :=
    teacher_future_transverse lesson.execution probe before.le lesson.transverse
  have framedSilent : framed.ledger.emissions = [] := by
    rw [Execution.withFuture_ledger, lesson.silent]
  let waiting := withFuture lesson.final [probe]
  have tailPhysical := lesson.execution.physical_invariant box phys
  have waitingPhysical : PhysicalInvariant θ waiting :=
    ⟨tailPhysical.region, tailPhysical.gain_cap, tailPhysical.recovery_cap, tailPhysical.reserve⟩
  have waitingReady (i : Fin 1) : ReadyCoordinates waiting i := by
    rw [Subsingleton.elim i 0]
    exact ⟨lesson.ready.ready, lesson.ready.charge, lesson.ready.auxiliary⟩
  have rawNone (i : Fin 1) (p : Port) : waiting.raw i p = none := by
    rw [Subsingleton.elim i 0]; exact lesson.rawNone p
  have queue : waiting.pending = [probe] := by simp [waiting, withFuture, lesson.empty]
  obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := fun _ _ => []) box waiting probe []
    waitingPhysical (by intro i p o raw; rw [rawNone] at raw; contradiction)
    waitingReady rawNone before queue (by simp)
  let lead := framed.append arrival.execution
  have prefixTransverse : lead.ContactsTransversal :=
    (Execution.contactsTransversal_append _ _).2 ⟨framedTransverse, arrival.contacts_transversal⟩
  have prefixSilent : lead.ledger.emissions = [] := by
    rw [Execution.emissions_append, framedSilent, arrival.emissions]
    rfl
  have admitted : arrival.final.time = probe.due := arrival.date
  have measured (p : Port) : arrival.final.x 0 (.z p) =
      start.x 0 (.z p) + (3 / 5 : ℝ) * (calendar.map Delivery.port).count p := by
    rw [arrival.gain_preserved]
    exact lesson.gains p
  have gain : if third then arrival.final.x 0 (.z probe.port) = 3 / 5
      else arrival.final.x 0 (.z probe.port) ≤ 0 := by
    rw [measured]
    exact readGain
  have leadDeliveries : lead.deliveries = calendar ++ [probe] := by
    rw [Execution.deliveries_append, teacher_future_deliveries, lesson.deliveries, arrival.deliveries]
  have future : ∀ d ∈ arrival.final.pending, arrival.final.time + 8 ≤ d.due := by simp [arrival.pending]
  have active : arrival.final.raw 0 probe.port = some arrival.final.time := by
    simpa only [Subsingleton.elim probe.cell 0] using arrival.raw_active
  have other (i : Fin 1) (p : Port) (h : i ≠ 0 ∨ p ≠ probe.port) : arrival.final.raw i p = none :=
    arrival.raw_other i p (by simpa only [Subsingleton.elim probe.cell 0] using h)
  cases third with
  | false =>
    have nonpositive : arrival.final.x 0 (.z probe.port) ≤ 0 := gain
    obtain ⟨cycle⟩ := weak_input_cycle_exists (route := fun _ _ => []) arrival.final box
      arrival.physical arrival.raw_valid 0 probe.port arrival.ready
      (by
        have h := Real.exp_le_exp.mpr nonpositive
        rw [Real.exp_zero] at h
        linarith)
      (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 6 / 5 by norm_num)])
      active other future
    have later : cycle.final.time < T := by rw [cycle.complete.1, admitted]; linarith [horizon]
    obtain ⟨tail, complete, positive, silent, noDeliveries⟩ := quiet_ready_tail_exists (θ := θ) later
      (fun i => by rw [Subsingleton.elim i 0]; exact cycle.pulse.coordinates)
      (fun i p => by rw [Subsingleton.elim i 0]; exact cycle.pulse.raw_finished p)
      (cycle.pending.trans arrival.pending)
    refine ⟨⟨_, (lead.append cycle.execution).append tail, complete, ?_,
      cycle.pending.trans arrival.pending, ?_,
      (fun i p => by rw [Subsingleton.elim i 0]; exact cycle.pulse.raw_finished p),
      none, rfl, by simp, ?_, ?_, arrival.final, lead, ?_, active, measured⟩⟩
    · change ((lead.append cycle.execution).append tail).ContactsTransversal
      exact (Execution.contactsTransversal_append _ _).2
        ⟨(Execution.contactsTransversal_append _ _).2 ⟨prefixTransverse, cycle.contacts_transversal⟩, positive⟩
    · intro i
      rw [Subsingleton.elim i 0]
      exact quietAt_ready_coordinates cycle.final 0 cycle.pulse.coordinates later.le
    · change ((lead.append cycle.execution).append tail).ledger.emissions = []
      rw [Execution.emissions_append, Execution.emissions_append, prefixSilent, cycle.emissions, silent]
      rfl
    · change ((lead.append cycle.execution).append tail).deliveries = _
      rw [Execution.deliveries_append, Execution.deliveries_append, leadDeliveries,
        cycle.deliveries, noDeliveries]
      simp
    · change ((lead.append cycle.execution).append tail).IsPrefix lead
      rw [Execution.append_assoc]
      exact lesson_prefix_append lead _
  | true =>
    have strong : 9 / 5 ≤ Real.exp (arrival.final.x 0 (.z probe.port)) ∧
        Real.exp (arrival.final.x 0 (.z probe.port)) ≤ 11 / 5 := by
      rw [show arrival.final.x 0 (.z probe.port) = 3 / 5 from gain]
      exact learnedProbe_gain
    have late : ∀ d ∈ arrival.final.pending, arrival.final.time + 31 / 4 ≤ d.due := by simp [arrival.pending]
    obtain ⟨fire⟩ := first_mid_learned_fire_exists arrival.final box arrival.physical arrival.raw_valid
      0 probe.port arrival.ready strong active other late
    obtain ⟨fast⟩ := fire.mid_learned_fast_end_exists box (arrival.ready 0) strong.2
      (fun p different => other 0 p (Or.inr different)) late
    have b : fast.final.x 0 .b = 2 / 25 := by
      rw [fast.recovery, fire.recovery_preserved, arrival.recovery_preserved]
      change lesson.final.x 0 .b = _
      exact lesson.recovery.trans recovery
    have state : LearnerDispatchState fast.final :=
      ⟨fast.raw_none, fun p => ⟨fast.auxiliary 0 p, fast.rest p⟩,
        Or.inr ⟨fast.main_slow, by rw [fast.charge]; norm_num, fast.charge.le, b⟩⟩
    have noQueue : fast.final.pending = [] := by
      rw [fast.pending, fire.pending, arrival.pending]
      rfl
    have date : fire.final.time = probe.due + fire.latency := by rw [fire.date, admitted]
    have wait : fast.final.time + 19 < T := by rw [fast.date, date]; linarith [fire.deadline, horizon]
    obtain ⟨tail⟩ := learner_wait_exists (θ := θ) state noQueue wait
    refine ⟨⟨_, ((lead.append fire.execution).append fast.execution).append tail.execution,
      tail.complete, ?_, tail.empty, tail.ready, tail.rawNone, some fire.final.time, rfl, ?_, ?_, ?_,
      arrival.final, lead, ?_, active, measured⟩⟩
    · change (((lead.append fire.execution).append fast.execution).append tail.execution).ContactsTransversal
      exact (Execution.contactsTransversal_append _ _).2
        ⟨(Execution.contactsTransversal_append _ _).2
          ⟨(Execution.contactsTransversal_append _ _).2 ⟨prefixTransverse, fire.contacts_transversal⟩,
            fast.contacts_transversal⟩, tail.transverse⟩
    · intro F equal
      have e : fire.final.time = F := Option.some.inj equal
      rw [← e, date]
      constructor <;> linarith [fire.early, fire.deadline]
    · change (((lead.append fire.execution).append fast.execution).append tail.execution).ledger.emissions =
        [(0, fire.final.time)]
      rw [Execution.emissions_append, Execution.emissions_append, Execution.emissions_append,
        prefixSilent, fire.emissions, fast.emissions, tail.silent, fire.date]
      rfl
    · change (((lead.append fire.execution).append fast.execution).append tail.execution).deliveries = _
      rw [Execution.deliveries_append, Execution.deliveries_append, Execution.deliveries_append,
        leadDeliveries, fire.deliveries, fast.deliveries, tail.deliveries]
      simp
    · change (((lead.append fire.execution).append fast.execution).append tail.execution).IsPrefix lead
      rw [Execution.append_assoc, Execution.append_assoc]
      exact lesson_prefix_append lead _

/-- A native readout of the actual endpoint of a completed dose lesson.
The admitted read pulse sees the same gains written by the lesson. -/
structure DoseReadout (θ : Fin 1 → Parameters) (start : Snapshot 1) (ports : List Port)
    (probe : Delivery 1) (T : ℝ) (third : Bool) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) (withFuture start [probe]) final
  complete : CompleteThrough execution T
  transverse : execution.ContactsTransversal
  empty : final.pending = []
  ready : ∀ i, ReadyCoordinates final i
  rawNone : ∀ i p, final.raw i p = none
  fire : Option ℝ
  reports : fire.isSome = third
  window : ∀ F, fire = some F → probe.due < F ∧ F < probe.due + 1
  emissions : execution.ledger.emissions = fire.toList.map (fun F => (0, F))
  deliveries : execution.deliveries = lessonDeliveries start.time ports ++ [probe]
  observed : Snapshot 1
  observation : Execution θ (fun _ _ => []) (withFuture start [probe]) observed
  observationPrefix : execution.IsPrefix observation
  observedRaw : observed.raw 0 probe.port = some observed.time
  measured : ∀ p, observed.x 0 (.z p) = start.x 0 (.z p) + (3 / 5 : ℝ) * ports.count p

private theorem lesson_deliveries_ports (time : ℝ) (ports : List Port) :
    (lessonDeliveries time ports).map Delivery.port = ports := by
  induction ports generalizing time with
  | nil => rfl
  | cons p ps ih => simp [lessonDeliveries, ih]

theorem dose_readout_exists_of_gain {θ ε start ports probe T third} (box : @PhysicalBox 1 θ ε)
    (lesson : LessonDoseRun θ start ports) (phys : PhysicalInvariant θ start)
    (before : lesson.final.time < probe.due) (horizon : probe.due + 23 ≤ T)
    (recovery : start.x 0 .b = 2 / 25)
    (readGain : let gain := start.x 0 (.z probe.port) + (3 / 5 : ℝ) * ports.count probe.port
      if third then gain = 3 / 5 else gain ≤ 0) :
    Nonempty (DoseReadout θ start ports probe T third) := by
  let run : CalendarDoseRun θ start (lessonDeliveries start.time ports) :=
    ⟨lesson.final, lesson.execution, lesson.transverse, lesson.silent, lesson.deliveries,
      fun p => by rw [lesson_deliveries_ports]; exact lesson.gains p,
      lesson.recovery, lesson.ready, lesson.rawNone, lesson.empty⟩
  have gain : let value := start.x 0 (.z probe.port) +
      (3 / 5 : ℝ) * ((lessonDeliveries start.time ports).map Delivery.port).count probe.port
      if third then value = 3 / 5 else value ≤ 0 := by
    dsimp only
    rw [lesson_deliveries_ports]
    exact readGain
  obtain ⟨read⟩ := calendar_dose_readout_exists box run phys before horizon recovery gain
  exact ⟨⟨read.final, read.execution, read.complete, read.transverse, read.empty, read.ready,
    read.rawNone, read.fire, read.reports, read.window, read.emissions, read.deliveries,
    read.observed, read.observation, read.observationPrefix, read.observedRaw,
    fun p => by simpa only [lesson_deliveries_ports] using read.measured p⟩⟩

theorem dose_readout_exists {θ ε start ports probe T third} (box : @PhysicalBox 1 θ ε)
    (lesson : LessonDoseRun θ start ports) (phys : PhysicalInvariant θ start)
    (before : lesson.final.time < probe.due) (horizon : probe.due + 23 ≤ T)
    (recovery : start.x 0 .b = 2 / 25)
    (readGain : start.x 0 (.z probe.port) + (3 / 5 : ℝ) * ports.count probe.port =
      if third then 3 / 5 else 0) :
    Nonempty (DoseReadout θ start ports probe T third) := by
  apply dose_readout_exists_of_gain box lesson phys before horizon recovery
  dsimp only
  rw [readGain]
  cases third <;> simp

theorem acceptance_signal_exists {θ ε} (box : @PhysicalBox 1 θ ε) (time : ℝ) (third : Bool) :
    Nonempty (AcceptanceSignal θ time third) := by
  let s := acceptanceCounter time third
  let token := acceptanceProbe time
  have phys := acceptance_counter_physical box time third
  have ready : ReadyCoordinates s 0 :=
    ⟨rfl, by norm_num [s, acceptanceCounter, preparedTeacher],
      fun _ => ⟨rfl, by norm_num [s, acceptanceCounter, preparedTeacher, RestBand]⟩⟩
  obtain ⟨lesson⟩ := lesson_dose_run_exists (start := s) (ports := thresholdPorts third)
    box phys (by simp [RawValid, s, acceptanceCounter, preparedTeacher]) ready (fun _ => rfl) rfl
    (by intro p; fin_cases p <;> cases third <;>
      norm_num [s, acceptanceCounter, thresholdPorts, List.count_cons])
  have lessonBefore : lesson.final.time < token.due := by
    rw [lesson.complete.1]
    change time + 8 * (thresholdPorts third).length < time + 25
    cases third <;> simp [thresholdPorts] <;> linarith
  have gain : s.x 0 (.z token.port) + (3 / 5 : ℝ) * (thresholdPorts third).count token.port =
      if third then 3 / 5 else 0 := by
    cases third <;> norm_num [s, token, acceptanceProbe, acceptanceCounter, thresholdPorts]
  obtain ⟨read⟩ := dose_readout_exists (T := time + 48) box lesson phys lessonBefore
    (by change time + 25 + 23 ≤ time + 48; linarith) rfl gain
  exact ⟨⟨read.final, read.execution, read.complete, read.transverse, read.empty,
    read.ready, read.rawNone, read.fire, read.reports,
    fun F h => by
      obtain ⟨early, late⟩ := read.window F h
      change time + 25 < F at early
      change F < time + 25 + 1 at late
      exact ⟨early, by linarith⟩,
    read.emissions⟩⟩

noncomputable def acceptanceContacts (credit : Port) : HeadRoutes 1 :=
  fun _ F => [⟨0, credit, F + 7 / 20⟩]

noncomputable def acceptanceNetworkStart (time : ℝ) (third : Bool) : Snapshot 2 :=
  let tester := acceptanceStart time third
  tester.prependQueued (preparedTeacher time) (tester.pending.map Delivery.succ)

structure CreditResponse (θ : Fin 1 → Parameters) (time T : ℝ) (credit : Port) (fire : Option ℝ) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => [])
    ((preparedTeacher time).requeue (fire.toList.map (fun F => ⟨0, credit, F + 7 / 20⟩))) final
  complete : CompleteThrough execution T
  positive : execution.ContactsTransversal
  written : ∀ p, final.x 0 (.z p) = if p = credit ∧ fire.isSome then 3 / 5 else 0

theorem credit_response_exists {θ ε time T credit fire} (box : @PhysicalBox 1 θ ε)
    (later : time < T) (window : ∀ F, fire = some F → time < F ∧ F + 8 ≤ T) :
    Nonempty (CreditResponse θ time T credit fire) := by
  let start := (preparedTeacher time).requeue (fire.toList.map (fun F => ⟨0, credit, F + 7 / 20⟩))
  have ready (i : Fin 1) : ReadyCoordinates start i :=
    ⟨rfl, by norm_num [start, Snapshot.requeue, preparedTeacher],
      fun _ => ⟨rfl, by norm_num [start, Snapshot.requeue, preparedTeacher, RestBand]⟩⟩
  have raw (i : Fin 1) (p : Port) : start.raw i p = none := rfl
  cases fire with
  | none =>
    obtain ⟨wait, complete, positive, _, _⟩ := quiet_ready_tail_exists (θ := θ)
      (T := T) later ready raw rfl
    exact ⟨⟨_, wait, complete, positive, fun p => by simp [quietAt, quietValues, start,
      Snapshot.requeue, preparedTeacher]⟩⟩
  | some F =>
    let due := F + 7 / 20
    have later := window F rfl
    obtain ⟨dose⟩ := port_dose_exists (route := fun _ _ => []) (start := start)
      (port := credit) (due := due) (later := []) box (preparedTeacher_physical box time _)
      (by intro i p o h; rw [raw] at h; contradiction)
      (ready 0) (raw 0) (by change time < F + 7 / 20; linarith [later.1]) rfl
      (by simp) (by change Real.exp 0 ≤ _; norm_num)
      (by change 0 ≤ _; linarith [Real.log_nonneg (show (1 : ℝ) ≤ 6 / 5 by norm_num)])
    have before : dose.final.time < T := by
      rw [dose.complete.1]
      dsimp [due]
      linarith [later.2]
    obtain ⟨wait, complete, positive, _, _⟩ := quiet_ready_tail_exists (θ := θ) before
      (fun i => by rw [Subsingleton.elim i 0]; exact dose.ready)
      (fun i p => by rw [Subsingleton.elim i 0]; exact dose.rawNone p) dose.pending
    refine ⟨⟨_, dose.execution.append wait, complete,
      (Execution.contactsTransversal_append _ _).2 ⟨dose.transversal, positive⟩, ?_⟩⟩
    intro p
    change dose.final.x 0 (.z p) = _
    rw [dose.gain]
    simp [start, Snapshot.requeue, preparedTeacher]

/-- The counter and the credit cell are woven into a single native history.
The credit pulse is absent from the initial queue and comes from an actual
counter FIRE. Two lesson pulses write nothing, while three write one dose. -/
theorem native_acceptance_writes_credit {θT θC ε} (testBox : @PhysicalBox 1 θT ε)
    (creditBox : @PhysicalBox 1 θC ε) (time : ℝ) (credit : Port) (third : Bool) :
    let θ := prependParameters θC θT
    let route := prependRouted (fun _ _ => []) (acceptanceContacts credit)
    let start := acceptanceNetworkStart time third
    ∃ (final : Snapshot 2) (e : Execution θ route start final)
      (crossing : CrossingExecution θ route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing (time + 48) ∧
      (e.emissionTimes 1).length = (if third then 1 else 0) ∧
      ∀ p, final.x 0 (.z p) = if p = credit ∧ third then 3 / 5 else 0 := by
  obtain ⟨test⟩ := acceptance_signal_exists testBox time third
  obtain ⟨response⟩ := credit_response_exists creditBox (credit := credit) (T := time + 48) (by linarith)
    (fun F h => by obtain ⟨early, late⟩ := test.window F h; constructor <;> linarith)
  let tester := acceptanceStart time third
  let receiver := (preparedTeacher time).requeue (test.fire.toList.map (fun F => ⟨0, credit, F + 7 / 20⟩))
  have queue : receiver.pending = test.execution.headInputQueue (acceptanceContacts credit) := by
    simp only [Execution.headInputQueue, test.emissions, List.flatMap_map]
    cases h : test.fire <;> simp [receiver, Snapshot.requeue, h, acceptanceContacts]
  have balance := HeadQueueBalance.initial test.execution receiver (acceptanceContacts credit) queue
  have causal : StrictHeadRoutes (acceptanceContacts credit) := by
    intro i F d hd
    obtain rfl := List.mem_singleton.mp hd
    change F < F + 7 / 20
    linarith
  obtain ⟨weave⟩ := test.execution.prepend_causal_result response.execution rfl
    (test.complete.1.trans response.complete.1.symm) (acceptanceContacts credit) causal
    (tester.pending.map Delivery.succ) balance
  have box : PhysicalBox (prependParameters θC θT) ε := by
    refine ⟨testBox.1, ?_⟩
    intro i p
    cases i using Fin.cases with
    | zero => exact creditBox.2 0 p
    | succ i => exact testBox.2 i p
  have physical : PhysicalInvariant (prependParameters θC θT) (acceptanceNetworkStart time third) := by
    have testPhys := acceptance_counter_physical testBox time third
    have creditPhys := preparedTeacher_physical creditBox time []
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i
      · exact creditPhys.region 0
      · exact testPhys.region 0
    · intro i p; fin_cases i
      · exact creditPhys.gain_cap 0 p
      · exact testPhys.gain_cap 0 p
    · intro i; fin_cases i
      · exact creditPhys.recovery_cap 0
      · exact testPhys.recovery_cap 0
    · intro i; fin_cases i
      · exact creditPhys.reserve 0
      · exact testPhys.reserve 0
  have initial : InitiallyBelowReady (acceptanceNetworkStart time third) := by
    intro i c h
    cases c with
    | q =>
      cases i using Fin.cases <;> change (1 / 10 : ℝ) < 1 <;> norm_num
    | m p =>
      cases i using Fin.cases <;> change (1 / 40 : ℝ) < 1 <;> norm_num
    | z _ => exact False.elim h
    | b => exact False.elim h
    | energy => exact False.elim h
  have done := weave.complete test.complete response.complete
  have positive := weave.contacts_transversal test.transverse response.positive
  refine ⟨_, weave.execution, weave.execution.toCrossing initial box physical positive, rfl,
    done.toCrossing weave.execution initial box physical positive, ?_, ?_⟩
  · change (weave.execution.emissionTimes ((0 : Fin 1).succ)).length = _
    rw [weave.tail_emission_times, Execution.emissionTimes, test.emissions]
    cases h : test.fire with
    | none =>
      have eq : third = false := by simpa [h] using test.reports.symm
      simp [eq]
    | some F =>
      have eq : third = true := by simpa [h] using test.reports.symm
      simp [eq]
  · intro p
    change response.final.x 0 (.z p) = _
    rw [response.written, test.reports]

end RecursiveLearning.Native
