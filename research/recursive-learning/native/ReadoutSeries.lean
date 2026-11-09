import LearnerReadout

/-! The serial experiment with actual learner readouts. Separate trials
exercise both lesson blocks. All interstage inputs are issued by native
FIRE jumps. The selector update wire is the only frozen intervention. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid

private structure LocalRun (θ : Fin 1 → Parameters) (start : Snapshot 1) (T : ℝ) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) start final
  complete : CompleteThrough execution T
  positive : execution.ContactsTransversal

private theorem LocalRun.dates_of_ledger {θ s T} (run : LocalRun θ s T) (fire : Option ℝ)
    (emissions : run.execution.ledger.emissions = fire.toList.map (fun F => (0, F))) :
    run.execution.emissionTimes 0 = fire.toList := by
  rw [Execution.emissionTimes, emissions]
  cases fire <;> rfl

private theorem quiet_prefix_at_rest {θ : Fin 1 → Parameters} {s : Snapshot 1} {t : ℝ} (later : t ≤ s.time)
    (main : ∀ i, s.main i = .ready) (aux : ∀ i p, s.aux i p = .ready)
    (raw : ∀ i p, s.raw i p = none) (q : ∀ i, s.x i .q = 1 / 10)
    (m : ∀ i p, s.x i (.m p) = 1 / 40) (reserve : ∀ i, s.x i .energy = 100)
    (future : ∀ d ∈ s.pending, s.time ≤ d.due) :
    ∃ e : Execution θ (fun _ _ => []) {s with time := t} s,
      e.ContactsTransversal ∧ e.ledger.emissions = [] ∧ e.deliveries = [] := by
  rcases later.lt_or_eq with positive | rfl
  · exact rest_prefix positive main aux raw q m reserve future
  · exact ⟨.nil _, trivial, rfl, rfl⟩

/-- The trial queue contains its actual ordered lesson plus a common
read pulse, which is placed first as a future token. -/
noncomputable def seriesTrial (clock : ℝ) (practice third : Bool) : Snapshot 1 :=
  withFuture (readoutLearner clock (trialLesson practice third) (trialPort practice))
    [learnerRead clock (trialPort practice)]

private theorem series_trial_future {clock practice third d}
    (h : d ∈ (seriesTrial clock practice third).pending) : clock < d.due := by
  change d ∈ learnerRead clock (trialPort practice) ::
    lessonDeliveries clock (lessonPorts (trialLesson practice third)) at h
  rcases List.mem_cons.mp h with rfl | member
  · change clock < clock + 65
    linarith
  · linarith [lesson_delivery_time member]

private theorem staged_trial_exists {θ ε time clock T} (box : @PhysicalBox 1 θ ε)
    (later : time ≤ clock) (horizon : clock + 96 < T) (practice third : Bool) :
    ∃ (run : LocalRun θ {seriesTrial clock practice third with time := time} T) (fire : Option ℝ),
      fire.isSome = third ∧
      (∀ F, fire = some F → clock + 65 < F ∧ F < clock + 66) ∧
      run.execution.emissionTimes 0 = fire.toList ∧
      run.execution.deliveries.length = (trialLesson practice third).cost + 1 := by
  let s := seriesTrial clock practice third
  have capacity : (trialLesson practice third).preparation ≤ 4 ∧
      (trialLesson practice third).practice ≤ 4 := by
    cases practice <;> cases third <;> decide
  have count : (lessonPorts (trialLesson practice third)).count (trialPort practice) =
      if third then 3 else 2 := by
    cases practice
    · exact (lessonPorts_count (preparationTrial third)).1
    · exact (lessonPorts_count (practiceTrial third)).2.1
  obtain ⟨read⟩ := full_learner_read_exists box clock (trialLesson practice third) (trialPort practice)
    third capacity count
  obtain ⟨wait, positive, silent, noDelivery⟩ := quiet_prefix_at_rest (θ := θ) (s := s)
    later (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun d h => (series_trial_future h).le)
  obtain ⟨rest, complete, restPositive, restSilent, restDelivery⟩ := quiet_ready_tail_exists (θ := θ)
    (T := T) (by rw [read.complete.1]; exact horizon) read.ready read.rawNone read.empty
  let measured : Execution θ (fun _ _ => []) s read.final := read.execution
  let e := (wait.append measured).append rest
  let run : LocalRun θ {s with time := time} T :=
    ⟨_, e, complete, (Execution.contactsTransversal_append _ _).2
      ⟨(Execution.contactsTransversal_append _ _).2 ⟨positive, read.transverse⟩, restPositive⟩⟩
  have measuredEmissions := read.emissions
  change measured.ledger.emissions = _ at measuredEmissions
  have measuredDeliveries := read.deliveries
  change measured.deliveries = _ at measuredDeliveries
  have events : run.execution.ledger.emissions = read.fire.toList.map (fun F => (0, F)) := by
    change e.ledger.emissions = _
    rw [Execution.emissions_append, Execution.emissions_append, silent, measuredEmissions, restSilent,
      List.nil_append, List.append_nil]
  refine ⟨run, read.fire, read.reports, ?_, run.dates_of_ledger _ events, ?_⟩
  · intro F h
    obtain ⟨early, late⟩ := read.window F h
    change clock + 65 < F at early
    change F < clock + 65 + 1 at late
    exact ⟨early, by linarith⟩
  · change e.deliveries.length = _
    rw [Execution.deliveries_append, Execution.deliveries_append, noDelivery, measuredDeliveries,
      restDelivery, List.nil_append, List.append_nil]
    cases practice <;> cases third <;> rfl

private theorem fired {fire : Option ℝ} (h : fire.isSome = true) : ∃ F, fire = some F := by
  cases fire with
  | none => simp at h
  | some F => exact ⟨F, rfl⟩

private theorem silent {fire : Option ℝ} (h : fire.isSome = false) : fire = none := by
  cases fire with
  | none => rfl
  | some F => simp at h

private noncomputable def atCell {n} (sender : Fin n) (send : ℝ → List (Delivery 1)) : HeadRoutes n :=
  fun i F => if i = sender then send F else []

private theorem atCell_strict {n} (sender : Fin n) {send : ℝ → List (Delivery 1)}
    (strict : ∀ F d, d ∈ send F → F < d.due) : StrictHeadRoutes (atCell sender send) := by
  intro i F d member
  by_cases matchCell : i = sender
  · exact strict F d (by simpa [atCell, matchCell] using member)
  · simp [atCell, matchCell] at member

private theorem atCell_inputs {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (send : ℝ → List (Delivery 1)) :
    e.headInputQueue (atCell i send) = (e.emissionTimes i).flatMap send := by
  unfold Execution.headInputQueue Execution.emissionTimes
  induction e.ledger.emissions with
  | nil => rfl
  | cons event events ih =>
    simp only [atCell] at ih
    by_cases h : event.1 = i <;> simp [atCell, h, ih]

private noncomputable def fixedCalendar (gate : ℝ) (tokens : List (Delivery 1))
    (F : ℝ) : List (Delivery 1) := if F < gate then tokens else []

private theorem fixedCalendar_strict {gate tokens} (future : ∀ d ∈ tokens, gate ≤ d.due) :
    ∀ F d, d ∈ fixedCalendar gate tokens F → F < d.due := by
  intro F d member
  by_cases early : F < gate
  · exact early.trans_le (future d (by simpa [fixedCalendar, early] using member))
  · simp [fixedCalendar, early] at member

/-- Initial head sources are separate from the proof-only future wires. -/
private theorem stage_balance {n θ route s u} (e : @Execution n θ route s u)
    (h : Snapshot 1) (external : List (Delivery 1)) (contacts : HeadRoutes n)
    (pending : (external ++ e.headInputQueue contacts).Perm h.pending) :
    HeadQueueBalance e h
      (external.map (Delivery.head (n := n)) ++ s.pending.map Delivery.succ) contacts := by
  unfold HeadQueueBalance
  rw [e.futureHeadWires_map]
  have same := Multiset.coe_eq_coe.mpr (pending.map (Delivery.head (n := n)))
  rw [List.map_append, ← Multiset.coe_add] at same
  rw [← same, ← Multiset.coe_add]
  change (external.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1))) +
    (s.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
    (List.map (Delivery.head (n := n)) (e.headInputQueue contacts) : Multiset (Delivery (n + 1))) =
      (s.pending.map Delivery.succ : Multiset (Delivery (n + 1))) +
        ((external.map (Delivery.head (n := n)) : Multiset (Delivery (n + 1))) +
          (List.map (Delivery.head (n := n)) (e.headInputQueue contacts) : Multiset (Delivery (n + 1))))
  exact (congrArg (fun z => z + _) (add_comm _ _)).trans (add_assoc _ _ _)

private noncomputable def inverterSource (time : ℝ) : Snapshot 1 :=
  { lessonProbeStart false (time + 140) with time := time }

private theorem staged_inverter_exists {θ ε time T} (box : @PhysicalBox 1 θ ε)
    (horizon : time + 185 < T) :
    ∃ (run : LocalRun θ (inverterSource time) T) (F : ℝ),
      time + 157 ≤ F ∧ F < time + 158 ∧
      ∀ send : ℝ → List (Delivery 1), (∀ date < time + 157, send date = []) →
        (run.execution.emissionTimes 0).flatMap send = send F := by
  let clock := time + 140
  let start := lessonProbeStart false clock
  have due : ∀ d ∈ start.pending, start.time ≤ d.due := by
    intro d h
    change d ∈ lessonProbeQueue false clock at h
    simp only [lessonProbeQueue, Bool.false_eq_true, ite_false, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · change clock ≤ clock + 9; linarith
    · change clock ≤ clock + 17; linarith
  obtain ⟨lead, leadPositive, leadSilent, _⟩ := rest_prefix (θ := θ) (s := start) (origin := time)
    (by change time < time + 140; linarith) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) due
  obtain ⟨probe, dispatch⟩ := lesson_probe_dispatch_state_exists box false clock
  obtain ⟨finish⟩ := learner_wait_exists (θ := θ) (T := T) dispatch probe.pendingEmpty
    (by rw [probe.complete.1]; dsimp [clock]; linarith)
  obtain ⟨F, fired⟩ := probe.emissions
  have member : (0, F) ∈ probe.readout.ledger.emissions := by simp [fired]
  have early := (probe.readout.emission_time_bounds _ member).1
  rw [probe.admission.complete.1] at early
  have late := probe.earlyReadout _ member
  let execution := (lead.append probe.execution).append finish.execution
  let run : LocalRun θ (inverterSource time) T :=
    ⟨_, execution, finish.complete, (Execution.contactsTransversal_append _ _).2
      ⟨(Execution.contactsTransversal_append _ _).2 ⟨leadPositive, probe.contacts_transversal⟩,
        finish.transverse⟩⟩
  refine ⟨run, F, by dsimp [clock] at early; linarith, by dsimp [clock] at late; linarith, ?_⟩
  intro send ignored
  have earlier (event : Fin 1 × ℝ) (member : event ∈ probe.admission.execution.ledger.emissions) :
      send event.2 = [] := by
    apply ignored
    have h := probe.admission.earlyEmissions event member
    dsimp [clock] at h
    linarith
  change (execution.emissionTimes 0).flatMap send = _
  rw [Execution.emissionTimes, Execution.emissions_append, Execution.emissions_append, leadSilent,
    finish.silent, List.nil_append, List.append_nil, LessonProbeRun.execution, Execution.emissions_append,
    fired, List.filter_append, List.map_append, List.flatMap_append]
  have none : ((probe.admission.execution.ledger.emissions.filter (fun e => e.1 = 0)).map Prod.snd).flatMap send = [] := by
    rw [List.flatMap_map]
    exact List.flatMap_eq_nil_iff.mpr (fun e he => earlier e (List.mem_filter.mp he).1)
  rw [none, List.nil_append]
  simp

private noncomputable def selectorReadPulse (time : ℝ) : Delivery 1 := ⟨0, 2, time + 174⟩

private noncomputable def feedbackPulse (F : ℝ) : Delivery 1 := ⟨0, 2, F + 7 / 20⟩

/-- Only the diagnostic readout can write this selector. The optional
write is a real token, and the common probe reads its stored dose. -/
private noncomputable def seriesFeedback (time : ℝ) (adaptive : Bool) (F : ℝ) : List (Delivery 1) :=
  if adaptive ∧ time + 157 ≤ F then [feedbackPulse F] else []

private theorem staged_selector_exists {θ ε time T F} (box : @PhysicalBox 1 θ ε)
    (window : time + 157 ≤ F ∧ F < time + 158) (horizon : time + 198 < T) (adaptive : Bool) :
    ∃ (run : LocalRun θ ((preparedTeacher time).requeue
      ([selectorReadPulse time] ++ seriesFeedback time adaptive F)) T) (fire : Option ℝ),
      fire.isSome = adaptive ∧
      (∀ G, fire = some G → time + 174 < G ∧ G < time + 175) ∧
      run.execution.emissionTimes 0 = fire.toList := by
  let origin := F + 7 / 20 - 1 / 2
  let ports : List Port := if adaptive then [2] else []
  let initial := (preparedTeacher origin).requeue (lessonDeliveries origin ports)
  let pulse := selectorReadPulse time
  have initialPhysical := preparedTeacher_physical box origin (lessonDeliveries origin ports)
  have ready : ReadyCoordinates initial 0 :=
    ⟨rfl, by norm_num [initial, Snapshot.requeue, preparedTeacher],
      fun _ => ⟨rfl, by norm_num [initial, Snapshot.requeue, preparedTeacher, RestBand]⟩⟩
  have headroom (p : Port) : initial.x 0 (.z p) + (3 / 5 : ℝ) * ports.count p ≤ 3 / 5 := by
    change (0 : ℝ) + (3 / 5 : ℝ) * ports.count p ≤ 3 / 5
    cases adaptive with
    | false => norm_num [ports]
    | true =>
      by_cases h : p = 2
      · simp [ports, h]
      · norm_num [ports, h, Ne.symm]
  obtain ⟨lesson⟩ := lesson_dose_run_exists (start := initial) (ports := ports) box initialPhysical
    (by simp [RawValid, initial, Snapshot.requeue, preparedTeacher]) ready (fun _ => rfl) rfl headroom
  have before : lesson.final.time < pulse.due := by
    rw [lesson.complete.1]
    change origin + 8 * ports.length < time + 174
    have b := window.2
    cases adaptive <;> norm_num [ports, origin] <;> linarith
  have gain : initial.x 0 (.z pulse.port) + (3 / 5 : ℝ) * ports.count pulse.port =
      if adaptive then 3 / 5 else 0 := by
    change (0 : ℝ) + (3 / 5 : ℝ) * ports.count 2 = _
    cases adaptive <;> norm_num [ports]
  obtain ⟨read⟩ := dose_readout_exists (T := T) box lesson initialPhysical before
    (by change time + 174 + 23 ≤ T; linarith) rfl gain
  have clock : time < origin := by dsimp [origin]; linarith [window.1]
  let start := withFuture initial [pulse]
  have future : ∀ d ∈ start.pending, start.time ≤ d.due := by
    intro d hd
    change d ∈ pulse :: lessonDeliveries origin ports at hd
    rcases List.mem_cons.mp hd with rfl | tail
    · change origin ≤ time + 174
      dsimp [origin]
      linarith [window.2]
    · change origin ≤ d.due
      linarith [lesson_delivery_time tail]
  obtain ⟨lead, leadPositive, leadSilent, _⟩ := rest_prefix (θ := θ) (s := start) clock
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) future
  have calendar : {start with time := time} =
      (preparedTeacher time).requeue ([pulse] ++ seriesFeedback time adaptive F) := by
    cases adaptive <;>
      simp [start, initial, pulse, origin, ports, withFuture, lessonDeliveries,
        Snapshot.requeue, preparedTeacher, seriesFeedback, window.1, feedbackPulse]
  let execution := lead.append read.execution
  let run : LocalRun θ {start with time := time} T :=
    ⟨_, execution, read.complete, (Execution.contactsTransversal_append _ _).2 ⟨leadPositive, read.transverse⟩⟩
  have ledger : run.execution.ledger.emissions = read.fire.toList.map (fun F => (0, F)) := by
    change execution.ledger.emissions = _
    rw [Execution.emissions_append, leadSilent, List.nil_append, read.emissions]
  have dates : run.execution.emissionTimes 0 = read.fire.toList := run.dates_of_ledger _ ledger
  have actualWindow (G : ℝ) (h : read.fire = some G) : time + 174 < G ∧ G < time + 175 := by
    obtain ⟨early, late⟩ := read.window G h
    change time + 174 < G at early
    change G < time + 174 + 1 at late
    exact ⟨early, by linarith⟩
  have transport {target : Snapshot 1} (eq : {start with time := time} = target) :
      ∃ result : LocalRun θ target T, result.execution.emissionTimes 0 = read.fire.toList := by
    cases eq
    exact ⟨run, dates⟩
  obtain ⟨result, dates⟩ := transport calendar
  exact ⟨result, read.fire, read.reports, actualWindow, dates⟩

private noncomputable def practiceReceiver (time : ℝ) : Snapshot 1 :=
  (seriesTrial time true true).requeue []

private theorem staged_practice_exists {θ ε time T} (box : @PhysicalBox 1 θ ε)
    (horizon : time + 276 < T) (adaptive : Bool) :
    ∃ (run : LocalRun θ ((practiceReceiver time).requeue
      (if adaptive then (seriesTrial (time + 180) true true).pending else [])) T) (fire : Option ℝ),
      fire.isSome = adaptive ∧
      (∀ F, fire = some F → time + 245 < F ∧ F < time + 246) ∧
      run.execution.emissionTimes 0 = fire.toList ∧
      run.execution.deliveries.length = (if adaptive then 7 else 0) := by
  cases adaptive with
  | false =>
    let start := practiceReceiver time
    have ready (i : Fin 1) : ReadyCoordinates start i :=
      ⟨rfl, by norm_num [start, practiceReceiver, seriesTrial, Snapshot.requeue, withFuture,
          readoutLearner, preparedTeacher],
        fun _ => ⟨rfl, by norm_num [start, practiceReceiver, seriesTrial, Snapshot.requeue,
          withFuture, readoutLearner, preparedTeacher, RestBand]⟩⟩
    obtain ⟨e, complete, positive, silent, deliveries⟩ := quiet_ready_tail_exists (θ := θ)
      (s := start) (T := T) (by change time < T; linarith) ready (fun _ _ => rfl) rfl
    have dates : e.emissionTimes 0 = [] := by simp [Execution.emissionTimes, silent]
    exact ⟨⟨_, e, complete, positive⟩, none, rfl, by simp, dates, by change e.deliveries.length = 0; rw [deliveries]; rfl⟩
  | true =>
    obtain ⟨run, fire, reports, window, dates, count⟩ := staged_trial_exists box
      (time := time) (clock := time + 180) (T := T) (by linarith) (by linarith) true true
    refine ⟨run, fire, reports, ?_, dates, count⟩
    intro F h
    obtain ⟨a,b⟩ := window F h
    constructor <;> linarith

private noncomputable def queueHead {n} (s : Snapshot n) (h : Snapshot 1) : Snapshot (n + 1) :=
  s.prependQueued h (independentHeadQueue s h)

private noncomputable def probeReceiver (time : ℝ) : Snapshot 1 :=
  { seriesTrial (time + 70) false false with time := time, pending := [] }

private noncomputable def selectorReceiver (time : ℝ) : Snapshot 1 :=
  (preparedTeacher time).requeue [selectorReadPulse time]

private noncomputable def probeLaunch (time : ℝ) : HeadRoutes 1 :=
  atCell 0 (fixedCalendar (time + 69) (seriesTrial (time + 70) false false).pending)

private noncomputable def inverterInput (time : ℝ) : HeadRoutes 2 :=
  atCell 0 (fixedCalendar (time + 141) [⟨0, 1, time + 140 + 1⟩])

private noncomputable def selectorInput (time : ℝ) (adaptive : Bool) : HeadRoutes 3 :=
  atCell 0 (seriesFeedback time adaptive)

private noncomputable def practiceLaunch (time : ℝ) : HeadRoutes 4 :=
  atCell 0 (fixedCalendar (time + 179) (seriesTrial (time + 180) true true).pending)

private noncomputable def creditPulses (p : Port) (F : ℝ) : List (Delivery 1) :=
  [⟨0, p, F + 7 / 20⟩]

private noncomputable def seriesCreditInput : HeadRoutes 5 :=
  fun i F => atCell 4 (creditPulses 0) i F ++ atCell 0 (creditPulses 1) i F

private theorem probeLaunch_strict (time : ℝ) : StrictHeadRoutes (probeLaunch time) :=
  atCell_strict _ (fixedCalendar_strict (fun d h => by linarith [series_trial_future h]))

private theorem inverterInput_strict (time : ℝ) : StrictHeadRoutes (inverterInput time) :=
  atCell_strict _ (fixedCalendar_strict (by
    intro d hd
    obtain rfl := List.mem_singleton.mp hd
    change time + 141 ≤ time + 140 + 1
    linarith))

private theorem selectorInput_strict (time : ℝ) (adaptive : Bool) :
    StrictHeadRoutes (selectorInput time adaptive) :=
  atCell_strict _ (by
    intro F d hd
    by_cases h : adaptive ∧ time + 157 ≤ F
    · have eq : d = feedbackPulse F := by simpa [seriesFeedback, h] using hd
      rw [eq]
      change F < F + 7 / 20
      linarith
    · simp [seriesFeedback, h] at hd)

private theorem practiceLaunch_strict (time : ℝ) : StrictHeadRoutes (practiceLaunch time) :=
  atCell_strict _ (fixedCalendar_strict (fun d h => by linarith [series_trial_future h]))

private theorem creditPulses_strict (p : Port) : ∀ F d, d ∈ creditPulses p F → F < d.due := by
  intro F d hd
  obtain rfl := List.mem_singleton.mp hd
  change F < F + 7 / 20
  linarith

private theorem seriesCreditInput_strict : StrictHeadRoutes seriesCreditInput := by
  intro i F d hd
  rcases List.mem_append.mp hd with a | b
  · exact atCell_strict 4 (creditPulses_strict 0) i F d a
  · exact atCell_strict 0 (creditPulses_strict 1) i F d b

private noncomputable def readoutCoreStart (time : ℝ) : Snapshot 6 :=
  let first := seriesTrial time false true
  let probe := queueHead first (probeReceiver time)
  let inverter := queueHead probe (inverterSource time)
  let selector := queueHead inverter (selectorReceiver time)
  let practice := queueHead selector (practiceReceiver time)
  practice.prependQueued (preparedTeacher time) (practice.pending.map Delivery.succ)

private noncomputable def readoutCoreRouter (time : ℝ) (adaptive : Bool) : Router 6 :=
  let probe := prependRouted (fun _ _ => []) (probeLaunch time)
  let inverter := prependRouted probe (inverterInput time)
  let selector := prependRouted inverter (selectorInput time adaptive)
  let practice := prependRouted selector (practiceLaunch time)
  prependRouted practice seriesCreditInput

private theorem readoutCore_causal (time : ℝ) (adaptive : Bool) :
    StrictCausalRouter (readoutCoreRouter time adaptive) :=
  prepend_routed_causal
    (prepend_routed_causal
      (prepend_routed_causal
        (prepend_routed_causal
          (prepend_routed_causal (fun _ _ _ hd => (List.not_mem_nil hd).elim) (probeLaunch_strict time))
          (inverterInput_strict time))
        (selectorInput_strict time adaptive))
      (practiceLaunch_strict time))
    seriesCreditInput_strict

private abbrev readoutCoreParameters (first probe inverter selector practice credit : Fin 1 → Parameters) :
    Fin 6 → Parameters :=
  prependParameters credit (prependParameters practice (prependParameters selector
    (prependParameters inverter (prependParameters probe first))))

private structure CoreRun (θ : Fin 6 → Parameters) (time T : ℝ) (adaptive : Bool) where
  final : Snapshot 6
  execution : Execution θ (readoutCoreRouter time adaptive) (readoutCoreStart time) final
  complete : CompleteThrough execution T
  positive : execution.ContactsTransversal
  prep : final.x 0 (.z 0) = 3 / 5
  practice : final.x 0 (.z 1) = if adaptive then 3 / 5 else 0
  first : ℝ
  firstDates : execution.emissionTimes 5 = [first]
  firstWindow : time + 65 < first ∧ first < time + 66
  practiceFire : Option ℝ
  practiceDates : execution.emissionTimes 1 = practiceFire.toList
  practiceFlag : practiceFire.isSome = adaptive
  practiceWindow : ∀ F, practiceFire = some F → time + 245 < F ∧ F < time + 246
  firstTrial : lessonReceipts execution.deliveries 5 = 8
  failedTrial : lessonReceipts execution.deliveries 4 = 7
  noPassOnFailure : execution.emissionTimes 4 = []
  selectorReads : (execution.emissionTimes 2).length = if adaptive then 1 else 0
  practiceTrial : lessonReceipts execution.deliveries 1 = if adaptive then 7 else 0

private theorem readout_core_exists {θF θP θI θS θR θC ε time T}
    (firstBox : @PhysicalBox 1 θF ε) (probeBox : @PhysicalBox 1 θP ε)
    (inverterBox : @PhysicalBox 1 θI ε) (selectorBox : @PhysicalBox 1 θS ε)
    (practiceBox : @PhysicalBox 1 θR ε) (creditBox : @PhysicalBox 1 θC ε)
    (horizon : time + 276 < T) (adaptive : Bool) :
    Nonempty (CoreRun (readoutCoreParameters θF θP θI θS θR θC) time T adaptive) := by
  obtain ⟨first, fire, flag, window, dates, firstCount⟩ := staged_trial_exists firstBox
    (time := time) (clock := time) (T := T) le_rfl (by linarith) false true
  obtain ⟨F, hF⟩ := fired flag
  have firstWindow := window F hF
  have firstDates : first.execution.emissionTimes 0 = [F] := by rw [dates, hF]; rfl
  obtain ⟨probe, probeFire, probeFlag, _, probeDates, probeCount⟩ := staged_trial_exists probeBox
    (time := time) (clock := time + 70) (T := T) (by linarith) (by linarith) false false
  have noProbeFire : probe.execution.emissionTimes 0 = [] := by rw [probeDates, silent probeFlag]; rfl
  have probeQueue : first.execution.headInputQueue (probeLaunch time) =
      (seriesTrial (time + 70) false false).pending := by
    rw [show probeLaunch time = atCell 0 (fixedCalendar (time + 69)
      (seriesTrial (time + 70) false false).pending) from rfl, atCell_inputs, firstDates]
    simp [fixedCalendar, show F < time + 69 by linarith [firstWindow.2]]
  have probeBalance := stage_balance first.execution
    ({seriesTrial (time + 70) false false with time := time} : Snapshot 1) [] (probeLaunch time)
    (by simpa only [List.nil_append] using List.Perm.of_eq probeQueue)
  obtain ⟨paired⟩ := first.execution.prepend_causal_result probe.execution rfl
    (first.complete.1.trans probe.complete.1.symm) (probeLaunch time) (probeLaunch_strict time) _ probeBalance
  have pairedComplete := paired.complete first.complete probe.complete
  have pairedPositive := paired.contacts_transversal first.positive probe.positive
  have bProbeDates : paired.execution.emissionTimes 0 = [] := paired.head_emission_times.trans noProbeFire
  obtain ⟨inverter, failure, failureEarly, failureLate, inverterDates⟩ :=
    staged_inverter_exists inverterBox (time := time) (T := T) (by linarith)
  have invQueue : paired.execution.headInputQueue (inverterInput time) = [] := by
    rw [show inverterInput time = atCell 0 (fixedCalendar (time + 141) [⟨0, 1, time + 140 + 1⟩]) from rfl,
      atCell_inputs, bProbeDates]
    rfl
  have invBalance := stage_balance paired.execution (inverterSource time) (inverterSource time).pending
    (inverterInput time) (by simp [invQueue])
  obtain ⟨diagnosed⟩ := paired.execution.prepend_causal_result inverter.execution rfl
    (pairedComplete.1.trans inverter.complete.1.symm) (inverterInput time) (inverterInput_strict time) _ invBalance
  have diagnosedComplete := diagnosed.complete pairedComplete inverter.complete
  have diagnosedPositive := diagnosed.contacts_transversal pairedPositive inverter.positive
  obtain ⟨selector, selectedFire, selectedFlag, selectedWindow, selectedDates⟩ :=
    staged_selector_exists selectorBox (time := time) (T := T)
      ⟨failureEarly, failureLate⟩ (by linarith) adaptive
  have selectorQueueEq : diagnosed.execution.headInputQueue (selectorInput time adaptive) =
      seriesFeedback time adaptive failure := by
    rw [show selectorInput time adaptive = atCell 0 (seriesFeedback time adaptive) from rfl,
      atCell_inputs, diagnosed.head_emission_times]
    apply inverterDates
    intro date early
    simp [seriesFeedback, not_le.mpr early]
  have selectBalance := stage_balance diagnosed.execution
    ((preparedTeacher time).requeue ([selectorReadPulse time] ++ seriesFeedback time adaptive failure))
    [selectorReadPulse time] (selectorInput time adaptive) (by rw [selectorQueueEq]; rfl)
  obtain ⟨selected⟩ := diagnosed.execution.prepend_causal_result selector.execution rfl
    (diagnosedComplete.1.trans selector.complete.1.symm) (selectorInput time adaptive)
    (selectorInput_strict time adaptive) _ selectBalance
  have selectedComplete := selected.complete diagnosedComplete selector.complete
  have selectedPositive := selected.contacts_transversal diagnosedPositive selector.positive
  obtain ⟨practice, practiceFire, practiceFlag, practiceWindow, practiceDates, practiceCount⟩ :=
    staged_practice_exists practiceBox (time := time) (T := T) horizon adaptive
  have practiceQueueEq : selected.execution.headInputQueue (practiceLaunch time) =
      if adaptive then (seriesTrial (time + 180) true true).pending else [] := by
    rw [show practiceLaunch time = atCell 0 (fixedCalendar (time + 179)
      (seriesTrial (time + 180) true true).pending) from rfl, atCell_inputs,
      selected.head_emission_times, selectedDates]
    cases h : selectedFire with
    | none =>
      have eq : adaptive = false := by simpa [h] using selectedFlag.symm
      simp [eq]
    | some G =>
      have eq : adaptive = true := by simpa [h] using selectedFlag.symm
      have early : G < time + 179 := by linarith [(selectedWindow G h).2]
      simp [eq, fixedCalendar, early]
  have practiceBalance := stage_balance selected.execution
    ((practiceReceiver time).requeue (if adaptive then (seriesTrial (time + 180) true true).pending else []))
    [] (practiceLaunch time) (by rw [practiceQueueEq]; rfl)
  obtain ⟨tested⟩ := selected.execution.prepend_causal_result practice.execution rfl
    (selectedComplete.1.trans practice.complete.1.symm) (practiceLaunch time) (practiceLaunch_strict time) _
    practiceBalance
  have testedComplete := tested.complete selectedComplete practice.complete
  have testedPositive := tested.contacts_transversal selectedPositive practice.positive
  have testedFirst : tested.execution.emissionTimes 4 = [F] := by
    change tested.execution.emissionTimes ((0 : Fin 1).succ.succ.succ.succ) = _
    rw [tested.tail_emission_times, selected.tail_emission_times, diagnosed.tail_emission_times,
      paired.tail_emission_times, firstDates]
  have testedPractice : tested.execution.emissionTimes 0 = practiceFire.toList :=
    tested.head_emission_times.trans practiceDates
  obtain ⟨credit⟩ := two_credit_run_exists creditBox (time := time) (T := T) (second := practiceFire)
    (show time < F ∧ F + 8 ≤ T by constructor <;> linarith [firstWindow.1, firstWindow.2])
    (fun G h => by obtain ⟨lo, hi⟩ := practiceWindow G h; constructor <;> linarith [firstWindow.2])
  let creditStart := (preparedTeacher time).requeue
    (⟨0, 0, F + 7 / 20⟩ :: practiceFire.toList.map (fun G => ⟨0, 1, G + 7 / 20⟩))
  have creditQueueEq : (tested.execution.headInputQueue seriesCreditInput).Perm creditStart.pending := by
    have split := (List.flatMap_append_perm tested.execution.ledger.emissions
      (fun event => atCell 4 (creditPulses 0) event.1 event.2)
      (fun event => atCell 0 (creditPulses 1) event.1 event.2)).symm
    change (tested.execution.headInputQueue seriesCreditInput).Perm
      (tested.execution.headInputQueue (atCell 4 (creditPulses 0)) ++
        tested.execution.headInputQueue (atCell 0 (creditPulses 1))) at split
    refine split.trans (List.Perm.of_eq ?_)
    rw [atCell_inputs, atCell_inputs, testedFirst, testedPractice]
    cases h : practiceFire <;> simp [creditStart, Snapshot.requeue, creditPulses, h]
  have creditBalance := stage_balance tested.execution creditStart [] seriesCreditInput
    (by simpa only [List.nil_append] using creditQueueEq)
  obtain ⟨whole⟩ := tested.execution.prepend_causal_result credit.execution rfl
    (testedComplete.1.trans credit.complete.1.symm) seriesCreditInput seriesCreditInput_strict _ creditBalance
  have complete := whole.complete testedComplete credit.complete
  have positive := whole.contacts_transversal testedPositive credit.positive
  have prepGain := credit.firstGain
  have practiceGain : credit.final.x 0 (.z 1) = if adaptive then 3 / 5 else 0 := by
    rw [credit.secondGain, practiceFlag]
  have firstOut : whole.execution.emissionTimes 5 = [F] := by
    change whole.execution.emissionTimes (4 : Fin 5).succ = _
    rw [whole.tail_emission_times, testedFirst]
  have practiceOut : whole.execution.emissionTimes 1 = practiceFire.toList := by
    change whole.execution.emissionTimes (0 : Fin 5).succ = _
    rw [whole.tail_emission_times, testedPractice]
  have firstReceipts : lessonReceipts whole.execution.deliveries 5 = 8 := by
    change lessonReceipts whole.execution.deliveries (0 : Fin 1).succ.succ.succ.succ.succ = _
    rw [CausalTraceBalance.tail_receipts whole.trace, CausalTraceBalance.tail_receipts tested.trace,
      CausalTraceBalance.tail_receipts selected.trace, CausalTraceBalance.tail_receipts diagnosed.trace,
      CausalTraceBalance.tail_receipts paired.trace, lessonReceipts]
    have all : first.execution.deliveries.filter (fun d => d.cell == 0) = first.execution.deliveries :=
      List.filter_eq_self.mpr (fun d _ => by rw [Subsingleton.elim d.cell 0]; rfl)
    rw [all, firstCount]
    rfl
  have probeReceipts : lessonReceipts whole.execution.deliveries 4 = 7 := by
    change lessonReceipts whole.execution.deliveries (0 : Fin 2).succ.succ.succ.succ = _
    rw [CausalTraceBalance.tail_receipts whole.trace, CausalTraceBalance.tail_receipts tested.trace,
      CausalTraceBalance.tail_receipts selected.trace, CausalTraceBalance.tail_receipts diagnosed.trace,
      CausalTraceBalance.head_receipts paired.trace, probeCount]
    rfl
  have probeSilent : whole.execution.emissionTimes 4 = [] := by
    change whole.execution.emissionTimes (0 : Fin 2).succ.succ.succ.succ = _
    rw [whole.tail_emission_times, tested.tail_emission_times, selected.tail_emission_times,
      diagnosed.tail_emission_times, bProbeDates]
  have selectorReads : (whole.execution.emissionTimes 2).length = if adaptive then 1 else 0 := by
    change (whole.execution.emissionTimes (0 : Fin 4).succ.succ).length = _
    rw [whole.tail_emission_times, tested.tail_emission_times, selected.head_emission_times, selectedDates]
    cases adaptive with
    | false => rw [silent selectedFlag]; rfl
    | true => obtain ⟨_, h⟩ := fired selectedFlag; rw [h]; rfl
  have practiceReceipts : lessonReceipts whole.execution.deliveries 1 = if adaptive then 7 else 0 := by
    change lessonReceipts whole.execution.deliveries (0 : Fin 5).succ = _
    rw [CausalTraceBalance.tail_receipts whole.trace, CausalTraceBalance.head_receipts tested.trace, practiceCount]
  exact ⟨⟨_, whole.execution, complete, positive, prepGain, practiceGain,
    F, firstOut, firstWindow, practiceFire, practiceOut, practiceFlag, practiceWindow,
    firstReceipts, probeReceipts, probeSilent, selectorReads, practiceReceipts⟩⟩

/-- Cells 0, 1 and 2 receive the deployed 8-, 6- and 7-pulse lessons.
Cells 3 through 8 carry credits, practice trial, selector, diagnostic,
failed preparation trial and first accepted trial, in that order. -/
noncomputable def readoutSeriesStart (time : ℝ) : Snapshot 9 :=
  queueHead (addEmptyLearner (addEmptyLearner (readoutCoreStart time))) (nativeLessonStart time ⟨4, 4⟩)

noncomputable def readoutSeriesRouter (time : ℝ) (adaptive : Bool) : Router 9 :=
  let seven := prependRouted (readoutCoreRouter time adaptive) (deployedLessonContacts 5 10 ⟨3, 4⟩)
  let six := prependRouted seven (deployedLessonContacts 2 10 ⟨3, 3⟩)
  prependRouted six (fun _ _ => [])

abbrev readoutSeriesParameters
    (first probe inverter selector practice credit seven six eight : Fin 1 → Parameters) :
    Fin 9 → Parameters :=
  prependParameters eight (prependParameters six (prependParameters seven
    (readoutCoreParameters first probe inverter selector practice credit)))

theorem readoutSeriesRouter_causal (time : ℝ) (adaptive : Bool) :
    StrictCausalRouter (readoutSeriesRouter time adaptive) :=
  prepend_routed_causal (prepend_routed_causal
    (prepend_routed_causal (readoutCore_causal time adaptive)
      (deployed_contacts_strict 5 (by norm_num : (0 : ℝ) < 10) ⟨3, 4⟩))
    (deployed_contacts_strict 2 (by norm_num : (0 : ℝ) < 10) ⟨3, 3⟩))
    (fun _ _ _ h => (List.not_mem_nil h).elim)

private theorem readout_core_physical {θF θP θI θS θR θC ε}
    (firstBox : @PhysicalBox 1 θF ε) (probeBox : @PhysicalBox 1 θP ε)
    (inverterBox : @PhysicalBox 1 θI ε) (selectorBox : @PhysicalBox 1 θS ε)
    (practiceBox : @PhysicalBox 1 θR ε) (creditBox : @PhysicalBox 1 θC ε) (time : ℝ) :
    PhysicalInvariant (readoutCoreParameters θF θP θI θS θR θC) (readoutCoreStart time) := by
  have first : PhysicalInvariant θF (seriesTrial time false true) := by
    have p := readout_learner_physical firstBox time ⟨3, 4⟩ 0
    exact ⟨p.region, p.gain_cap, p.recovery_cap, p.reserve⟩
  have probe : PhysicalInvariant θP (probeReceiver time) := by
    have p := readout_learner_physical probeBox (time + 70) ⟨2, 4⟩ 0
    exact ⟨p.region, p.gain_cap, p.recovery_cap, p.reserve⟩
  have inverter : PhysicalInvariant θI (inverterSource time) := by
    have p := lessonProbe_physical (prepared := false) (time := time + 140) inverterBox
    exact ⟨p.region, p.gain_cap, p.recovery_cap, p.reserve⟩
  have selector : PhysicalInvariant θS (selectorReceiver time) :=
    preparedTeacher_physical selectorBox time _
  have practice : PhysicalInvariant θR (practiceReceiver time) := by
    have p := readout_learner_physical practiceBox time ⟨3, 3⟩ 1
    exact ⟨p.region, p.gain_cap, p.recovery_cap, p.reserve⟩
  exact prepend_physical (prepend_physical (prepend_physical
    (prepend_physical (prepend_physical first probe _) inverter _) selector _) practice _)
    (preparedTeacher_physical creditBox time []) _

/-- A single complete native execution checks both improvements using
the physical learners. The frozen run changes only the feedback wire. -/
theorem native_readout_eight_seven_six {θF θP θI θS θR θC θ7 θ6 θ8 ε}
    (firstBox : @PhysicalBox 1 θF ε) (probeBox : @PhysicalBox 1 θP ε)
    (inverterBox : @PhysicalBox 1 θI ε) (selectorBox : @PhysicalBox 1 θS ε)
    (practiceBox : @PhysicalBox 1 θR ε) (creditBox : @PhysicalBox 1 θC ε)
    (sevenBox : @PhysicalBox 1 θ7 ε) (sixBox : @PhysicalBox 1 θ6 ε) (eightBox : @PhysicalBox 1 θ8 ε)
    (time : ℝ) (adaptive : Bool) :
    let θ := readoutSeriesParameters θF θP θI θS θR θC θ7 θ6 θ8
    let route := readoutSeriesRouter time adaptive
    let start := readoutSeriesStart time
    ∃ (final : Snapshot 9) (e : Execution θ route start final)
      (crossing : CrossingExecution θ route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing (time + 330) ∧
      lessonReceipts e.deliveries 0 = 8 ∧ lessonReceipts e.deliveries 2 = 7 ∧
      lessonReceipts e.deliveries 1 = (if adaptive then 6 else 0) ∧
      NativeRetains final 0 ⟨3, 3⟩ ∧ NativeRetains final 2 ⟨3, 3⟩ ∧
      (NativeRetains final 1 ⟨3, 3⟩ ↔ adaptive = true) ∧
      final.x 3 (.z 0) = 3 / 5 ∧ final.x 3 (.z 1) = (if adaptive then 3 / 5 else 0) ∧
      lessonReceipts e.deliveries 8 = 8 ∧ lessonReceipts e.deliveries 7 = 7 ∧
      e.emissionTimes 7 = [] ∧ lessonReceipts e.deliveries 4 = (if adaptive then 7 else 0) ∧
      (e.emissionTimes 8).length = 1 ∧
      (e.emissionTimes 5).length = (if adaptive then 1 else 0) ∧
      (e.emissionTimes 4).length = (if adaptive then 1 else 0) ∧
      (∀ (otherFinal : Snapshot 9) (other : Execution θ route start otherFinal),
        CompleteThrough other (time + 330) → other.deliveries.Perm e.deliveries) ∧
      ∀ (otherFinal : Snapshot 9) (other : CrossingExecution θ route start otherFinal),
        CrossingCompleteThrough other (time + 330) →
        otherFinal.ObservationalEq final ∧ ∀ i, other.execution.emissionTimes i = e.emissionTimes i := by
  let T := time + 330
  obtain ⟨core⟩ := readout_core_exists firstBox probeBox inverterBox selectorBox practiceBox creditBox
    (time := time) (T := T) (by dsimp [T]; linarith) adaptive
  have sevenWindow (F : ℝ) (h : some core.first = some F) :
      (readoutCoreStart time).time < F + 10 ∧ F + 10 + 8 * ((⟨3, 4⟩ : Lesson).cost : ℝ) < T := by
    obtain rfl := Option.some.inj h
    change time < core.first + 10 ∧ _
    norm_num [Lesson.cost, T]
    constructor <;> linarith [core.firstWindow.1, core.firstWindow.2]
  obtain ⟨seven⟩ := deployed_lesson_exists core.execution sevenBox core.complete core.positive (5 : Fin 6)
    (gap := 10) (by norm_num) ⟨3, 4⟩ (some core.first) core.firstDates (by decide)
    (by change time + 1 < T; dsimp [T]; linarith) sevenWindow
  have practiceDates : seven.execution.emissionTimes (2 : Fin 7) = core.practiceFire.toList := by
    change seven.execution.emissionTimes (1 : Fin 6).succ = _
    rw [seven.previousTimes, core.practiceDates]
  have sixWindow (F : ℝ) (h : core.practiceFire = some F) :
      (addEmptyLearner (readoutCoreStart time)).time < F + 10 ∧
        F + 10 + 8 * ((⟨3, 3⟩ : Lesson).cost : ℝ) < T := by
    obtain ⟨lo, hi⟩ := core.practiceWindow F h
    change time < F + 10 ∧ _
    norm_num [Lesson.cost, T]
    constructor <;> linarith
  obtain ⟨six⟩ := deployed_lesson_exists seven.execution sixBox seven.complete seven.positive (2 : Fin 7)
    (gap := 10) (by norm_num) ⟨3, 3⟩ core.practiceFire practiceDates (by decide)
    (by change time + 1 < T; dsimp [T]; linarith) sixWindow
  obtain ⟨baseline⟩ := native_lesson_exists eightBox time ⟨4, 4⟩ (by decide) (by decide)
  obtain ⟨base, baseDone, basePositive, baseCount, _, baseRetains⟩ := baseline.finish_at
    (T := T) (by norm_num [T, Lesson.cost])
  obtain ⟨whole, complete⟩ := six.execution.prepend_independent_complete base rfl six.complete baseDone
  have positive := whole.contacts_transversal six.positive basePositive
  have box := prepend_box
    (prepend_box (prepend_box (prepend_box (prepend_box (prepend_box (prepend_box
      (prepend_box firstBox probeBox) inverterBox) selectorBox) practiceBox) creditBox) sevenBox) sixBox) eightBox
  have ps := readout_core_physical firstBox probeBox inverterBox selectorBox practiceBox creditBox time
  have p7 : PhysicalInvariant (prependParameters θ7 (readoutCoreParameters θF θP θI θS θR θC))
      (addEmptyLearner (readoutCoreStart time)) :=
    prepend_physical ps (native_lesson_physical sevenBox time ⟨0, 0⟩) _
  have p6 : PhysicalInvariant (prependParameters θ6 (prependParameters θ7 (readoutCoreParameters θF θP θI θS θR θC)))
      (addEmptyLearner (addEmptyLearner (readoutCoreStart time))) :=
    prepend_physical p7 (native_lesson_physical sixBox time ⟨0, 0⟩) _
  have physical : PhysicalInvariant (readoutSeriesParameters θF θP θI θS θR θC θ7 θ6 θ8)
      (readoutSeriesStart time) :=
    prepend_physical p6 (native_lesson_physical eightBox time ⟨4, 4⟩) _
  have initial : InitiallyBelowReady (readoutSeriesStart time) := by
    intro i c h
    cases c with
    | q => fin_cases i <;> change (1 / 10 : ℝ) < 1 <;> norm_num
    | m p => fin_cases i <;> change (1 / 40 : ℝ) < 1 <;> norm_num
    | z _ => exact False.elim h
    | b => exact False.elim h
    | energy => exact False.elim h
  have deployedSeven : lessonReceipts whole.execution.deliveries 2 = 7 := by
    change lessonReceipts whole.execution.deliveries (0 : Fin 7).succ.succ = _
    rw [CausalTraceBalance.tail_receipts whole.trace, six.previousReceipts]
    exact seven.count
  have deployedSix : lessonReceipts whole.execution.deliveries 1 = if adaptive then 6 else 0 := by
    change lessonReceipts whole.execution.deliveries (0 : Fin 8).succ = _
    rw [CausalTraceBalance.tail_receipts whole.trace, six.count, core.practiceFlag]
    cases adaptive <;> rfl
  have carried (i : Fin 6) :
      lessonReceipts whole.execution.deliveries i.succ.succ.succ =
        lessonReceipts core.execution.deliveries i := by
    rw [CausalTraceBalance.tail_receipts whole.trace, six.previousReceipts, seven.previousReceipts]
  have carriedDates (i : Fin 6) : whole.execution.emissionTimes i.succ.succ.succ =
      core.execution.emissionTimes i := by
    rw [whole.tail_emission_times, six.previousTimes, seven.previousTimes]
  have noProbe : whole.execution.emissionTimes 7 = [] :=
    (carriedDates 4).trans core.noPassOnFailure
  have firstAccepted : (whole.execution.emissionTimes 8).length = 1 := by
    change (whole.execution.emissionTimes (5 : Fin 6).succ.succ.succ).length = _
    rw [carriedDates, core.firstDates]
    rfl
  have selectorFired : (whole.execution.emissionTimes 5).length = if adaptive then 1 else 0 := by
    change (whole.execution.emissionTimes (2 : Fin 6).succ.succ.succ).length = _
    rw [carriedDates]
    exact core.selectorReads
  have practiceAccepted : (whole.execution.emissionTimes 4).length = if adaptive then 1 else 0 := by
    change (whole.execution.emissionTimes (1 : Fin 6).succ.succ.succ).length = _
    rw [carriedDates, core.practiceDates]
    cases adaptive with
    | false => rw [silent core.practiceFlag]; rfl
    | true => obtain ⟨_, h⟩ := fired core.practiceFlag; rw [h]; rfl
  refine ⟨_, whole.execution, whole.execution.toCrossing initial box physical positive, rfl,
    complete.toCrossing whole.execution initial box physical positive,
    (CausalTraceBalance.head_receipts whole.trace).trans baseCount, deployedSeven, deployedSix,
    ?_, ?_, ?_, ?_, ?_, (carried 5).trans core.firstTrial, (carried 4).trans core.failedTrial,
    noProbe, (carried 1).trans core.practiceTrial, firstAccepted, selectorFired, practiceAccepted, ?_, ?_⟩
  · exact (baseRetains ⟨3, 3⟩).mpr (by decide)
  · change NativeRetains six.final (0 : Fin 7).succ ⟨3, 3⟩
    unfold NativeRetains
    rw [six.previousValues]
    exact (seven.retention ⟨3, 3⟩).mpr (by change ((⟨3, 4⟩ : Lesson).train ⟨3, 3⟩).retained = true; decide)
  · change NativeRetains six.final 0 ⟨3, 3⟩ ↔ adaptive = true
    rw [six.retention, core.practiceFlag]
    cases adaptive <;> decide
  · change six.final.x (0 : Fin 6).succ.succ (.z 0) = _
    rw [six.previousValues, seven.previousValues]
    exact core.prep
  · change six.final.x (0 : Fin 6).succ.succ (.z 1) = _
    rw [six.previousValues, seven.previousValues]
    exact core.practice
  · intro otherFinal other done
    exact same_complete_deliveries whole.execution other box physical complete done
  · intro otherFinal other done
    obtain ⟨native, same⟩ := other.execution.toNative_of_transverse_completion whole.execution
      (readoutSeriesRouter_causal time adaptive) box physical complete positive (le_of_eq done.1)
    have weak := done.toWeak_of_native other native same initial box physical
    exact ⟨(whole.execution.observational_unique_weak box other.execution physical complete positive weak).1.symm,
      fun i => (whole.execution.emissionTimes_unique_weak other.execution box physical complete positive weak i).symm⟩

end RecursiveLearning.Native
