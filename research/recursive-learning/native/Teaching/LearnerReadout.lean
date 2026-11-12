import Teaching.SerialAcceptance

/-! A reduced lesson is delivered to the physical learner that is read.
A second cell inverts the readout so that failure issues a positive
feedback pulse to the selector. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

def preparationTrial (third : Bool) : Lesson :=
  ⟨if third then 3 else 2, 4⟩

def practiceTrial (third : Bool) : Lesson :=
  ⟨3, if third then 3 else 2⟩

noncomputable def readoutLearner (time : ℝ) (lesson : Lesson) (readPort : Port)
    (birthGain : ℝ := -(6 / 5 : ℝ)) : Snapshot 1 :=
  { nativeLessonStart time lesson with
    x := fun i c => match c with
      | .z p => if p = readPort then birthGain else -(12 / 5 : ℝ)
      | other => (preparedTeacher time).x i other }

noncomputable def learnerRead (time : ℝ) (port : Port) : Delivery 1 := ⟨0, port, time + 65⟩

noncomputable abbrev preparationLearner (time : ℝ) (third : Bool) :=
  readoutLearner time (preparationTrial third) 0

noncomputable abbrev preparationRead (time : ℝ) := learnerRead time 0

theorem readout_learner_physical_of_gain {θ ε} (box : @PhysicalBox 1 θ ε)
    (time : ℝ) (lesson : Lesson) (readPort : Port)
    (birthGain : ℝ) (nonpositive : birthGain ≤ 0) :
    PhysicalInvariant θ (readoutLearner time lesson readPort birthGain) := by
  have rest := preparedTeacher_physical box time []
  refine ⟨rest.region, ?_, rest.recovery_cap, rest.reserve⟩
  intro i p
  have cap := rest.gain_cap i p
  change (0 : ℝ) ≤ Real.log ((θ i).cap p) at cap
  change (if p = readPort then birthGain else -(12 / 5 : ℝ)) ≤ Real.log ((θ i).cap p)
  split <;> linarith

theorem readout_learner_physical {θ ε} (box : @PhysicalBox 1 θ ε)
    (time : ℝ) (lesson : Lesson) (readPort : Port) :
    PhysicalInvariant θ (readoutLearner time lesson readPort) :=
  readout_learner_physical_of_gain box time lesson readPort _ (by norm_num)

/-- Read a preparation or practice counter on the very cell that received
the full two-block trial. The read port has received two or three doses. -/
theorem full_learner_read_exists_of_gain {θ ε} (box : @PhysicalBox 1 θ ε) (time : ℝ) (lesson : Lesson)
    (port : Port) (third : Bool) (capacity : lesson.preparation ≤ 4 ∧ lesson.practice ≤ 4)
    (birthGain : ℝ) (nonpositive : birthGain ≤ 0)
    (gainTest : let gain := birthGain + (3 / 5 : ℝ) * (lessonPorts lesson).count port
      if third then gain = 3 / 5 else gain ≤ 0) :
    Nonempty (DoseReadout θ (readoutLearner time lesson port birthGain) (lessonPorts lesson)
      (learnerRead time port) (time + 96) third) := by
  let start := readoutLearner time lesson port birthGain
  let ports := lessonPorts lesson
  let read := learnerRead time port
  have physical := readout_learner_physical_of_gain box time lesson port birthGain nonpositive
  have ready : ReadyCoordinates start 0 :=
    ⟨rfl, by norm_num [start, readoutLearner, preparedTeacher],
      fun p => ⟨rfl, by norm_num [start, readoutLearner, preparedTeacher, RestBand]⟩⟩
  obtain ⟨h0,h1,h2⟩ := lessonPorts_count lesson
  have maxDoses (p : Port) : ports.count p ≤ 4 := by
    fin_cases p
    · change (lessonPorts lesson).count 0 ≤ 4
      rw [h0]; exact capacity.1
    · change (lessonPorts lesson).count 1 ≤ 4
      rw [h1]; exact capacity.2
    · change (lessonPorts lesson).count 2 ≤ 4
      rw [h2]; norm_num
  have bounds (p : Port) : start.x 0 (.z p) + (3 / 5 : ℝ) * ports.count p ≤ 3 / 5 := by
    change (if p = port then birthGain else -(12 / 5 : ℝ)) + 3 / 5 * ports.count p ≤ 3 / 5
    by_cases same : p = port
    · subst p
      rw [ite_eq_left rfl]
      cases third with
      | false =>
        have h : birthGain + (3 / 5 : ℝ) * ports.count port ≤ 0 := gainTest
        linarith
      | true =>
        have h : birthGain + (3 / 5 : ℝ) * ports.count port = 3 / 5 := gainTest
        exact h.le
    · rw [ite_eq_right same]
      have upper : (ports.count p : ℝ) ≤ 4 := by exact_mod_cast maxDoses p
      linarith
  obtain ⟨lessonRun⟩ := lesson_dose_run_exists box physical
    (by simp [RawValid, readoutLearner, nativeLessonStart, preparedTeacher]) ready (fun _ => rfl) rfl bounds
  have before : lessonRun.final.time < read.due := by
    rw [lessonRun.complete.1]
    change time + 8 * (lessonPorts lesson).length < time + 65
    have h : (lesson.preparation : ℝ) ≤ 4 := by exact_mod_cast capacity.1
    have k : (lesson.practice : ℝ) ≤ 4 := by exact_mod_cast capacity.2
    simp only [lessonPorts, List.length_append, List.length_replicate, Nat.cast_add]
    linarith
  apply dose_readout_exists_of_gain box lessonRun physical before
    (by change time + 65 + 23 ≤ time + 96; linarith) rfl
  change let gain := (if port = port then birthGain else -(12 / 5 : ℝ)) +
      3 / 5 * (lessonPorts lesson).count port
    if third then gain = 3 / 5 else gain ≤ 0
  simpa only [eq_self, ite_true] using gainTest

theorem full_learner_read_exists {θ ε} (box : @PhysicalBox 1 θ ε) (time : ℝ) (lesson : Lesson)
    (port : Port) (third : Bool) (capacity : lesson.preparation ≤ 4 ∧ lesson.practice ≤ 4)
    (count : (lessonPorts lesson).count port = if third then 3 else 2) :
    Nonempty (DoseReadout θ (readoutLearner time lesson port) (lessonPorts lesson)
      (learnerRead time port) (time + 96) third) := by
  apply full_learner_read_exists_of_gain box time lesson port third capacity _ (by norm_num)
  dsimp only
  rw [count]
  cases third <;> norm_num

theorem preparation_learner_read_exists {θ ε} (box : @PhysicalBox 1 θ ε) (time : ℝ) (third : Bool) :
    Nonempty (DoseReadout θ (preparationLearner time third) (lessonPorts (preparationTrial third))
      (preparationRead time) (time + 96) third) := by
  apply full_learner_read_exists box time (preparationTrial third) 0 third
  · cases third <;> decide
  · exact (lessonPorts_count (preparationTrial third)).1

theorem practice_learner_read_exists {θ ε} (box : @PhysicalBox 1 θ ε) (time : ℝ) (third : Bool) :
    Nonempty (DoseReadout θ (readoutLearner time (practiceTrial third) 1) (lessonPorts (practiceTrial third))
      (learnerRead time 1) (time + 96) third) := by
  apply full_learner_read_exists box time (practiceTrial third) 1 third
  · cases third <;> decide
  · exact (lessonPorts_count (practiceTrial third)).2.1

/-- The only optional input to the inverter is produced by the learner's
own FIRE. Its diagnostic and read pulses are common to both trials. -/
noncomputable def learnerReadContacts (time : ℝ) : HeadRoutes 1 :=
  fun _ F => if F < time + 71 then [⟨0, 1, time + 70 + 1⟩] else []

noncomputable def failureFeedbackContacts (time : ℝ) (delay : ℝ → ℝ) : HeadRoutes 2 :=
  fun i F => if i = 0 then lessonSelectorContacts (time + 70) delay 0 F else []

noncomputable def readoutFeedbackRouter (time : ℝ) (delay : ℝ → ℝ) : Router 3 :=
  prependRouted (prependRouted (fun _ _ => []) (learnerReadContacts time)) (failureFeedbackContacts time delay)

noncomputable def readoutFeedbackStart (time : ℝ) (third : Bool) : Snapshot 3 :=
  let learner := withFuture (preparationLearner time third) [preparationRead time]
  let inverter := {lessonProbeStart false (time + 70) with time := time}
  let pair := learner.prependQueued inverter (independentHeadQueue learner inverter)
  pair.prependQueued (preparedTeacher time) (pair.pending.map Delivery.succ)

/-- A quiet prefix to an exact rest snapshot. This changes the clock
continuously while the charge, reserve and all memories remain at rest. -/
theorem rest_prefix {θ : Fin 1 → Parameters} {s : Snapshot 1} {origin : ℝ}
    (later : origin < s.time) (main : ∀ i, s.main i = .ready) (aux : ∀ i p, s.aux i p = .ready)
    (raw : ∀ i p, s.raw i p = none) (q : ∀ i, s.x i .q = 1 / 10)
    (m : ∀ i p, s.x i (.m p) = 1 / 40) (reserve : ∀ i, s.x i .energy = 100)
    (future : ∀ d ∈ s.pending, s.time ≤ d.due) :
    ∃ e : Execution θ (fun _ _ => []) {s with time := origin} s,
      e.ContactsTransversal ∧ e.ledger.emissions = [] ∧ e.deliveries = [] := by
  let before : Snapshot 1 := {s with time := origin}
  let wait : Flow θ before (quietAt before s.time) :=
    quietFlow before later main aux raw
      (fun i => by change s.x i .q < 1; rw [q]; norm_num)
      (fun i p => by change s.x i (.m p) < 1; rw [m]; norm_num) future
  have vals : (quietAt before s.time).x = s.x := by
    funext i c
    cases c <;> simp [before, quietAt, quietValues, relax, q, m, reserve]
  have same : quietAt before s.time = s := congrArg (fun x => {s with x := x}) vals
  have transport {u : Snapshot 1} (eq : quietAt before s.time = u) :
      ∃ e : Execution θ (fun _ _ => []) before u,
        e.ContactsTransversal ∧ e.ledger.emissions = [] ∧ e.deliveries = [] := by
    cases eq
    exact ⟨.cons (.flow wait) (.nil _), trivial, rfl, rfl⟩
  exact transport same

private theorem learner_read_contacts_causal (time : ℝ) : StrictHeadRoutes (learnerReadContacts time) := by
  intro i F d hd
  by_cases before : F < time + 71
  · have eq : d = ⟨0, 1, time + 70 + 1⟩ := by simpa [learnerReadContacts, before] using hd
    rw [eq]
    change F < time + 70 + 1
    linarith
  · simp [learnerReadContacts, before] at hd

private theorem failure_feedback_causal {time delay} (positive : ∀ F, 0 < delay F) :
    StrictHeadRoutes (failureFeedbackContacts time delay) := by
  intro i F d hd
  by_cases h : i = 0
  · exact lesson_contacts_strict positive 0 F d (by simpa [failureFeedbackContacts, h] using hd)
  · simp [failureFeedbackContacts, h] at hd

/-- On the actual 2+4 trial, absence of the learner's preparation readout
leaves the diagnostic cell exposed. Its subsequent FIRE sends exactly one
feedback dose to the selector. On 3+4 the learner's FIRE protects the
diagnostic cell and the selector receives nothing. -/
theorem preparation_failure_updates_selector {θL θI θS ε}
    (learnerBox : @PhysicalBox 1 θL ε) (inverterBox : @PhysicalBox 1 θI ε) (selectorBox : @PhysicalBox 1 θS ε)
    (time : ℝ) (delay : ℝ → ℝ)
    (wire : ∀ F, (3 / 10 : ℝ) ≤ delay F ∧ delay F ≤ 2 / 5) (third : Bool) :
    let θ := prependParameters θS (prependParameters θI θL)
    let route := readoutFeedbackRouter time delay
    let start := readoutFeedbackStart time third
    ∃ (final : Snapshot 3) (e : Execution θ route start final)
      (crossing : CrossingExecution θ route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing (time + 96) ∧
      lessonReceipts e.deliveries 2 = (preparationTrial third).cost + 1 ∧
      (e.emissionTimes 2).length = (if third then 1 else 0) ∧
      lessonReceipts e.deliveries 0 = (if third then 0 else 1) ∧
      final.x 0 (.z 2) = (if third then 0 else 3 / 5) ∧
      final.x 0 (.z 0) = 0 ∧ final.x 0 (.z 1) = 0 ∧
      ∀ (otherFinal : Snapshot 3) (other : CrossingExecution θ route start otherFinal),
        CrossingCompleteThrough other (time + 96) →
        otherFinal.ObservationalEq final ∧ ∀ i, other.execution.emissionTimes i = e.emissionTimes i := by
  obtain ⟨learner⟩ := preparation_learner_read_exists learnerBox time third
  let clock := time + 70
  let inv := lessonProbeStart third clock
  let invStart : Snapshot 1 := {inv with time := time}
  let rawLearner := withFuture (preparationLearner time third) [preparationRead time]
  let rawInv : Snapshot 1 := {lessonProbeStart false clock with time := time}
  have invFuture : ∀ d ∈ inv.pending, inv.time ≤ d.due := by
    intro d member
    change d ∈ lessonProbeQueue third clock at member
    cases third with
    | false =>
      simp only [lessonProbeQueue, Bool.false_eq_true, ite_false, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change clock ≤ clock + 9; linarith
      · change clock ≤ clock + 17; linarith
    | true =>
      simp only [lessonProbeQueue, ite_true, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · change clock ≤ clock + 1; linarith
      · change clock ≤ clock + 9; linarith
      · change clock ≤ clock + 17; linarith
  obtain ⟨waitInv, waitPositive, waitSilent, _⟩ := rest_prefix (θ := θI) (s := inv) (origin := time)
    (by change time < time + 70; linarith) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) invFuture
  obtain ⟨inverter⟩ := lesson_probe_late_run_exists inverterBox third clock
  obtain ⟨failure, failFlag, failWindow, _, inverterQueue⟩ := readout_label inverter delay
  let traceInv := waitInv.append inverter.execution
  have invComplete : CompleteThrough traceInv (time + 96) := by
    have eq : clock + 26 = time + 96 := by dsimp [clock]; ring
    rw [← eq]
    exact inverter.complete_execution
  have invPositive : traceInv.ContactsTransversal :=
    (Execution.contactsTransversal_append _ _).2 ⟨waitPositive, inverter.contacts_transversal⟩
  let Q := independentHeadQueue rawLearner rawInv
  have extra : learner.execution.headInputQueue (learnerReadContacts time) =
      if third then [⟨0, 1, clock + 1⟩] else [] := by
    rw [Execution.headInputQueue, learner.emissions, List.flatMap_map]
    cases h : learner.fire with
    | none =>
      have no : third = false := by simpa [h] using learner.reports.symm
      simp [no]
    | some F =>
      have yes : third = true := by simpa [h] using learner.reports.symm
      have early : F < time + 71 := by
        have bound := (learner.window F h).2
        change F < time + 65 + 1 at bound
        linarith
      simp [yes, learnerReadContacts, early, clock]
  have balance : HeadQueueBalance learner.execution invStart Q (learnerReadContacts time) := by
    unfold HeadQueueBalance
    rw [learner.execution.futureHeadWires_map, extra]
    have pending : invStart.pending =
        (if third then [⟨0, 1, clock + 1⟩] else []) ++ rawInv.pending := by
      cases third <;> rfl
    change (Q : Multiset (Delivery 2)) + _ = _ +
      ((invStart.pending.map (Delivery.head (n := 1))) : Multiset (Delivery 2))
    rw [pending, List.map_append, Multiset.coe_add]
    rw [show Q = rawInv.pending.map (Delivery.head (n := 1)) ++ rawLearner.pending.map Delivery.succ from rfl,
      Multiset.coe_add]
    simpa only [List.append_assoc] using
      (Multiset.coe_eq_coe.mpr (List.perm_append_comm
        (l₁ := rawInv.pending.map (Delivery.head (n := 1)))
        (l₂ := rawLearner.pending.map Delivery.succ ++
          (if third then [⟨0, 1, clock + 1⟩] else []).map (Delivery.head (n := 1)))))
  obtain ⟨pair⟩ := learner.execution.prepend_causal_result traceInv rfl
    (learner.complete.1.trans invComplete.1.symm) (learnerReadContacts time)
    (learner_read_contacts_causal time) Q balance
  have pairComplete := pair.complete learner.complete invComplete
  have pairPositive := pair.contacts_transversal learner.transverse invPositive
  let responseRoute := failureFeedbackContacts time delay
  let pairStart := rawLearner.prependQueued invStart Q
  have invFires : traceInv.ledger.emissions = inverter.execution.ledger.emissions := by
    rw [Execution.emissions_append, waitSilent, List.nil_append]
  have pairEvents : pair.execution.ledger.emissions.Perm
      (learner.execution.ledger.emissions.map (fun e => (e.1.succ, e.2)) ++
        inverter.execution.ledger.emissions.map (fun e => ((0 : Fin 2), e.2))) := by
    apply Multiset.coe_eq_coe.mp
    apply pair.trace.emissions.trans
    exact congrArg (fun l : List (Fin 1 × ℝ) =>
      (learner.execution.ledger.emissions.map (fun e => (e.1.succ, e.2)) : Multiset (Fin 2 × ℝ)) +
        (l.map (fun e => ((0 : Fin 2), e.2)) : Multiset (Fin 2 × ℝ))) invFires
  have failureQueue : (pair.execution.headInputQueue responseRoute).Perm (selectorQueue delay failure) := by
    unfold Execution.headInputQueue
    refine (pairEvents.flatMap_right (fun event => responseRoute event.1 event.2)).trans ?_
    have none : (learner.execution.ledger.emissions.map (fun e => (e.1.succ, e.2))).flatMap
        (fun event => responseRoute event.1 event.2) = [] := by
      simp [List.flatMap_map, responseRoute, failureFeedbackContacts]
    rw [List.flatMap_append, none, List.nil_append, List.flatMap_map]
    change (inverter.execution.headInputQueue (lessonSelectorContacts clock delay)).Perm _
    rw [inverterQueue]
  obtain ⟨response⟩ := selector_response_exists selectorBox failWindow wire
  let selected := {preparedTeacher clock with pending := selectorQueue delay failure}
  have selectorFuture : ∀ d ∈ selected.pending, selected.time ≤ d.due := by
    intro d member
    cases h : failure with
    | none => simp [selected, selectorQueue, h] at member
    | some F =>
      have eq : d = ⟨0, 2, F + delay F⟩ := by simpa [selected, selectorQueue, h] using member
      rw [eq]
      change clock ≤ F + delay F
      linarith [(failWindow F h).1, (wire F).1]
  obtain ⟨wait, waitTransverse, _, waitDeliveries⟩ := rest_prefix (θ := θS) (s := selected) (origin := time)
    (by change time < time + 70; linarith) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) selectorFuture
  let traceSelector := wait.append response.execution
  have selectorComplete : CompleteThrough traceSelector (time + 96) := by
    have eq : clock + 26 = time + 96 := by dsimp [clock]; ring
    rw [← eq]
    exact response.complete
  have selectorPositive : traceSelector.ContactsTransversal :=
    (Execution.contactsTransversal_append _ _).2 ⟨waitTransverse, response.transversal⟩
  let creditQ := pairStart.pending.map Delivery.succ
  have selectBalance : HeadQueueBalance pair.execution {selected with time := time} creditQ responseRoute := by
    unfold HeadQueueBalance
    rw [pair.execution.futureHeadWires_map]
    exact congrArg (fun l : Multiset (Delivery 3) =>
      (creditQ : Multiset (Delivery 3)) + l) (Multiset.coe_eq_coe.mpr (failureQueue.map _))
  obtain ⟨whole⟩ := pair.execution.prepend_causal_result traceSelector rfl
    (pairComplete.1.trans selectorComplete.1.symm) responseRoute
    (failure_feedback_causal (fun f => by linarith [(wire f).1])) creditQ selectBalance
  have complete := whole.complete pairComplete selectorComplete
  have positive := whole.contacts_transversal pairPositive selectorPositive
  have box := prepend_box (prepend_box learnerBox inverterBox) selectorBox
  have learnerPhysical := readout_learner_physical learnerBox time (preparationTrial third) 0
  have inverterPhysical : PhysicalInvariant θI rawInv := by
    have h := lessonProbe_physical (prepared := false) (time := clock) inverterBox
    exact ⟨h.region, h.gain_cap, h.recovery_cap, h.reserve⟩
  have physical : PhysicalInvariant (prependParameters θS (prependParameters θI θL))
      (readoutFeedbackStart time third) :=
    prepend_physical
      (prepend_physical ⟨learnerPhysical.region, learnerPhysical.gain_cap, learnerPhysical.recovery_cap,
        learnerPhysical.reserve⟩ inverterPhysical _) (preparedTeacher_physical selectorBox time []) _
  have initial : InitiallyBelowReady (readoutFeedbackStart time third) := by
    intro i c h
    cases c with
    | q => fin_cases i <;> change (1 / 10 : ℝ) < 1 <;> norm_num
    | m p => fin_cases i <;> change (1 / 40 : ℝ) < 1 <;> norm_num
    | z _ => exact False.elim h
    | b => exact False.elim h
    | energy => exact False.elim h
  have learnerCount : learner.execution.deliveries.length = (preparationTrial third).cost + 1 := by
    rw [learner.deliveries]
    cases third <;> rfl
  have count : lessonReceipts whole.execution.deliveries 2 = (preparationTrial third).cost + 1 := by
    change lessonReceipts whole.execution.deliveries ((0 : Fin 1).succ.succ) = _
    rw [CausalTraceBalance.tail_receipts whole.trace, CausalTraceBalance.tail_receipts pair.trace,
      lessonReceipts]
    have eq : learner.execution.deliveries.filter (fun d => d.cell == 0) = learner.execution.deliveries :=
      List.filter_eq_self.mpr (fun d _ => by rw [Subsingleton.elim d.cell 0]; rfl)
    rw [eq, learnerCount]
  have reads : (whole.execution.emissionTimes 2).length = (if third then 1 else 0) := by
    change (whole.execution.emissionTimes ((0 : Fin 1).succ.succ)).length = _
    rw [whole.tail_emission_times, pair.tail_emission_times, Execution.emissionTimes, learner.emissions]
    cases h : learner.fire with
    | none =>
      have no : third = false := by simpa [h] using learner.reports.symm
      simp [no]
    | some F =>
      have yes : third = true := by simpa [h] using learner.reports.symm
      simp [yes]
  have feedback : lessonReceipts whole.execution.deliveries 0 = (if third then 0 else 1) := by
    rw [CausalTraceBalance.head_receipts whole.trace, Execution.deliveries_append, waitDeliveries,
      List.nil_append, response.deliveries]
    cases h : failure with
    | none =>
      have yes : third = true := by cases third <;> simp_all
      simp [selectorQueue, yes]
    | some F =>
      have no : third = false := by cases third <;> simp_all
      simp [selectorQueue, no]
  refine ⟨_, whole.execution, whole.execution.toCrossing initial box physical positive, rfl,
    complete.toCrossing whole.execution initial box physical positive, count, reads, feedback, ?_, ?_, ?_, ?_⟩
  · change response.final.x 0 (.z 2) = _
    rw [response.gains, failFlag]
    cases third <;> simp
  · change response.final.x 0 (.z 0) = _
    rw [response.gains]
    simp
  · change response.final.x 0 (.z 1) = _
    rw [response.gains]
    simp
  · intro otherFinal other done
    have causal : StrictCausalRouter (readoutFeedbackRouter time delay) :=
      prepend_routed_causal
        (prepend_routed_causal (fun _ _ _ hd => (List.not_mem_nil hd).elim) (learner_read_contacts_causal time))
        (failure_feedback_causal (fun F => by linarith [(wire F).1]))
    obtain ⟨native, same⟩ := other.execution.toNative_of_transverse_completion whole.execution causal
      box physical complete positive (le_of_eq done.1)
    have weak := done.toWeak_of_native other native same initial box physical
    exact ⟨(whole.execution.observational_unique_weak box other.execution physical complete positive weak).1.symm,
      fun i => (whole.execution.emissionTimes_unique_weak other.execution box physical complete positive weak i).symm⟩

def trialLesson (practice third : Bool) : Lesson :=
  if practice then practiceTrial third else preparationTrial third

def trialPort (practice : Bool) : Port :=
  if practice then 1 else 0

noncomputable def learnerTrialStart (time : ℝ) (practice third : Bool) : Snapshot 2 :=
  let learner := withFuture (readoutLearner time (trialLesson practice third) (trialPort practice))
    [learnerRead time (trialPort practice)]
  learner.prependQueued (preparedTeacher time) (learner.pending.map Delivery.succ)

/-- For either lesson reduction, the test pulse reads the actual learner
and its FIRE writes the corresponding credit. The unchanged block meets
its requirement in each compared trial. -/
theorem learner_readout_commits_trial {θL θC ε}
    (learnerBox : @PhysicalBox 1 θL ε) (creditBox : @PhysicalBox 1 θC ε)
    (time : ℝ) (practice third : Bool) :
    let θ := prependParameters θC θL
    let route := prependRouted (fun _ _ => []) (acceptanceContacts (trialPort practice))
    let start := learnerTrialStart time practice third
    ∃ (final : Snapshot 2) (e : Execution θ route start final)
      (crossing : CrossingExecution θ route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing (time + 96) ∧
      lessonReceipts e.deliveries 1 = (trialLesson practice third).cost + 1 ∧
      (((trialLesson practice third).train ⟨3, 3⟩).retained = true ↔
        (e.emissionTimes 1).length = 1) ∧
      ∀ p, final.x 0 (.z p) = if p = trialPort practice ∧ third then 3 / 5 else 0 := by
  let port := trialPort practice
  let lesson := trialLesson practice third
  let start := readoutLearner time lesson port
  let source := withFuture start [learnerRead time port]
  have capacity : lesson.preparation ≤ 4 ∧ lesson.practice ≤ 4 := by
    cases practice <;> cases third <;> decide
  have count : (lessonPorts lesson).count port = if third then 3 else 2 := by
    cases practice
    · exact (lessonPorts_count (preparationTrial third)).1
    · exact (lessonPorts_count (practiceTrial third)).2.1
  obtain ⟨learner⟩ := full_learner_read_exists learnerBox time lesson port third capacity count
  have window (F : ℝ) (h : learner.fire = some F) : time < F ∧ F + 8 ≤ time + 96 := by
    obtain ⟨early, late⟩ := learner.window F h
    change time + 65 < F at early
    change F < time + 65 + 1 at late
    constructor <;> linarith
  obtain ⟨credit⟩ := credit_response_exists creditBox (credit := port) (T := time + 96)
    (by linarith) window
  let receiving := (preparedTeacher time).requeue
    (learner.fire.toList.map (fun F => ⟨0, port, F + 7 / 20⟩))
  have pending : receiving.pending = learner.execution.headInputQueue (acceptanceContacts port) := by
    simp only [Execution.headInputQueue, learner.emissions, List.flatMap_map]
    cases h : learner.fire <;> simp [receiving, Snapshot.requeue, h, acceptanceContacts]
  have causal : StrictHeadRoutes (acceptanceContacts port) := by
    intro i F d hd
    obtain rfl := List.mem_singleton.mp hd
    change F < F + 7 / 20
    linarith
  obtain ⟨weave⟩ := learner.execution.prepend_causal_result credit.execution rfl
    (learner.complete.1.trans credit.complete.1.symm) (acceptanceContacts port) causal
    (source.pending.map Delivery.succ) (HeadQueueBalance.initial learner.execution receiving _ pending)
  have complete := weave.complete learner.complete credit.complete
  have positive := weave.contacts_transversal learner.transverse credit.positive
  have box := prepend_box learnerBox creditBox
  have p := readout_learner_physical learnerBox time lesson port
  have physical : PhysicalInvariant (prependParameters θC θL) (learnerTrialStart time practice third) :=
    prepend_physical ⟨p.region, p.gain_cap, p.recovery_cap, p.reserve⟩
      (preparedTeacher_physical creditBox time []) _
  have init : InitiallyBelowReady (learnerTrialStart time practice third) := by
    intro i c h
    cases c with
    | q => fin_cases i <;> change (1 / 10 : ℝ) < 1 <;> norm_num
    | m p => fin_cases i <;> change (1 / 40 : ℝ) < 1 <;> norm_num
    | z _ => exact False.elim h
    | b => exact False.elim h
    | energy => exact False.elim h
  have learnerCount : learner.execution.deliveries.length = lesson.cost + 1 := by
    rw [learner.deliveries]
    cases practice <;> cases third <;> rfl
  have delivered : lessonReceipts weave.execution.deliveries 1 = lesson.cost + 1 := by
    change lessonReceipts weave.execution.deliveries (0 : Fin 1).succ = _
    rw [CausalTraceBalance.tail_receipts weave.trace, lessonReceipts]
    have eq : learner.execution.deliveries.filter (fun d => d.cell == 0) = learner.execution.deliveries :=
      List.filter_eq_self.mpr (fun d _ => by rw [Subsingleton.elim d.cell 0]; rfl)
    rw [eq, learnerCount]
  have reports : (weave.execution.emissionTimes 1).length = if third then 1 else 0 := by
    change (weave.execution.emissionTimes (0 : Fin 1).succ).length = _
    rw [weave.tail_emission_times, Execution.emissionTimes, learner.emissions]
    cases h : learner.fire with
    | none =>
      have no : third = false := by simpa [h] using learner.reports.symm
      simp [no]
    | some F =>
      have yes : third = true := by simpa [h] using learner.reports.symm
      simp [yes]
  refine ⟨_, weave.execution, weave.execution.toCrossing init box physical positive, rfl,
    complete.toCrossing weave.execution init box physical positive, delivered, ?_, ?_⟩
  · change ((trialLesson practice third).train ⟨3, 3⟩).retained = true ↔
      (weave.execution.emissionTimes 1).length = 1
    rw [reports]
    cases practice <;> cases third <;> decide
  · intro p
    change credit.final.x 0 (.z p) = _
    rw [credit.written, learner.reports]

end RecursiveLearning.Native
