import AcceptanceDispatch

/-! Two native credit writes with an intervening one-shot selector. The
first acceptance changes the selector by a routed dose, and the resulting
selector FIRE releases the practice test. The frozen control keeps the
default preparation proposal and rejects it. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid

private noncomputable def stagedCounter (origin clock : ℝ) (third : Bool) : Snapshot 1 :=
  { acceptanceStart clock third with time := origin }

private theorem counter_queue (clock : ℝ) (third : Bool) :
    (acceptanceStart clock third).pending =
      [acceptanceProbe clock, ⟨0, 0, clock + 1 / 2⟩, ⟨0, 0, clock + 8 + 1 / 2⟩] ++
        if third then [⟨0, 0, clock + 8 + 8 + 1 / 2⟩] else [] := by
  cases third <;> rfl

private theorem counter_due {clock : ℝ} {third : Bool} {d : Delivery 1}
    (member : d ∈ (acceptanceStart clock third).pending) : clock < d.due := by
  rw [counter_queue, List.mem_append] at member
  rcases member with base | extra
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at base
    rcases base with rfl | rfl | rfl
    · change clock < clock + 25
      linarith
    · change clock < clock + 1 / 2
      linarith
    · change clock < clock + 8 + 1 / 2
      linarith
  · cases third with
    | false => simp at extra
    | true =>
      obtain rfl := List.mem_singleton.mp extra
      change clock < clock + 8 + 8 + 1 / 2
      linarith

private theorem counter_wait {θ : Fin 1 → Parameters} {origin clock : ℝ} (later : origin ≤ clock)
    (third : Bool) :
    ∃ e : Execution θ (fun _ _ => []) (stagedCounter origin clock third) (acceptanceStart clock third),
      e.ContactsTransversal ∧ e.ledger.emissions = [] := by
  rcases later.lt_or_eq with positive | rfl
  · let s := stagedCounter origin clock third
    have future : ∀ d ∈ s.pending, clock ≤ d.due := fun d hd => (counter_due hd).le
    let flow : Flow θ s (quietAt s clock) :=
      quietFlow s positive (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun i => by change (1 / 10 : ℝ) < 1; norm_num)
        (fun i p => by change (1 / 40 : ℝ) < 1; norm_num) future
    let v := acceptanceStart clock third
    have vals : (quietAt s clock).x = v.x := by
      funext i c
      cases c <;> simp [s, v, stagedCounter, quietAt, quietValues, acceptanceStart,
        acceptanceCounter, withFuture, preparedTeacher, relax]
    have eq : quietAt s clock = v := congrArg (fun x => {v with x := x}) vals
    have transport {u : Snapshot 1} (same : quietAt s clock = u) :
        ∃ e : Execution θ (fun _ _ => []) s u, e.ContactsTransversal ∧ e.ledger.emissions = [] := by
      cases same
      exact ⟨.cons (.flow flow) (.nil _), trivial, rfl⟩
    exact transport eq
  · exact ⟨.nil _, trivial, rfl⟩

private structure StagedSignal (θ : Fin 1 → Parameters) (origin clock T : ℝ) (third : Bool) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) (stagedCounter origin clock third) final
  complete : CompleteThrough execution T
  positive : execution.ContactsTransversal
  empty : final.pending = []
  fire : Option ℝ
  reports : fire.isSome = third
  window : ∀ F, fire = some F → clock + 25 < F ∧ F < clock + 26
  emissions : execution.ledger.emissions = fire.toList.map (fun F => (0, F))

private theorem staged_signal_exists {θ ε origin clock T} (box : @PhysicalBox 1 θ ε)
    (later : origin ≤ clock) (after : clock + 48 < T) (third : Bool) :
    Nonempty (StagedSignal θ origin clock T third) := by
  obtain ⟨lead, leadPositive, leadSilent⟩ := counter_wait (θ := θ) later third
  obtain ⟨signal⟩ := acceptance_signal_exists box clock third
  obtain ⟨tail, complete, positive, silent, _⟩ := quiet_ready_tail_exists (θ := θ)
    (T := T) (by rw [signal.complete.1]; exact after) signal.ready signal.rawNone signal.empty
  let execution := (lead.append signal.execution).append tail
  have fires : execution.ledger.emissions = signal.fire.toList.map (fun F => (0, F)) := by
    rw [Execution.emissions_append, Execution.emissions_append, leadSilent, signal.emissions, silent,
      List.nil_append, List.append_nil]
  exact ⟨⟨_, execution, complete,
    (Execution.contactsTransversal_append _ _).2
      ⟨(Execution.contactsTransversal_append _ _).2 ⟨leadPositive, signal.transverse⟩, positive⟩,
    signal.empty, signal.fire, signal.reports, signal.window, fires⟩⟩

private theorem StagedSignal.fire_true {θ origin clock T} (s : StagedSignal θ origin clock T true) :
    ∃ F, s.fire = some F := by
  cases h : s.fire with
  | none =>
    have reports := s.reports
    simp [h] at reports
  | some F => exact ⟨F, rfl⟩

private theorem StagedSignal.fire_false {θ origin clock T} (s : StagedSignal θ origin clock T false) :
    s.fire = none := by
  cases h : s.fire with
  | none => rfl
  | some F =>
    have reports := s.reports
    simp [h] at reports

/-- The first acceptance can supply the selector's third input. The first
two and the common readout are fixed sources. -/
noncomputable def selectorThird (time : ℝ) : Delivery 1 :=
  ⟨0, 0, time + 24 + 8 + 8 + 1 / 2⟩

noncomputable def serialSelectorContacts (time : ℝ) (adaptive : Bool) : HeadRoutes 1 :=
  fun _ F => if adaptive && decide (F < time + 27) then [selectorThird time] else []

/-- The first FIRE launches the second test with its two default inputs.
A selector FIRE adds the third input that distinguishes the practice proposal. -/
noncomputable def serialTestContacts (time : ℝ) : HeadRoutes 2 :=
  fun i F => if F < time + 51 then
    if i = 0 then [⟨0, 0, time + 60 + 8 + 8 + 1 / 2⟩]
    else (acceptanceStart (time + 60) false).pending
  else []

/-- The two tester cells write to different ports of the same credit cell.
The selector alone cannot write either credit. -/
noncomputable def serialCreditContacts : HeadRoutes 3 :=
  fun i F => if i = 2 then [⟨0, 0, F + 7 / 20⟩]
    else if i = 0 then [⟨0, 1, F + 7 / 20⟩] else []

noncomputable def serialRoute (time : ℝ) (adaptive : Bool) : Router 4 :=
  prependRouted (prependRouted
    (prependRouted (fun _ _ => []) (serialSelectorContacts time adaptive))
    (serialTestContacts time)) serialCreditContacts

/-- Initial sources feed the first tester and the selector's clock. Neither
the second test nor either credit pulse occurs in the birth queue. -/
noncomputable def serialStart (time : ℝ) : Snapshot 4 :=
  let first := stagedCounter time time true
  let selector := stagedCounter time (time + 24) false
  let paired := first.prependQueued selector (independentHeadQueue first selector)
  let tested := paired.prependQueued (stagedCounter time (time + 60) false) (paired.pending.map Delivery.succ)
  tested.prependQueued (preparedTeacher time) (tested.pending.map Delivery.succ)

abbrev serialParameters (first selector test credit : Fin 1 → Parameters) : Fin 4 → Parameters :=
  prependParameters credit (prependParameters test (prependParameters selector first))

private theorem selector_contacts_strict (time : ℝ) (adaptive : Bool) :
    StrictHeadRoutes (serialSelectorContacts time adaptive) := by
  intro i F d hd
  by_cases h : adaptive && decide (F < time + 27)
  · have same : d = selectorThird time := by simpa [serialSelectorContacts, h] using hd
    have early := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
    subst d
    change F < time + 24 + 8 + 8 + 1 / 2
    linarith
  · simp [serialSelectorContacts, h] at hd

private theorem test_contacts_strict (time : ℝ) :
    StrictHeadRoutes (serialTestContacts time) := by
  intro i F d hd
  by_cases early : F < time + 51
  · by_cases selector : i = 0
    · have equal : d = ⟨0, 0, time + 60 + 8 + 8 + 1 / 2⟩ := by
        simpa [serialTestContacts, early, selector] using hd
      subst d
      change F < time + 60 + 8 + 8 + 1 / 2
      linarith
    · have member : d ∈ (acceptanceStart (time + 60) false).pending := by
        simpa [serialTestContacts, early, selector] using hd
      linarith [counter_due member]
  · simp [serialTestContacts, early] at hd

private theorem credit_contacts_strict : StrictHeadRoutes serialCreditContacts := by
  intro i F d hd
  unfold serialCreditContacts at hd
  split at hd
  · obtain rfl := List.mem_singleton.mp hd
    change F < F + 7 / 20
    linarith
  · split at hd
    · obtain rfl := List.mem_singleton.mp hd
      change F < F + 7 / 20
      linarith
    · simp at hd

private structure SerialCreditRun (θ : Fin 1 → Parameters) (time first T : ℝ) (second : Option ℝ) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => [])
    ((preparedTeacher time).requeue (⟨0, 0, first + 7 / 20⟩ ::
      second.toList.map (fun F => ⟨0, 1, F + 7 / 20⟩))) final
  complete : CompleteThrough execution T
  positive : execution.ContactsTransversal
  empty : final.pending = []
  firstGain : final.x 0 (.z 0) = 3 / 5
  secondGain : final.x 0 (.z 1) = if second.isSome then 3 / 5 else 0

private theorem serial_credit_run_exists {θ ε time first T second} (box : @PhysicalBox 1 θ ε)
    (firstWindow : time + 25 < first ∧ first < time + 26)
    (secondWindow : ∀ F, second = some F → time + 85 < F ∧ F < time + 86)
    (horizon : time + 108 < T) :
    Nonempty (SerialCreditRun θ time first T second) := by
  let later := second.toList.map (fun F => (⟨0, 1, F + 7 / 20⟩ : Delivery 1))
  let due := first + 7 / 20
  let s := (preparedTeacher time).requeue (⟨0, 0, due⟩ :: later)
  have ready : ReadyCoordinates s 0 := ⟨rfl, by norm_num [s, Snapshot.requeue, preparedTeacher],
    fun _ => ⟨rfl, by norm_num [s, Snapshot.requeue, preparedTeacher, RestBand]⟩⟩
  have logPos : (0 : ℝ) ≤ Real.log (6 / 5) := Real.log_nonneg (by norm_num)
  have separation : ∀ d ∈ later, due + 8 ≤ d.due := by
    intro d hd
    cases h : second with
    | none => simp [later, h] at hd
    | some F =>
      have same : d = ⟨0, 1, F + 7 / 20⟩ := by simpa [later, h] using hd
      rw [same]
      change first + 7 / 20 + 8 ≤ F + 7 / 20
      linarith [firstWindow.2, (secondWindow F h).1]
  obtain ⟨dose⟩ := port_dose_exists (route := fun _ _ => []) (port := 0) (due := due)
    box (preparedTeacher_physical box time _) (by simp [RawValid, preparedTeacher])
    ready (fun _ => rfl) (by change time < first + 7 / 20; linarith [firstWindow.1]) rfl
    separation (by change Real.exp 0 ≤ _; norm_num) (by change 0 ≤ _; linarith)
  have written : dose.final.x 0 (.z 0) = 3 / 5 := by
    rw [dose.gain]
    norm_num [s, Snapshot.requeue, preparedTeacher]
  have unused : dose.final.x 0 (.z 1) = 0 := by
    rw [dose.gain]
    norm_num [s, Snapshot.requeue, preparedTeacher]
  cases second with
  | none =>
    have empty : dose.final.pending = [] := by simpa [later] using dose.pending
    obtain ⟨tail, complete, positive, _, _⟩ := quiet_ready_tail_exists (θ := θ) (T := T)
      (by rw [dose.complete.1]; dsimp [due]; linarith [firstWindow.2])
      (fun i => by rw [Subsingleton.elim i 0]; exact dose.ready)
      (fun i p => by rw [Subsingleton.elim i 0]; exact dose.rawNone p) empty
    exact ⟨⟨_, dose.execution.append tail, complete,
      (Execution.contactsTransversal_append _ _).2 ⟨dose.transversal, positive⟩, empty, written, unused⟩⟩
  | some F =>
    let d := F + 7 / 20
    have queue : dose.final.pending = [⟨0, 1, d⟩] := by simpa [later, d] using dose.pending
    have before : dose.final.time < d := by
      rw [dose.complete.1]
      dsimp [due, d]
      linarith [firstWindow.2, (secondWindow F rfl).1]
    obtain ⟨next⟩ := port_dose_exists (route := fun _ _ => []) (port := 1) (due := d)
      box dose.physical dose.rawValid dose.ready dose.rawNone before queue (by simp)
      (by rw [unused]; norm_num) (by rw [unused]; linarith)
    obtain ⟨tail, complete, positive, _, _⟩ := quiet_ready_tail_exists (θ := θ) (T := T)
      (by rw [next.complete.1]; dsimp [d]; linarith [(secondWindow F rfl).2])
      (fun i => by rw [Subsingleton.elim i 0]; exact next.ready)
      (fun i p => by rw [Subsingleton.elim i 0]; exact next.rawNone p) next.pending
    refine ⟨⟨_, (dose.execution.append next.execution).append tail, complete,
      (Execution.contactsTransversal_append _ _).2
        ⟨(Execution.contactsTransversal_append _ _).2 ⟨dose.transversal, next.transversal⟩, positive⟩,
      next.pending, ?_, ?_⟩⟩
    · change next.final.x 0 (.z 0) = _
      rw [next.gain, written]
      norm_num
    · change next.final.x 0 (.z 1) = _
      rw [next.gain, unused]
      norm_num

theorem prepend_physical {n θ θH s h} (tail : @PhysicalInvariant n θ s)
    (head : PhysicalInvariant θH h) (Q : List (Delivery (n + 1))) :
    PhysicalInvariant (prependParameters θH θ) (s.prependQueued h Q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; cases i using Fin.cases with
    | zero => exact head.region 0
    | succ j => exact tail.region j
  · intro i p; cases i using Fin.cases with
    | zero => exact head.gain_cap 0 p
    | succ j => exact tail.gain_cap j p
  · intro i; cases i using Fin.cases with
    | zero => exact head.recovery_cap 0
    | succ j => exact tail.recovery_cap j
  · intro i; cases i using Fin.cases with
    | zero => exact head.reserve 0
    | succ j => exact tail.reserve j

theorem prepend_box {n θ θH ε} (tail : @PhysicalBox n θ ε) (head : PhysicalBox θH ε) :
    PhysicalBox (prependParameters θH θ) ε := by
  refine ⟨tail.1, ?_⟩
  intro i p
  cases i using Fin.cases with
  | zero => exact head.2 0 p
  | succ j => exact tail.2 j p

private theorem serial_initial (time : ℝ) : InitiallyBelowReady (serialStart time) := by
  intro i c h
  cases c with
  | q => fin_cases i <;> change (1 / 10 : ℝ) < 1 <;> norm_num
  | m p => fin_cases i <;> change (1 / 40 : ℝ) < 1 <;> norm_num
  | z _ => exact False.elim h
  | b => exact False.elim h
  | energy => exact False.elim h

private theorem serial_physical {θF θS θP θC ε}
    (firstBox : @PhysicalBox 1 θF ε) (selectorBox : @PhysicalBox 1 θS ε)
    (testBox : @PhysicalBox 1 θP ε) (creditBox : @PhysicalBox 1 θC ε) (time : ℝ) :
    PhysicalInvariant (serialParameters θF θS θP θC) (serialStart time) := by
  have stagedPhysical {θ : Fin 1 → Parameters} (hb : PhysicalBox θ ε) (clock : ℝ) (third : Bool) :
      PhysicalInvariant θ (stagedCounter time clock third) := by
    have p := acceptance_counter_physical hb clock third
    exact ⟨p.region, p.gain_cap, p.recovery_cap, p.reserve⟩
  exact prepend_physical
    (prepend_physical (prepend_physical (stagedPhysical firstBox time true)
      (stagedPhysical selectorBox (time + 24) false) _) (stagedPhysical testBox (time + 60) false) _)
    (preparedTeacher_physical creditBox time []) _

/-- One complete upward-crossing execution contains both native commits.
The frozen intervention keeps the first credit and rejects the second test. -/
theorem native_serial_acceptance {θF θS θP θC ε}
    (firstBox : @PhysicalBox 1 θF ε) (selectorBox : @PhysicalBox 1 θS ε)
    (testBox : @PhysicalBox 1 θP ε) (creditBox : @PhysicalBox 1 θC ε)
    (time T : ℝ) (horizon : time + 108 < T) (adaptive : Bool) :
    let θ := serialParameters θF θS θP θC
    let route := serialRoute time adaptive
    let start := serialStart time
    ∃ (final : Snapshot 4) (e : Execution θ route start final)
      (crossing : CrossingExecution θ route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing T ∧
      CompleteThrough e T ∧ e.ContactsTransversal ∧ final.pending = [] ∧ final.x 0 (.z 0) = 3 / 5 ∧
      final.x 0 (.z 1) = (if adaptive then 3 / 5 else 0) ∧
      ∃ (first : ℝ) (second : Option ℝ),
        (e.emissionTimes 3) = [first] ∧ time + 25 < first ∧ first < time + 26 ∧
        (e.emissionTimes 2).length = (if adaptive then 1 else 0) ∧
        (e.emissionTimes 1) = second.toList ∧ second.isSome = adaptive ∧
        (∀ F, second = some F → time + 85 < F ∧ F < time + 86) := by
  obtain ⟨first⟩ := staged_signal_exists firstBox (origin := time) (clock := time) (T := T)
    le_rfl (by linarith) true
  obtain ⟨F, firstFire⟩ := first.fire_true
  have firstWindow := first.window F firstFire
  have firstEmissions : first.execution.ledger.emissions = [(0, F)] := by
    rw [first.emissions, firstFire]
    rfl
  obtain ⟨selector⟩ := staged_signal_exists selectorBox (origin := time) (clock := time + 24)
    (T := T) (by linarith) (by linarith) adaptive
  let firstStart := stagedCounter time time true
  let selectorStart := stagedCounter time (time + 24) false
  let selectorProofStart := stagedCounter time (time + 24) adaptive
  let Q := independentHeadQueue firstStart selectorStart
  let selectRoute := serialSelectorContacts time adaptive
  have signalQueue : first.execution.headInputQueue selectRoute =
      if adaptive then [selectorThird time] else [] := by
    have early : F < time + 27 := by linarith [firstWindow.2]
    rw [Execution.headInputQueue, firstEmissions]
    cases adaptive <;> simp [selectRoute, serialSelectorContacts, early]
  have balance : HeadQueueBalance first.execution selectorProofStart Q selectRoute := by
    unfold HeadQueueBalance
    rw [first.execution.futureHeadWires_map, signalQueue]
    change (Q : Multiset (Delivery 2)) + _ =
      (firstStart.pending.map Delivery.succ : Multiset (Delivery 2)) +
      ((selectorProofStart.pending.map (Delivery.head (n := 1))) : Multiset (Delivery 2))
    have pending : selectorProofStart.pending =
        selectorStart.pending ++ (if adaptive then [selectorThird time] else []) := by
      cases adaptive <;> simp [selectorProofStart, selectorStart, stagedCounter, counter_queue, selectorThird]
    rw [pending, List.map_append, Multiset.coe_add]
    rw [show Q = selectorStart.pending.map (Delivery.head (n := 1)) ++ firstStart.pending.map Delivery.succ from rfl,
      Multiset.coe_add]
    simpa only [← Multiset.coe_add, List.append_assoc] using
      (Multiset.coe_eq_coe.mpr ((List.perm_append_comm
        (l₁ := selectorStart.pending.map (Delivery.head (n := 1)))
        (l₂ := firstStart.pending.map Delivery.succ)).append_right
          ((if adaptive then [selectorThird time] else []).map (Delivery.head (n := 1)))))
  obtain ⟨pair⟩ := first.execution.prepend_causal_result selector.execution rfl
    (first.complete.1.trans selector.complete.1.symm) selectRoute
    (selector_contacts_strict time adaptive) Q balance
  have pairComplete := pair.complete first.complete selector.complete
  have pairPositive := pair.contacts_transversal first.positive selector.positive
  have pairEmpty := pair.pending_empty first.empty selector.empty
  have pairEvents : pair.execution.ledger.emissions.Perm
      ((1, F) :: selector.fire.toList.map (fun f => ((0 : Fin 2), f))) := by
    apply Multiset.coe_eq_coe.mp
    rw [pair.trace.emissions, firstEmissions, selector.emissions, List.map_map]
    rfl
  obtain ⟨test⟩ := staged_signal_exists testBox (origin := time) (clock := time + 60)
    (T := T) (by linarith) (by linarith) adaptive
  let secondStart := stagedCounter time (time + 60) adaptive
  let testRoute := serialTestContacts time
  have secondQueue : (pair.execution.headInputQueue testRoute).Perm secondStart.pending := by
    unfold Execution.headInputQueue
    refine (pairEvents.flatMap_right (fun event => testRoute event.1 event.2)).trans ?_
    have early : F < time + 51 := by linarith [firstWindow.2]
    cases adaptive with
    | false =>
      rw [selector.fire_false]
      simp [testRoute, serialTestContacts, early, secondStart, stagedCounter]
    | true =>
      obtain ⟨S, signal⟩ := selector.fire_true
      have earlier : S < time + 51 := by linarith [(selector.window S signal).2]
      rw [signal]
      simp [testRoute, serialTestContacts, early, earlier, secondStart, stagedCounter, counter_queue]
  let pairStart := firstStart.prependQueued selectorProofStart Q
  let secondQ := pairStart.pending.map Delivery.succ
  have testBalance : HeadQueueBalance pair.execution secondStart secondQ testRoute := by
    unfold HeadQueueBalance
    rw [pair.execution.futureHeadWires_map]
    exact congrArg (fun l : Multiset (Delivery 3) =>
      (secondQ : Multiset (Delivery 3)) + l) (Multiset.coe_eq_coe.mpr (secondQueue.map _))
  obtain ⟨tested⟩ := pair.execution.prepend_causal_result test.execution rfl
    (pairComplete.1.trans test.complete.1.symm) testRoute (test_contacts_strict time) secondQ testBalance
  have testedComplete := tested.complete pairComplete test.complete
  have testedPositive := tested.contacts_transversal pairPositive test.positive
  have testedEmpty := tested.pending_empty pairEmpty test.empty
  have testEvents : tested.execution.ledger.emissions.Perm
      ((2, F) :: (selector.fire.toList.map (fun f => ((1 : Fin 3), f)) ++
        test.fire.toList.map (fun f => ((0 : Fin 3), f)))) := by
    have compose := (pairEvents.map (fun e => (e.1.succ, e.2))).append_right
      (test.execution.ledger.emissions.map (fun e => ((0 : Fin 3), e.2)))
    have base := Multiset.coe_eq_coe.mp (tested.trace.emissions.trans (Multiset.coe_add _ _).symm)
    have composed := base.trans compose
    have mapped : test.execution.ledger.emissions.map (fun e => ((0 : Fin 3), e.2)) =
        test.fire.toList.map (fun f => ((0 : Fin 3), f)) := by
      rw [test.emissions, List.map_map]
      rfl
    have shiftFirst : (1 : Fin 2).succ = (2 : Fin 3) := by decide
    have shiftSelector : (0 : Fin 2).succ = (1 : Fin 3) := by decide
    simpa only [mapped, List.map_cons, List.map_map, List.cons_append, Function.comp_def, shiftFirst, shiftSelector] using composed
  have secondWindow (G : ℝ) (same : test.fire = some G) :
      time + 85 < G ∧ G < time + 86 := by
    obtain ⟨a, b⟩ := test.window G same
    constructor <;> linarith
  obtain ⟨credit⟩ := serial_credit_run_exists creditBox firstWindow secondWindow horizon
  let creditStart := (preparedTeacher time).requeue
    (⟨0, 0, F + 7 / 20⟩ :: test.fire.toList.map (fun f => ⟨0, 1, f + 7 / 20⟩))
  have creditQueue : (tested.execution.headInputQueue serialCreditContacts).Perm creditStart.pending := by
    unfold Execution.headInputQueue
    refine (testEvents.flatMap_right (fun event => serialCreditContacts event.1 event.2)).trans ?_
    cases hs : selector.fire <;> cases ht : test.fire <;>
      simp [serialCreditContacts, creditStart, Snapshot.requeue, ht]
  let testedStart := pairStart.prependQueued secondStart secondQ
  let creditQ := testedStart.pending.map Delivery.succ
  have creditBalance : HeadQueueBalance tested.execution creditStart creditQ serialCreditContacts := by
    unfold HeadQueueBalance
    rw [tested.execution.futureHeadWires_map]
    exact congrArg (fun l : Multiset (Delivery 4) =>
      (creditQ : Multiset (Delivery 4)) + l) (Multiset.coe_eq_coe.mpr (creditQueue.map _))
  obtain ⟨whole⟩ := tested.execution.prepend_causal_result credit.execution rfl
    (testedComplete.1.trans credit.complete.1.symm) serialCreditContacts credit_contacts_strict creditQ creditBalance
  have complete := whole.complete testedComplete credit.complete
  have positive := whole.contacts_transversal testedPositive credit.positive
  have empty := whole.pending_empty testedEmpty credit.empty
  have box : PhysicalBox (serialParameters θF θS θP θC) ε :=
    prepend_box (prepend_box (prepend_box firstBox selectorBox) testBox) creditBox
  have physical := serial_physical firstBox selectorBox testBox creditBox time
  have initial := serial_initial time
  have firstDates : whole.execution.emissionTimes 3 = [F] := by
    change whole.execution.emissionTimes (((0 : Fin 1).succ).succ).succ = [F]
    rw [whole.tail_emission_times, tested.tail_emission_times, pair.tail_emission_times,
      Execution.emissionTimes, firstEmissions]
    simp
  have selectorCount : (whole.execution.emissionTimes 2).length = (if adaptive then 1 else 0) := by
    change (whole.execution.emissionTimes ((0 : Fin 2).succ).succ).length = _
    rw [whole.tail_emission_times, tested.tail_emission_times, pair.head_emission_times,
      Execution.emissionTimes, selector.emissions]
    cases adaptive with
    | false => rw [selector.fire_false]; rfl
    | true => obtain ⟨_, h⟩ := selector.fire_true; rw [h]; rfl
  have testDates : whole.execution.emissionTimes 1 = test.fire.toList := by
    change whole.execution.emissionTimes (0 : Fin 3).succ = _
    rw [whole.tail_emission_times, tested.head_emission_times, Execution.emissionTimes, test.emissions]
    cases adaptive with
    | false => rw [test.fire_false]; rfl
    | true => obtain ⟨_, h⟩ := test.fire_true; rw [h]; rfl
  have stored : credit.final.x 0 (.z 1) = (if adaptive then 3 / 5 else 0) := by
    rw [credit.secondGain, test.reports]
  exact ⟨_, whole.execution, whole.execution.toCrossing initial box physical positive, rfl,
    complete.toCrossing whole.execution initial box physical positive, complete, positive, empty, credit.firstGain, stored,
    F, test.fire, firstDates, firstWindow.1, firstWindow.2, selectorCount, testDates, test.reports, secondWindow⟩

/-- A real FIRE on the designated cell schedules the complete deployed
lesson, at a fixed offset from that physical FIRE. -/
noncomputable def deployedLessonContacts {n} (sender : Fin n) (gap : ℝ) (lesson : Lesson) :
    HeadRoutes n := fun i F => if i = sender then lessonDeliveries (F + gap) (lessonPorts lesson) else []

private theorem deployed_contacts_strict {n} (sender : Fin n) {gap : ℝ} (positive : 0 < gap)
    (lesson : Lesson) : StrictHeadRoutes (deployedLessonContacts sender gap lesson) := by
  intro i F d hd
  by_cases h : i = sender
  · have member : d ∈ lessonDeliveries (F + gap) (lessonPorts lesson) := by
      simpa [deployedLessonContacts, h] using hd
    linarith [lesson_delivery_time member]
  · simp [deployedLessonContacts, h] at hd

private theorem deployed_input_queue {n θ route s u} (e : @Execution n θ route s u)
    (sender : Fin n) (gap : ℝ) (lesson : Lesson) :
    e.headInputQueue (deployedLessonContacts sender gap lesson) =
      (e.emissionTimes sender).flatMap (fun F => lessonDeliveries (F + gap) (lessonPorts lesson)) := by
  unfold Execution.headInputQueue Execution.emissionTimes
  induction e.ledger.emissions with
  | nil => rfl
  | cons event events ih =>
    simp only [deployedLessonContacts] at ih
    by_cases h : event.1 = sender <;>
      simp [deployedLessonContacts, h, ih]

private noncomputable def addEmptyLearner {n} (s : Snapshot n) : Snapshot (n + 1) :=
  s.prependQueued (nativeLessonStart s.time ⟨0, 0⟩) (s.pending.map Delivery.succ)

private structure DeployedLesson {n θ route s u} (e : @Execution n θ route s u)
    (θL : Fin 1 → Parameters) (sender : Fin n) (gap T : ℝ) (proposal taught : Lesson) where
  final : Snapshot (n + 1)
  execution : Execution (prependParameters θL θ)
    (prependRouted route (deployedLessonContacts sender gap proposal)) (addEmptyLearner s) final
  complete : CompleteThrough execution T
  positive : execution.ContactsTransversal
  count : lessonReceipts execution.deliveries 0 = taught.cost
  retention : ∀ needs, NativeRetains final 0 needs ↔ (taught.train needs).retained = true
  previousValues : ∀ i, final.x i.succ = u.x i
  previousTimes : ∀ i, execution.emissionTimes i.succ = e.emissionTimes i
  previousReceipts : ∀ i, lessonReceipts execution.deliveries i.succ = lessonReceipts e.deliveries i

private theorem deployed_lesson_exists {n θ θL ε route s u T gap}
    (e : @Execution n θ route s u) (box : PhysicalBox θL ε)
    (complete : CompleteThrough e T) (positive : e.ContactsTransversal)
    (sender : Fin n) (delay : 0 < gap) (proposal : Lesson) (fire : Option ℝ)
    (source : e.emissionTimes sender = fire.toList)
    (capacity : proposal.preparation ≤ 4 ∧ proposal.practice ≤ 4)
    (after : s.time + 1 < T)
    (window : ∀ F, fire = some F → s.time < F + gap ∧ F + gap + 8 * proposal.cost < T) :
    Nonempty (DeployedLesson e θL sender gap T proposal (if fire.isSome then proposal else ⟨0, 0⟩)) := by
  let taught : Lesson := if fire.isSome then proposal else ⟨0, 0⟩
  let clock : ℝ := fire.elim (s.time + 1) (fun F => F + gap)
  have start : s.time < clock := by
    cases fire with
    | none => change s.time < s.time + 1; linarith
    | some F => exact (window F rfl).1
  have finish : clock + 8 * taught.cost < T := by
    cases fire with
    | none => simpa [clock, taught, Lesson.cost] using after
    | some F => exact (window F rfl).2
  have bounded : taught.preparation ≤ 4 ∧ taught.practice ≤ 4 := by
    cases fire with
    | none => norm_num [taught]
    | some F => exact capacity
  obtain ⟨run⟩ := native_lesson_exists box clock taught bounded.1 bounded.2
  obtain ⟨endLesson, endComplete, endPositive, count, _, retention⟩ := run.finish_at finish
  obtain ⟨wait, waitPositive, _, waitDeliveries⟩ := native_lesson_wait (θ := θL) start taught
  let learner := wait.append endLesson
  have learnerCount : learner.deliveries.length = taught.cost := by
    rw [Execution.deliveries_append, waitDeliveries, List.nil_append, count]
  let proofStart := {nativeLessonStart clock taught with time := s.time}
  have queue : proofStart.pending = e.headInputQueue (deployedLessonContacts sender gap proposal) := by
    rw [deployed_input_queue, source]
    cases fire <;> simp [proofStart, clock, taught, nativeLessonStart, lessonPorts, lessonDeliveries]
  have balance := HeadQueueBalance.initial e proofStart (deployedLessonContacts sender gap proposal) queue
  obtain ⟨weave⟩ := e.prepend_causal_result learner rfl (complete.1.trans endComplete.1.symm)
    (deployedLessonContacts sender gap proposal) (deployed_contacts_strict sender delay proposal) _ balance
  have done := weave.complete complete endComplete
  have transverse := weave.contacts_transversal positive
    ((Execution.contactsTransversal_append _ _).2 ⟨waitPositive, endPositive⟩)
  have received := (CausalTraceBalance.head_receipts weave.trace).trans learnerCount
  exact ⟨⟨_, weave.execution, done, transverse, received, retention,
    fun _ => rfl, weave.tail_emission_times, CausalTraceBalance.tail_receipts weave.trace⟩⟩

/-- Network indices are baseline 0, six-pulse learner 1, seven-pulse learner 2,
credits 3, second tester 4, selector 5 and first tester 6. -/
noncomputable def nativeImprovementStart (time : ℝ) : Snapshot 7 :=
  let s := addEmptyLearner (addEmptyLearner (serialStart time))
  let baseline := nativeLessonStart time ⟨4, 4⟩
  s.prependQueued baseline (independentHeadQueue s baseline)

noncomputable def nativeImprovementRoute (time : ℝ) (adaptive : Bool) : Router 7 :=
  let first := prependRouted (serialRoute time adaptive) (deployedLessonContacts 3 45 ⟨3, 4⟩)
  let second := prependRouted first (deployedLessonContacts 2 50 ⟨3, 3⟩)
  prependRouted second (fun _ _ => [])

abbrev nativeImprovementParameters (first selector test credit seven six eight : Fin 1 → Parameters) :
    Fin 7 → Parameters :=
  prependParameters eight (prependParameters six (prependParameters seven (serialParameters first selector test credit)))

theorem prepend_routed_causal {n} {route : Router n} {contacts : HeadRoutes n}
    (tail : StrictCausalRouter route) (head : StrictHeadRoutes contacts) :
    StrictCausalRouter (prependRouted route contacts) := by
  intro i t d member
  cases i using Fin.cases with
  | zero => exact False.elim (List.not_mem_nil member)
  | succ i =>
    change d ∈ (route i t).map Delivery.succ ++ (contacts i t).map Delivery.head at member
    rcases List.mem_append.mp member with source | wire
    · obtain ⟨token, seen, rfl⟩ := List.mem_map.mp source
      exact tail i t token seen
    · obtain ⟨token, seen, rfl⟩ := List.mem_map.mp wire
      exact head i t token seen

theorem native_improvement_route_causal (time : ℝ) (adaptive : Bool) :
    StrictCausalRouter (nativeImprovementRoute time adaptive) := by
  have empty {n : ℕ} : StrictCausalRouter (fun (_ : Fin n) (_ : ℝ) => []) :=
    fun _ _ _ member => False.elim (List.not_mem_nil member)
  have serial := prepend_routed_causal
    (prepend_routed_causal (prepend_routed_causal empty (selector_contacts_strict time adaptive))
      (test_contacts_strict time)) credit_contacts_strict
  exact prepend_routed_causal
    (prepend_routed_causal
      (prepend_routed_causal serial (deployed_contacts_strict 3 (by norm_num : (0 : ℝ) < 45) ⟨3, 4⟩))
      (deployed_contacts_strict 2 (by norm_num : (0 : ℝ) < 50) ⟨3, 3⟩))
    (fun _ _ _ member => False.elim (List.not_mem_nil member))

private theorem same_complete_deliveries {n θ ε route s u v T}
    (e : @Execution n θ route s u) (f : Execution θ route s v)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (complete : CompleteThrough e T) (other : CompleteThrough f T) :
    f.deliveries.Perm e.deliveries := by
  obtain ⟨states, spikes⟩ := f.observational_unique e box physical other complete
  have queues := Multiset.coe_eq_coe.mpr states.pending
  have issued := Multiset.coe_eq_coe.mpr
    (spikes.flatMap_right (fun event => route event.1 event.2))
  have balanced := f.token_balance.trans
    ((congrArg (fun m : Multiset (Delivery n) => (s.pending : Multiset (Delivery n)) + m) issued).trans
      e.token_balance.symm)
  apply Multiset.coe_eq_coe.mp
  exact add_left_cancel (by simpa only [queues] using balanced)

/-- The finite experiment deploys eight baseline pulses, then seven and
six pulses issued by actual acceptance events. The selector enables the
second commit; freezing its update leaves the first commit intact. -/
theorem native_eight_seven_six {θF θS θP θC θ7 θ6 θ8 ε}
    (firstBox : @PhysicalBox 1 θF ε) (selectorBox : @PhysicalBox 1 θS ε)
    (testBox : @PhysicalBox 1 θP ε) (creditBox : @PhysicalBox 1 θC ε)
    (sevenBox : @PhysicalBox 1 θ7 ε) (sixBox : @PhysicalBox 1 θ6 ε) (eightBox : @PhysicalBox 1 θ8 ε)
    (time : ℝ) (adaptive : Bool) :
    let θ := nativeImprovementParameters θF θS θP θC θ7 θ6 θ8
    let route := nativeImprovementRoute time adaptive
    let start := nativeImprovementStart time
    ∃ (final : Snapshot 7) (e : Execution θ route start final)
      (crossing : CrossingExecution θ route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing (time + 200) ∧
      lessonReceipts e.deliveries 0 = 8 ∧ lessonReceipts e.deliveries 2 = 7 ∧
      lessonReceipts e.deliveries 1 = (if adaptive then 6 else 0) ∧
      NativeRetains final 0 ⟨3, 3⟩ ∧ NativeRetains final 2 ⟨3, 3⟩ ∧
      (NativeRetains final 1 ⟨3, 3⟩ ↔ adaptive = true) ∧
      final.x 3 (.z 0) = 3 / 5 ∧ final.x 3 (.z 1) = (if adaptive then 3 / 5 else 0) ∧
      (∀ (otherFinal : Snapshot 7) (other : Execution θ route start otherFinal),
        CompleteThrough other (time + 200) → other.deliveries.Perm e.deliveries) ∧
      ∀ (otherFinal : Snapshot 7) (other : CrossingExecution θ route start otherFinal),
        CrossingCompleteThrough other (time + 200) →
        otherFinal.ObservationalEq final ∧
        ∀ i, other.execution.emissionTimes i = e.emissionTimes i := by
  let T := time + 200
  obtain ⟨_, core, _, _, _, complete, positive, _, credit0, credit1, F, G,
    firstDates, fEarly, fLate, _, secondDates, secondFlag, secondWindow⟩ :=
    native_serial_acceptance firstBox selectorBox testBox creditBox time T (by dsimp [T]; linarith) adaptive
  have clock : (serialStart time).time = time := rfl
  have window7 (t : ℝ) (fire : some F = some t) :
      (serialStart time).time < t + 45 ∧ t + 45 + 8 * ((⟨3, 4⟩ : Lesson).cost : ℝ) < T := by
    obtain rfl := Option.some.inj fire
    rw [clock]
    norm_num [Lesson.cost, T]
    constructor <;> linarith
  obtain ⟨seven⟩ := deployed_lesson_exists core sevenBox complete positive (3 : Fin 4)
    (gap := 45) (by norm_num) ⟨3, 4⟩ (some F) firstDates (by decide)
    (by rw [clock]; dsimp [T]; linarith) window7
  have secondDates' : seven.execution.emissionTimes (2 : Fin 5) = G.toList := by
    change seven.execution.emissionTimes (1 : Fin 4).succ = _
    rw [seven.previousTimes, secondDates]
  have window6 (t : ℝ) (fire : G = some t) :
      (addEmptyLearner (serialStart time)).time < t + 50 ∧
        t + 50 + 8 * ((⟨3, 3⟩ : Lesson).cost : ℝ) < T := by
    obtain ⟨early, late⟩ := secondWindow t fire
    change time < t + 50 ∧ _
    norm_num [Lesson.cost, T]
    constructor <;> linarith
  obtain ⟨six⟩ := deployed_lesson_exists seven.execution sixBox seven.complete seven.positive (2 : Fin 5)
    (gap := 50) (by norm_num) ⟨3, 3⟩ G secondDates' (by decide)
    (by change time + 1 < T; dsimp [T]; linarith) window6
  obtain ⟨baseline⟩ := native_lesson_exists eightBox time ⟨4, 4⟩ (by decide) (by decide)
  obtain ⟨base, baseDone, basePositive, baseCount, _, baseRetains⟩ := baseline.finish_at
    (T := T) (by norm_num [T, Lesson.cost])
  obtain ⟨whole, done⟩ := six.execution.prepend_independent_complete base rfl six.complete baseDone
  have trans := whole.contacts_transversal six.positive basePositive
  have box := prepend_box
    (prepend_box (prepend_box (prepend_box
      (prepend_box (prepend_box firstBox selectorBox) testBox) creditBox) sevenBox) sixBox) eightBox
  have ps := serial_physical firstBox selectorBox testBox creditBox time
  have p7 : PhysicalInvariant (prependParameters θ7 (serialParameters θF θS θP θC))
      (addEmptyLearner (serialStart time)) :=
    prepend_physical ps (native_lesson_physical sevenBox time ⟨0, 0⟩) _
  have p6 : PhysicalInvariant (prependParameters θ6 (prependParameters θ7 (serialParameters θF θS θP θC)))
      (addEmptyLearner (addEmptyLearner (serialStart time))) :=
    prepend_physical p7 (native_lesson_physical sixBox time ⟨0, 0⟩) _
  have physical : PhysicalInvariant (nativeImprovementParameters θF θS θP θC θ7 θ6 θ8)
      (nativeImprovementStart time) :=
    prepend_physical p6 (native_lesson_physical eightBox time ⟨4, 4⟩) _
  have initial : InitiallyBelowReady (nativeImprovementStart time) := by
    intro i c h
    cases c with
    | q => fin_cases i <;> change (1 / 10 : ℝ) < 1 <;> norm_num
    | m p => fin_cases i <;> change (1 / 40 : ℝ) < 1 <;> norm_num
    | z _ => exact False.elim h
    | b => exact False.elim h
    | energy => exact False.elim h
  have count7 : lessonReceipts whole.execution.deliveries 2 = 7 := by
    change lessonReceipts whole.execution.deliveries ((0 : Fin 5).succ.succ) = _
    rw [CausalTraceBalance.tail_receipts whole.trace, six.previousReceipts]
    exact seven.count
  have count6 : lessonReceipts whole.execution.deliveries 1 = (if adaptive then 6 else 0) := by
    change lessonReceipts whole.execution.deliveries (0 : Fin 6).succ = _
    rw [CausalTraceBalance.tail_receipts whole.trace, six.count, secondFlag]
    cases adaptive <;> rfl
  refine ⟨_, whole.execution, whole.execution.toCrossing initial box physical trans, rfl,
    done.toCrossing whole.execution initial box physical trans,
    (CausalTraceBalance.head_receipts whole.trace).trans baseCount, count7, count6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (baseRetains ⟨3, 3⟩).mpr (by decide)
  · change NativeRetains six.final (0 : Fin 5).succ ⟨3, 3⟩
    unfold NativeRetains
    rw [six.previousValues]
    exact (seven.retention ⟨3, 3⟩).mpr (by change ((⟨3, 4⟩ : Lesson).train ⟨3, 3⟩).retained = true; decide)
  · change NativeRetains six.final 0 ⟨3, 3⟩ ↔ adaptive = true
    rw [six.retention, secondFlag]
    cases adaptive <;> decide
  · change six.final.x ((0 : Fin 4).succ.succ) (.z 0) = _
    rw [six.previousValues, seven.previousValues]
    exact credit0
  · change six.final.x ((0 : Fin 4).succ.succ) (.z 1) = _
    rw [six.previousValues, seven.previousValues]
    exact credit1
  · intro otherFinal other completeOther
    exact same_complete_deliveries whole.execution other box physical done completeOther
  · intro otherFinal other completeOther
    have causal := native_improvement_route_causal time adaptive
    obtain ⟨native, agrees⟩ := other.execution.toNative_of_transverse_completion whole.execution
      causal box physical done trans (le_of_eq completeOther.1)
    have weak := completeOther.toWeak_of_native other native agrees initial box physical
    exact ⟨(whole.execution.observational_unique_weak box other.execution physical done trans weak).1.symm,
      fun i => (whole.execution.emissionTimes_unique_weak other.execution box physical done trans weak i).symm⟩

end RecursiveLearning.Native
