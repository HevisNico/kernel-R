import TeacherCappedCycle
import KernelR.HybridCausalHeadComplete
import KernelR.HybridContactTransversalityCuts
import KernelR.HybridPrefixBeforeFlow

/-! A prepared controller dispatches a lesson to a separate receiver.
The absolute-time decoder uses a calibrated ignition reference. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- The midpoint of the certified gap between the high and low windows. -/
noncomputable def cappedReadCutoff : ℝ := 99 / 400

theorem capped_read_decode {θ s high} (read : SelectorReadRun θ s high) {reference : ℝ}
    (clock : |s.time - reference| ≤ 21 / 400) :
    s.time + read.latency < reference + cappedReadCutoff ↔ high = true := by
  rw [abs_le] at clock
  cases high
  · have late : 3 / 10 < read.latency := read.window.1
    simp only [Bool.false_eq_true, iff_false, not_lt, cappedReadCutoff]
    linarith [clock.1]
  · have early : read.latency < 39 / 200 := read.window.2
    simp only [iff_true, cappedReadCutoff]
    linarith [clock.2]

/-- The output wire is selected before propagation. Its delay affects the
delivery date, while the decoder itself sees the controller's FIRE date. -/
noncomputable def cappedDispatchWire (reference : ℝ) (wireDelay : ℝ → ℝ) (fire : ℝ) : Delivery 1 :=
  ⟨0, if fire < reference + cappedReadCutoff then 1 else 0, fire + wireDelay fire⟩

noncomputable def cappedDispatchContacts (origin reference : ℝ) (wireDelay : ℝ → ℝ) :
    HeadRoutes 1 :=
  fun _ fire => if fire < origin + 1 then [] else [cappedDispatchWire reference wireDelay fire]

/-- The read's reference is fixed before running the router. The scalar
ignition equation depends on the prepared charge and ignition gain. -/
theorem CappedTeacherCycle.ignition_eq {θ s delay high ref}
    (run : CappedTeacherCycle θ s delay high)
    (q : s.x 0 .q ≤ 7 / 50) (gain : 9 / 5 ≤ Real.exp (s.x 0 (.z 1)))
    (window : ref ∈ Icc s.time (s.time + 9 / 10))
    (root : readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z 1))) s.time ref = 1) :
    run.ignition = ref :=
  readyPulse_root_unique q gain ⟨by linarith [run.ignitionWindow.1], run.ignitionWindow.2.le⟩
    window run.ignitionRoot root

private theorem dispatch_contacts_causal {origin reference wireDelay}
    (wire : ∀ F, 0 < wireDelay F) : StrictHeadRoutes (cappedDispatchContacts origin reference wireDelay) := by
  intro i F d hd
  unfold cappedDispatchContacts at hd
  split at hd
  · simp at hd
  · obtain rfl := List.mem_singleton.mp hd
    change F < F + wireDelay F
    linarith [wire F]

private structure CappedDispatchCut {θ s delay high} (run : CappedTeacherCycle θ s delay high)
    (H : ℝ) where
  state : Snapshot 1
  execution : Execution θ (cappedCycleRouter s.time delay) s state
  complete : CompleteThrough execution H
  transverse : execution.ContactsTransversal
  emissions : execution.ledger.emissions = [(0, run.ignition), (0, run.read.admitted.time + run.read.read.latency)]
  gain : state.x 0 (.z 2) = s.x 0 (.z 2)
  recovery : state.x 0 .b = 11 / 10

/-- A delivery can occur on either side of sensor return. After that return
and before FAST ends, the controller continues with no raw pulse. -/
private theorem capped_dispatch_cut_exists {θ ε s delay high H} (run : CappedTeacherCycle θ s delay high)
    (box : PhysicalBox θ ε) (recovery : s.x 0 .b = 11 / 10)
    (afterIgnition : s.time + 1 ≤ run.read.admitted.time + run.read.read.latency)
    (afterRead : run.read.admitted.time + run.read.read.latency < H)
    (beforeFastEnd : H < run.read.admitted.time + run.read.read.latency + 1) :
    Nonempty (CappedDispatchCut run H) := by
  let F := run.read.admitted.time + run.read.read.latency
  have fullFires : run.execution.ledger.emissions = [(0, run.ignition), (0, F)] := by
    rw [run.emissions, ← run.readDate]
  rcases lt_trichotomy H run.read.read.horizon with before | atEnd | after
  · obtain ⟨cut⟩ := run.execution.before_flow_cut_exists H (by linarith) (by rw [run.complete.1]; exact before)
    have restSilent : cut.rest.ledger.emissions = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro event member
      have here := (cut.rest.emission_time_bounds event member).1
      have next := cut.flow.positive
      rw [cut.date] at next
      have inFull := List.mem_append_right cut.cut.ledger.emissions member
      rw [← cut.emissions, fullFires] at inFull
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inFull
      rcases inFull with rfl | rfl <;> simp only at here <;> linarith [run.ignitionWindow.2]
    have cutFires : cut.cut.ledger.emissions = [(0, run.ignition), (0, F)] := by
      simpa only [restSilent, List.append_nil] using cut.emissions.symm.trans fullFires
    exact ⟨⟨cut.state, cut.cut, cut.complete, cut.isPrefix.contacts_transversal run.transverse,
      cutFires, cut.isPrefix.gain_eq_of_final box 0 2 (run.gains 2),
      (cut.isPrefix.recovery_eq_of_final box 0 (run.recovery.trans recovery.symm)).trans recovery⟩⟩
  · subst H
    exact ⟨⟨_, run.execution, run.complete, run.transverse, fullFires, run.gains 2, run.recovery⟩⟩
  · let v := run.read.read.final
    let u := protectedMainEnd θ v 0 2 .fast .ready none H
    have later : v.time < H := run.complete.1.trans_lt after
    have stillFast : run.read.read.horizon < F + 1 := after.trans beforeFastEnd
    have mode : v.main 0 = .fast := by
      rw [run.read.read.mainClock, ite_eq_left stillFast]
    have charge : v.x 0 .q = Real.exp (-a * (v.time - F)) := by
      rw [run.read.read.chargeClock, run.complete.1]
      exact ite_eq_left stillFast
    have aux (i : Fin 1) (p : Port) : v.aux i p = .ready := by
      rw [Subsingleton.elim i 0]; exact run.read.read.auxiliaryReady p
    have raw (i : Fin 1) (p : Port) : v.raw i p = none := by
      rw [Subsingleton.elim i 0]; exact run.read.read.rawNone p
    have auxBelow (i : Fin 1) (p : Port) : v.x i (.m p) < 1 := by
      rw [Subsingleton.elim i 0]; exact run.read.read.auxiliaryBelow p
    have mainGuard (t : ℝ) (ht : t < F + 1) :
        (1 / 4 : ℝ) < v.x 0 .q * Real.exp (-a * (t - v.time)) := by
      rw [charge, ← Real.exp_add, ← exp_neg_a]
      apply Real.exp_lt_exp.mpr
      nlinarith [a_coarse_bounds.1]
    have auxGuard (p : Port) (t : ℝ) (ht : v.time ≤ t) :
        relax (1 / 2) (1 / 40) (v.x 0 (.m p)) v.time t < 1 :=
      relax_lt (by norm_num) ht (auxBelow 0 p) (by norm_num)
    let flow : Flow θ v u :=
      protectedMainFlow v 0 2 .fast .ready none later (Or.inl rfl) (Or.inl rfl)
        mode (fun i h => (h (Subsingleton.elim i 0)).elim)
        (aux 0 2) (fun i p _ => aux i p) (raw 0 2) (fun i p _ => raw i p)
        (by intro o h; contradiction) (fun i h => (h (Subsingleton.elim i 0)).elim)
        (fun i p _ => auxBelow i p)
        (fun t ht => by simpa [protectedMainRate] using mainGuard t (ht.2.trans beforeFastEnd))
        (fun t ht => by
          simp only [ite_true, rawInputScale, mul_zero, auxPulse_zero_eq_relax]
          exact auxGuard 2 t ht.1)
        (by change ∀ d ∈ run.read.read.final.pending, H ≤ d.due; simp [run.read.read.empty])
    have guards : BeforeGuards u u.x := by
      constructor
      · intro i
        rw [Subsingleton.elim i 0]
        change (match v.main 0 with
          | .ready => u.x 0 .q < 1
          | .fast => 1 / 4 < u.x 0 .q
          | .slow => 1 / 10 < u.x 0 .q)
        rw [mode]
        simpa [u, protectedMainEnd, protectedMainValues, protectedMainRate] using mainGuard H beforeFastEnd
      · intro i p
        rw [Subsingleton.elim i 0]
        change (match v.aux 0 p with
          | .ready => u.x 0 (.m p) < 1
          | .mark => 4 / 5 < u.x 0 (.m p)
          | .silent => 1 / 10 < u.x 0 (.m p)
          | .error => 1 / 40 < u.x 0 (.m p))
        rw [aux]
        by_cases eq : p = 2
        · subst p
          simpa [u, protectedMainEnd, protectedMainValues, rawInputScale, auxPulse_zero_eq_relax] using auxGuard 2 H later.le
        · simpa [u, protectedMainEnd, protectedMainValues, eq] using auxGuard p H later.le
    have pending : ∀ d ∈ u.pending, u.time < d.due := by
      change ∀ d ∈ run.read.read.final.pending, H < d.due
      simp [run.read.read.empty]
    have done : ∀ w, IsEmpty (Jump (cappedCycleRouter s.time delay) u w) :=
      guards.no_jump (by intro i p o h; change v.raw i p = some o at h; rw [raw] at h; contradiction) pending
    let tail : Execution θ (cappedCycleRouter s.time delay) v u := .cons (.flow flow) (.nil _)
    refine ⟨⟨u, run.execution.append tail, ⟨rfl, done, pending⟩,
      (Execution.contactsTransversal_append _ _).2 ⟨run.transverse, trivial⟩, ?_, run.gains 2, run.recovery⟩⟩
    rw [Execution.emissions_append, fullFires]
    rfl

/-- The operational start has no lesson token. The receiver's proof queue is
erased by the causal product, and the controller's real read FIRE creates
the token that reaches the selected receiver port. -/
theorem capped_dispatch_arrives {θ θL ε s learner delay high σ ignitionRef wireDelay}
    (run : CappedTeacherCycle θ s delay high)
    (controllerBox : PhysicalBox θ ε) (learnerBox : PhysicalBox θL ε)
    (controllerPhysical : PhysicalInvariant θ s) (learnerPhysical : PhysicalInvariant θL learner)
    (controllerReady : ReadyCoordinates s 0) (controllerRecovery : s.x 0 .b = 11 / 10)
    (learnerReady : ∀ i, ReadyCoordinates learner i)
    (learnerRaw : ∀ i p, learner.raw i p = none)
    (startClock : s.time = learner.time) (empty : s.pending = [])
    (ignitionGain : 9 / 5 ≤ Real.exp (s.x 0 (.z 1)))
    (ignitionWindow : ignitionRef ∈ Icc s.time (s.time + 9 / 10))
    (ignitionRoot : readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z 1))) s.time ignitionRef = 1)
    (budget : σ ≤ cappedTeacherWorkJitter)
    (localWire : ∀ F, delay F ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ))
    (outputWire : ∀ F, wireDelay F ∈ Icc (3 / 10) (2 / 5)) :
    let reference := ignitionRef + cappedTeacherWorkOffset + 7 / 5
    let contacts := cappedDispatchContacts s.time reference wireDelay
    let route := prependRouted (cappedCycleRouter s.time delay) contacts
    let start := s.prependQueued learner []
    let F := run.read.admitted.time + run.read.read.latency
    let H := F + wireDelay F
    let port : Port := if high then 1 else 0
    ∃ (final : Snapshot 2) (e : Execution (prependParameters θL θ) route start final)
      (crossing : CrossingExecution (prependParameters θL θ) route start final),
      CompleteThrough e H ∧ CrossingCompleteThrough crossing H ∧ crossing.execution = e.toWeak ∧
        ⟨0, port, H⟩ ∈ e.deliveries ∧ final.raw 0 port = some H ∧
        final.x 1 (.z 2) = s.x 0 (.z 2) ∧ final.x 1 .b = 11 / 10 := by
  let reference := ignitionRef + cappedTeacherWorkOffset + 7 / 5
  let contacts := cappedDispatchContacts s.time reference wireDelay
  let F := run.read.admitted.time + run.read.read.latency
  let H := F + wireDelay F
  let port : Port := if high then 1 else 0
  let token : Delivery 1 := ⟨0, port, H⟩
  have ignition := run.ignition_eq controllerReady.charge.2 ignitionGain ignitionWindow ignitionRoot
  have startRead : run.read.admitted.time = run.ignition + delay run.ignition + 7 / 5 := run.readDate
  have localBudget := localWire run.ignition
  have clock : |run.read.admitted.time - reference| ≤ 21 / 400 := by
    rw [abs_le, startRead, ignition]
    have bounds := localWire ignitionRef
    norm_num [cappedTeacherWorkJitter] at budget
    dsimp [reference]
    constructor <;> linarith [bounds.1, bounds.2]
  have decide := capped_read_decode run.read.read clock
  have window : 0 < run.read.read.latency ∧ run.read.read.latency < 4 / 5 := by
    have hw := run.read.read.window
    cases high <;> simp at hw <;> constructor <;> linarith [hw.1, hw.2]
  have afterIgnition : s.time + 1 ≤ F := by
    dsimp only [F]
    rw [startRead]
    linarith [run.ignitionWindow.1, cycle_delay_gt_one budget localBudget, window.1]
  have arrivalLater : F < H := by dsimp only [H]; linarith [(outputWire F).1]
  have beforeFastEnd : H < F + 1 := by
    dsimp [H]
    linarith [(outputWire F).2]
  have readRoute : contacts 0 F = [token] := by
    unfold contacts cappedDispatchContacts
    rw [ite_eq_right (not_lt.mpr afterIgnition)]
    change [⟨0, if F < reference + cappedReadCutoff then 1 else 0, H⟩] = [token]
    cases high with
    | false =>
      have late : ¬ F < reference + cappedReadCutoff := fun h => Bool.noConfusion (decide.mp h)
      simp [late, token, port]
    | true =>
      have early : F < reference + cappedReadCutoff := decide.mpr rfl
      simp [early, token, port]
  have ignitionRoute : contacts 0 run.ignition = [] := by
    simp [contacts, cappedDispatchContacts, show run.ignition < s.time + 1 by linarith [run.ignitionWindow.2]]
  obtain ⟨cut⟩ := capped_dispatch_cut_exists run controllerBox controllerRecovery
    afterIgnition arrivalLater beforeFastEnd
  let receiving := learner.requeue [token]
  have receiverPhysical : PhysicalInvariant θL receiving :=
    ⟨learnerPhysical.region, learnerPhysical.gain_cap, learnerPhysical.recovery_cap, learnerPhysical.reserve⟩
  have receiverReady (i : Fin 1) : ReadyCoordinates receiving i :=
    ⟨(learnerReady i).ready, (learnerReady i).charge, (learnerReady i).auxiliary⟩
  have receiverValid : RawValid receiving := by
    intro i p o h
    change learner.raw i p = some o at h
    rw [learnerRaw i p] at h
    contradiction
  obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := fun _ _ => []) learnerBox receiving token []
    receiverPhysical receiverValid receiverReady learnerRaw (by change learner.time < H; rw [← startClock]; linarith) rfl (by simp)
  have receivingQueue : receiving.pending = cut.execution.headInputQueue contacts := by
    simp [receiving, Snapshot.requeue, Execution.headInputQueue, cut.emissions, ignitionRoute]
    exact readRoute.symm
  have balance : HeadQueueBalance cut.execution receiving [] contacts := by
    simpa [empty] using HeadQueueBalance.initial cut.execution receiving contacts receivingQueue
  have finishClock := cut.complete.1.trans arrival.date.symm
  obtain ⟨weave⟩ := cut.execution.prepend_causal_result arrival.execution startClock finishClock contacts
    (dispatch_contacts_causal (fun fire => by linarith [(outputWire fire).1])) [] balance
  have readyInitial : InitiallyBelowReady (s.prependQueued learner []) := by
    intro i c h
    fin_cases i
    · cases c with
      | q => exact lt_of_le_of_lt (learnerReady 0).charge.2 (by norm_num)
      | m p => exact lt_of_le_of_lt ((learnerReady 0).auxiliary p).2.2 (by norm_num)
      | z _ => exact False.elim h
      | b => exact False.elim h
      | energy => exact False.elim h
    · cases c with
      | q => exact lt_of_le_of_lt controllerReady.charge.2 (by norm_num)
      | m p => exact lt_of_le_of_lt (controllerReady.auxiliary p).2.2 (by norm_num)
      | z _ => exact False.elim h
      | b => exact False.elim h
      | energy => exact False.elim h
  have box : PhysicalBox (prependParameters θL θ) ε := by
    refine ⟨controllerBox.1, ?_⟩
    intro i p
    fin_cases i
    · exact learnerBox.2 0 p
    · exact controllerBox.2 0 p
  have physical : PhysicalInvariant (prependParameters θL θ) (s.prependQueued learner []) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i
      · exact learnerPhysical.region 0
      · exact controllerPhysical.region 0
    · intro i p; fin_cases i
      · exact learnerPhysical.gain_cap 0 p
      · exact controllerPhysical.gain_cap 0 p
    · intro i; fin_cases i
      · exact learnerPhysical.recovery_cap 0
      · exact controllerPhysical.recovery_cap 0
    · intro i; fin_cases i
      · exact learnerPhysical.reserve 0
      · exact controllerPhysical.reserve 0
  have complete := weave.complete cut.complete (arrival.complete (by simp))
  have positive := weave.contacts_transversal cut.transverse
    arrival.contacts_transversal
  refine ⟨_, weave.execution, weave.execution.toCrossing readyInitial box physical positive, complete,
    complete.toCrossing weave.execution readyInitial box physical positive, rfl, ?_, ?_, cut.gain, cut.recovery⟩
  · change Delivery.head (n := 1) token ∈ (weave.execution.deliveries : Multiset (Delivery 2))
    rw [weave.trace.deliveries, arrival.deliveries]
    exact Multiset.mem_add.mpr (Or.inr (by simp))
  · change arrival.final.raw 0 port = some H
    exact arrival.raw_active.trans (congrArg some arrival.date)

/-- A prepared controller uses port 0 for work, port 1 for ignition and
port 2 for the selector. Credit memories belong to a separate cell. -/
noncomputable def preparedCappedController (θ : Fin 1 → Parameters) (origin : ℝ)
    (high : Bool) : Snapshot 1 where
  time := origin
  x := fun _ c => match c with
    | .q => 1 / 10
    | .b => 11 / 10
    | .m _ => 1 / 40
    | .z p => if p = 0 then Real.log ((θ 0).cap p) else if p = 1 then Real.log 2 else selectorReadLogGain high
    | .energy => 100
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ p => if p = 1 then some origin else none
  pending := []

private theorem prepared_controller_ready {θ origin high} :
    ReadyCoordinates (preparedCappedController θ origin high) 0 := by
  refine ⟨rfl, ?_, fun p => ⟨rfl, ?_⟩⟩ <;> norm_num [preparedCappedController, RestBand]

private theorem prepared_controller_physical {θ ε origin high} (box : @PhysicalBox 1 θ ε) :
    PhysicalInvariant θ (preparedCappedController θ origin high) := by
  refine ⟨fun i => ?_, ?_, fun i => le_rfl, fun i => by norm_num [preparedCappedController]⟩
  · refine ⟨?_, ?_, fun p => ?_⟩ <;> norm_num [preparedCappedController, auxUpper]
  · intro i p
    rw [Subsingleton.elim i 0]
    have capLower : (2 : ℝ) ≤ (θ 0).cap p := by
      have h := (box.2 0 p).1.1
      linarith [box.epsilon_bounds.2]
    have logBound := Real.log_le_log (by norm_num : (0 : ℝ) < 2) capLower
    by_cases work : p = 0
    · simp [preparedCappedController, work]
    · by_cases ignition : p = 1
      · simpa [preparedCappedController, work, ignition] using logBound
      · cases high <;> simp [preparedCappedController, work, ignition, selectorReadLogGain] <;>
          linarith [Real.log_two_gt_d9]

private theorem prepared_controller_valid {θ origin high} :
    RawValid (preparedCappedController θ origin high) := by
  intro i p t h
  by_cases hp : p = 1
  · simp [preparedCappedController, hp] at h
    subst t
    exact ⟨le_rfl, by change origin ≤ origin + 1; linarith⟩
  · simp [preparedCappedController, hp] at h

/-- One absolute decoder calendar works for both selector values. The
ignition reference is obtained from the charge and gain shared by the two
preparations, before either physical execution is constructed. -/
theorem prepared_capped_dispatch_both {θ θL ε learner delay σ wireDelay}
    (controllerBox : PhysicalBox θ ε) (learnerBox : PhysicalBox θL ε)
    (learnerPhysical : PhysicalInvariant θL learner)
    (learnerReady : ∀ i, ReadyCoordinates learner i) (learnerRaw : ∀ i p, learner.raw i p = none)
    (nonnegative : 0 ≤ σ) (budget : σ ≤ cappedTeacherWorkJitter)
    (localWire : ∀ F, delay F ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ))
    (outputWire : ∀ F, wireDelay F ∈ Icc (3 / 10) (2 / 5)) :
    ∃ ignitionRef,
      ∀ high,
        let s := preparedCappedController θ learner.time high
        let contacts := cappedDispatchContacts learner.time
          (ignitionRef + cappedTeacherWorkOffset + 7 / 5) wireDelay
        let route := prependRouted (cappedCycleRouter learner.time delay) contacts
        let start := s.prependQueued learner []
        let port : Port := if high then 1 else 0
        ∃ (H : ℝ) (final : Snapshot 2)
          (crossing : CrossingExecution (prependParameters θL θ) route start final),
          CrossingCompleteThrough crossing H ∧ final.raw 0 port = some H ∧
            final.x 1 (.z 2) = selectorReadLogGain high ∧ final.x 1 .b = 11 / 10 := by
  obtain ⟨latency, early, late, root, _, _⟩ := readyPulse_first_mid_learned_crossing_transversal
    (initial := (1 / 10 : ℝ)) (amplitude := 2) (start := learner.time)
    (by constructor <;> norm_num) (by constructor <;> norm_num)
  let reference := learner.time + latency
  refine ⟨reference, ?_⟩
  intro high
  let s := preparedCappedController θ learner.time high
  have physical : PhysicalInvariant θ s := prepared_controller_physical controllerBox
  have gain : Real.exp (s.x 0 (.z 1)) = 2 := by
    norm_num [s, preparedCappedController, Real.exp_log]
  have gainBand : (9 / 5 : ℝ) ≤ Real.exp (s.x 0 (.z 1)) ∧ Real.exp (s.x 0 (.z 1)) ≤ 11 / 5 := by
    rw [gain]
    norm_num
  obtain ⟨run⟩ := capped_teacher_cycle_exists (high := high) controllerBox physical
    prepared_controller_valid prepared_controller_ready gainBand (by simp [s, preparedCappedController])
    (fun q ne => by simp [s, preparedCappedController, ne]) rfl (by simp [s, preparedCappedController])
    (by simp [s, preparedCappedController]) rfl nonnegative budget localWire
  have window : reference ∈ Icc s.time (s.time + 9 / 10) := by
    change learner.time ≤ learner.time + latency ∧ learner.time + latency ≤ learner.time + 9 / 10
    constructor <;> linarith
  have referenceRoot : readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z 1))) s.time reference = 1 := by
    rw [gain]
    exact root
  obtain ⟨final, e, crossing, _, complete, _, _, active, preserve, recovery⟩ :=
    capped_dispatch_arrives run controllerBox learnerBox physical learnerPhysical prepared_controller_ready
      rfl learnerReady learnerRaw rfl rfl gainBand.1 window referenceRoot budget localWire outputWire
  exact ⟨_, final, crossing, complete, active, preserve.trans (by simp [s, preparedCappedController]), recovery⟩

end RecursiveLearning.Native
