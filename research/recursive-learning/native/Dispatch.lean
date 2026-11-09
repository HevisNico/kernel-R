import RoutedLesson
import KernelR.HybridContactRouterTransport
import KernelR.HybridContactTransversalityFrame
import KernelR.HybridIndependentHeadProduct
import KernelR.HybridSlowReopenExistence
import KernelR.HybridFuture

/-! Read a physical selector with the same pair of clock pulses in both cases.
    The time of the first FIRE determines the destination port. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid

def dispatchClocks (time : ℝ) : List (Delivery 1) :=
  [⟨0, 2, time + 50⟩, ⟨0, 2, time + 58⟩]

def dispatchPort (prepared : Bool) : Port := if prepared then 0 else 1

private def dispatchTime (prepared : Bool) (time : ℝ) : ℝ :=
  if prepared then time + 58 else time + 50

private def laterClock (prepared : Bool) (time : ℝ) : List (Delivery 1) :=
  if prepared then [] else [⟨0, 2, time + 58⟩]

private structure DispatchAdmission (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (prepared : Bool) (time : ℝ) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) s final
  transversal : execution.ContactsTransversal
  silent : execution.ledger.emissions = []
  date : final.time = dispatchTime prepared time
  pending : final.pending = laterClock prepared time
  gain : final.x 0 (.z 2) = 3 / 5
  ready : ∀ i, ReadyCoordinates final i
  physical : PhysicalInvariant θ final
  rawValid : RawValid final
  active : final.raw 0 2 = some final.time
  other : ∀ i p, i ≠ 0 ∨ p ≠ 2 → final.raw i p = none

private theorem dispatch_admission_exists {θ ε s prepared time} (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (ready : ∀ i, ReadyCoordinates s i)
    (raw : ∀ i p, s.raw i p = none) (clock : s.time = time + 26)
    (queue : s.pending = dispatchClocks time)
    (gain : s.x 0 (.z 2) = if prepared then 0 else 3 / 5) :
    Nonempty (DispatchAdmission θ s prepared time) := by
  let first : Delivery 1 := ⟨0, 2, time + 50⟩
  let second : Delivery 1 := ⟨0, 2, time + 58⟩
  have rawValid : RawValid s := by intro i p origin active; rw [raw i p] at active; contradiction
  have firstLater : s.time < first.due := by rw [clock]; dsimp [first]; linarith
  cases prepared with
  | false =>
    obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := fun _ _ => [])
      box s first [second] physical rawValid ready raw firstLater queue
      (by norm_num [first, second])
    refine ⟨⟨arrival.final, arrival.execution, arrival.contacts_transversal, arrival.emissions,
      arrival.date, arrival.pending, ?_, arrival.ready, arrival.physical, arrival.raw_valid,
      arrival.raw_active, arrival.raw_other⟩⟩
    rw [arrival.gain_preserved]
    exact gain
  | true =>
    have logPos := Real.log_nonneg (show (1 : ℝ) ≤ 6 / 5 by norm_num)
    obtain ⟨dose⟩ := port_dose_exists (route := fun _ _ => []) (start := s)
      (port := 2) (due := first.due) (later := [second]) box
      physical rawValid (ready 0) (raw 0) firstLater queue
      (by simp [first, second]; linarith)
      (by rw [gain]; norm_num) (by rw [gain]; change 0 ≤ _; linarith)
    have nextLater : dose.final.time < second.due := by
      rw [dose.complete.1]
      dsimp [first, second]
      linarith
    obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := fun _ _ => []) box dose.final second []
      dose.physical dose.rawValid (fun i => by simpa only [Subsingleton.elim i 0] using dose.ready)
      (fun i p => by simpa only [Subsingleton.elim i 0] using dose.rawNone p) nextLater dose.pending (by simp)
    refine ⟨⟨arrival.final, dose.execution.append arrival.execution,
      (Execution.contactsTransversal_append _ _).2 ⟨dose.transversal, arrival.contacts_transversal⟩,
      by rw [Execution.emissions_append, dose.emissions, arrival.emissions]; rfl,
      arrival.date, arrival.pending, ?_, arrival.ready, arrival.physical, arrival.raw_valid,
      arrival.raw_active, arrival.raw_other⟩⟩
    rw [arrival.gain_preserved, dose.gain, gain]
    norm_num

structure TeacherDispatch (θ : Fin 1 → Parameters) (s : Snapshot 1) (prepared : Bool) (time : ℝ) where
  admitted : Snapshot 1
  lead : Execution θ (fun _ _ => []) s admitted
  transverse : lead.ContactsTransversal
  silent : lead.ledger.emissions = []
  fire : FirstLearnedFire θ (fun _ _ => []) admitted 0 2
  fast : MidLearnedFastEnd fire
  window : dispatchTime prepared time < fire.final.time ∧
    fire.final.time < dispatchTime prepared time + 1
  remaining : admitted.pending = laterClock prepared time

theorem teacher_dispatch_exists {θ ε s prepared time} (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (ready : ∀ i, ReadyCoordinates s i)
    (raw : ∀ i p, s.raw i p = none) (clock : s.time = time + 26)
    (queue : s.pending = dispatchClocks time)
    (gain : s.x 0 (.z 2) = if prepared then 0 else 3 / 5) :
    Nonempty (TeacherDispatch θ s prepared time) := by
  obtain ⟨arrival⟩ := dispatch_admission_exists box physical ready raw clock queue gain
  have strong : 9 / 5 ≤ Real.exp (arrival.final.x 0 (.z 2)) ∧
      Real.exp (arrival.final.x 0 (.z 2)) ≤ 11 / 5 := by
    rw [arrival.gain]
    exact learnedProbe_gain
  have future : ∀ d ∈ arrival.final.pending, arrival.final.time + 31 / 4 ≤ d.due := by
    rw [arrival.pending, arrival.date]
    cases prepared
    · simp [laterClock, dispatchTime]
      linarith
    · simp [laterClock]
  obtain ⟨fire⟩ := first_mid_learned_fire_exists arrival.final box arrival.physical arrival.rawValid
    0 2 arrival.ready strong arrival.active arrival.other future
  obtain ⟨fast⟩ := fire.mid_learned_fast_end_exists box (arrival.ready 0) strong.2
    (fun p hp => arrival.other 0 p (Or.inr hp)) future
  refine ⟨⟨arrival.final, arrival.execution, arrival.transversal, arrival.silent, fire, fast,
    ?_, arrival.pending⟩⟩
  rw [fire.date, arrival.date]
  constructor <;> linarith [fire.early, fire.deadline]

private theorem future_transverse {n θ route s u} (e : @Execution n θ route s u)
    (future : List (Delivery n)) (later : ∀ d ∈ future, u.time ≤ d.due)
    (positive : e.ContactsTransversal) : (e.withFuture future later).ContactsTransversal := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow flow => exact ih later positive
    | jump jump =>
      exact ⟨(jump.contactTransversal_requeue (jump.withFuture future)).1 positive.1,
        ih later positive.2⟩

private structure LearnerWait (θ : Fin 1 → Parameters) (s : Snapshot 1) (T : ℝ) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) s final
  complete : CompleteThrough execution T
  transverse : execution.ContactsTransversal
  silent : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  ready : ∀ i, ReadyCoordinates final i
  rawNone : ∀ i p, final.raw i p = none
  empty : final.pending = []

/-- Let a genuinely SLOW learner reopen at its own logarithmic guard.
    This uses the low recovery carried out of the lesson. -/
private theorem learner_reopens {θ : Fin 1 → Parameters} {s : Snapshot 1}
    (state : LearnerDispatchState s) (empty : s.pending = [])
    (mode : s.main 0 = .slow) (lower : 1 / 10 < s.x 0 .q) (upper : s.x 0 .q ≤ 1 / 4)
    (rate : s.x 0 .b = 2 / 25) :
    ∃ T, T < s.time + 19 ∧ Nonempty (LearnerWait θ s T) := by
  let T := s.time + slowReopenDuration s 0
  have ratePos : 0 < s.x 0 .b := by rw [rate]; norm_num
  have ratio : 1 < s.x 0 .q / (1 / 10) := by linarith
  have duration : 0 < slowReopenDuration s 0 := div_pos (Real.log_pos ratio) ratePos
  have later : s.time < T := by dsimp [T]; linarith
  have limit : T < s.time + 19 := by
    have logBound := Real.log_le_sub_one_of_pos (by linarith : 0 < s.x 0 .q / (1 / 10))
    dsimp [T, slowReopenDuration]
    rw [rate]
    linarith
  have auxBelow (i : Fin 1) (p : Port) : s.x i (.m p) < 1 := by
    rw [Subsingleton.elim i 0]
    linarith [(state.auxiliary p).2.2]
  let flow : Flow θ s (protectedMainEnd θ s 0 0 .slow .ready none T) :=
    protectedMainFlow s 0 0 .slow .ready none later (Or.inr rfl) (Or.inl rfl) mode
      (fun i hi => False.elim (hi (Subsingleton.elim i 0))) (state.auxiliary 0).1
      (fun i p _ => by rw [Subsingleton.elim i 0]; exact (state.auxiliary p).1)
      (state.rawNone 0 0) (fun i p _ => state.rawNone i p) (by simp)
      (fun i hi => False.elim (hi (Subsingleton.elim i 0))) (fun i p _ => auxBelow i p)
      (by intro t ht; simpa [protectedMainRate] using slowReopen_preguard s 0 lower ratePos ht.2)
      (by intro t ht; simp only [ite_true, rawInputScale, mul_zero, auxPulse_zero_eq_relax]
          exact relax_lt (by norm_num) ht.1 (auxBelow 0 0) (by norm_num))
      (by simp [empty])
  let before := protectedMainEnd θ s 0 0 .slow .ready none T
  have threshold : before.x 0 .q = 1 / 10 := by
    simpa [before, protectedMainEnd, protectedMainValues, protectedMainRate, T] using
      slowReopen_root s 0 lower ratePos
  let final := setMain before 0 .ready
  let trace : Execution θ (fun _ _ => []) s final :=
    .cons (.flow flow) (.cons (.jump (.reopen before 0 mode threshold)) (.nil _))
  have ready (i : Fin 1) : ReadyCoordinates final i := by
    rw [Subsingleton.elim i 0]
    refine ⟨by simp [final, setMain], ?_, ?_⟩
    · change 1 / 10 - 1 / 100000 ≤ before.x 0 .q ∧ before.x 0 .q ≤ 7 / 50
      rw [threshold]
      norm_num
    · intro p
      refine ⟨(state.auxiliary p).1, ?_⟩
      have band := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) later.le (state.auxiliary p).2
        (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Set.Icc
          (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
      change RestBand (before.x 0 (.m p))
      by_cases same : p = 0
      · subst p
        simpa [before, protectedMainEnd, protectedMainValues, rawInputScale,
          auxPulse_zero_eq_relax, RestBand] using band
      · simpa [before, protectedMainEnd, protectedMainValues, same, RestBand] using band
  refine ⟨T, limit, ⟨⟨final, trace, ⟨rfl, ?_, by simp [final, setMain, before, protectedMainEnd, empty]⟩,
    by simp [trace, Jump.ContactTransversal], rfl, rfl, ready, state.rawNone, empty⟩⟩⟩
  intro v
  apply ready_no_jump final (fun i => (ready i).ready) (fun i p => ((ready i).auxiliary p).1)
    state.rawNone (fun i => by linarith [(ready i).charge.2])
    (fun i p => by linarith [((ready i).auxiliary p).2.2])
  simp [final, setMain, before, protectedMainEnd, empty]

private theorem learner_wait_exists {θ : Fin 1 → Parameters} {s : Snapshot 1} {T : ℝ}
    (state : LearnerDispatchState s) (empty : s.pending = []) (later : s.time + 19 < T) :
    Nonempty (LearnerWait θ s T) := by
  have finish (v : Snapshot 1) (lead : Execution θ (fun _ _ => []) s v)
      (next : v.time < T) (ready : ∀ i, ReadyCoordinates v i)
      (raw : ∀ i p, v.raw i p = none) (empty : v.pending = [])
      (transverse : lead.ContactsTransversal)
      (silent : lead.ledger.emissions = []) (deliveries : lead.deliveries = []) :
      Nonempty (LearnerWait θ s T) := by
    obtain ⟨wait, complete, waitTransverse, waitSilent, waitDeliveries⟩ :=
      quiet_ready_tail_exists (θ := θ) next ready raw empty
    exact ⟨⟨_, lead.append wait, complete,
      (Execution.contactsTransversal_append _ _).2 ⟨transverse, waitTransverse⟩,
      by simp [Execution.emissions_append, silent, waitSilent],
      by simp [Execution.deliveries_append, deliveries, waitDeliveries],
      fun i => quietAt_ready_coordinates v i (ready i) next.le, raw, empty⟩⟩
  rcases state.main with ready | ⟨mode, lower, upper, rate⟩
  · exact finish s (.nil _) (by linarith) (fun i => by simpa only [Subsingleton.elim i 0] using ready)
      state.rawNone empty trivial rfl rfl
  · obtain ⟨date, bound, ⟨reopen⟩⟩ := learner_reopens (θ := θ) state empty mode lower upper rate
    exact finish reopen.final reopen.execution (by rw [reopen.complete.1]; linarith)
      reopen.ready reopen.rawNone reopen.empty reopen.transverse reopen.silent reopen.deliveries

noncomputable def dispatchRouter (time : ℝ) (delay : ℝ → ℝ) : Router 2 :=
  fun i t => if i = 0 then
    if time + 50 ≤ t then [⟨1, if t < time + 58 then 1 else 0, t + delay t⟩] else []
  else lessonSelectorRouter time delay i t

def globalDispatchClocks (time : ℝ) : List (Delivery 2) :=
  (dispatchClocks time).map Delivery.head

private theorem projections_prepend (s : Snapshot 2) (Q R : List (Delivery 1))
    (pending : List (Delivery 2)) :
    (s.cellProjection 1 Q).prependQueued (s.cellProjection 0 R) pending = s.requeue pending := by
  cases s
  simp only [Snapshot.cellProjection, Snapshot.prependQueued, Snapshot.prependQuiet, Snapshot.requeue]
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem local_physical {θ : Fin 2 → Parameters} {s : Snapshot 2}
    (physical : PhysicalInvariant θ s) (i : Fin 2) (Q : List (Delivery 1)) :
    PhysicalInvariant (fun _ => θ i) (s.cellProjection i Q) :=
  ⟨fun _ => physical.region i, fun _ => physical.gain_cap i,
    fun _ => physical.recovery_cap i, fun _ => physical.reserve i⟩

private theorem no_emissions_of_product {θL θT : Fin 1 → Parameters} {s u a b : Snapshot 1}
    {left : Execution θL (fun _ _ => []) s u} {right : Execution θT (fun _ _ => []) a b}
    (weave : IndependentHeadProduct left right)
    (silentL : left.ledger.emissions = []) (silentR : right.ledger.emissions = []) :
    weave.execution.ledger.emissions = [] := by
  apply (Multiset.coe_eq_zero _).mp
  calc
    _ = (left.ledger.emissions.map (fun ev => (ev.1.succ, ev.2)) : Multiset (Fin 2 × ℝ)) +
        (right.ledger.emissions.map (fun ev => ((0 : Fin 2), ev.2)) : Multiset (Fin 2 × ℝ)) :=
      weave.trace.emissions
    _ = 0 := by simp [silentL, silentR]

private theorem pending_of_product {θL θT : Fin 1 → Parameters} {s u a b : Snapshot 1}
    {left : Execution θL (fun _ _ => []) s u} {right : Execution θT (fun _ _ => []) a b}
    (weave : IndependentHeadProduct left right) {prepared time}
    (empty : u.pending = []) (remaining : b.pending = laterClock prepared time) :
    weave.pending = (laterClock prepared time).map (Delivery.head (n := 1)) := by
  have count : (weave.pending : Multiset (Delivery 2)) =
      ((laterClock prepared time).map (Delivery.head (n := 1)) : List (Delivery 2)) := by
    calc
      _ = (u.pending.map Delivery.succ : Multiset (Delivery 2)) +
          (b.pending.map (Delivery.head (n := 1)) : Multiset (Delivery 2)) := weave.terminal
      _ = _ := by simp [empty, remaining]
  have perm := Multiset.coe_eq_coe.mp count
  cases prepared
  · exact List.perm_singleton.mp perm
  · exact List.perm_nil.mp perm

private theorem teacher_route_at_fire {θ s prepared time delay} (d : TeacherDispatch θ s prepared time) :
    dispatchRouter time delay 0 d.fire.final.time =
      [⟨1, dispatchPort prepared, d.fire.final.time + delay d.fire.final.time⟩] := by
  have early := d.window.1
  have late := d.window.2
  cases prepared
  · change time + 50 < d.fire.final.time at early
    change d.fire.final.time < time + 50 + 1 at late
    simp [dispatchRouter, dispatchPort, early.le, show d.fire.final.time < time + 58 by linarith]
  · change time + 58 < d.fire.final.time at early
    simp [dispatchRouter, dispatchPort, show time + 50 ≤ d.fire.final.time by linarith, not_lt.mpr early.le]

structure DispatchedLesson (learner : Fin 1 → Parameters) (teacher : Parameters)
    (prepared : Bool) (time : ℝ) (delay : ℝ → ℝ) where
  lesson : RoutedLessonRun learner teacher prepared time delay
  lead : Execution (prependParameters (fun _ => teacher) learner) (dispatchRouter time delay)
    (withFuture (routedLessonStart prepared time) (globalDispatchClocks time))
    (withFuture lesson.final (globalDispatchClocks time))
  leadTransverse : lead.ContactsTransversal
  final : Snapshot 2
  dispatch : Execution (prependParameters (fun _ => teacher) learner) (dispatchRouter time delay)
    (withFuture lesson.final (globalDispatchClocks time)) final
  fire : ℝ
  complete : CompleteThrough dispatch (fire + delay fire)
  transverse : dispatch.ContactsTransversal
  onlyFire : dispatch.ledger.emissions = [(0, fire)]
  chosen : final.raw 1 (dispatchPort prepared) = some final.time
  wire : (⟨1, dispatchPort prepared, fire + delay fire⟩ : Delivery 2) ∈ dispatch.deliveries
  earlySlot : fire < time + 58 ↔ prepared = false

noncomputable def DispatchedLesson.execution {learner teacher prepared time delay}
    (run : DispatchedLesson learner teacher prepared time delay) :
    Execution (prependParameters (fun _ => teacher) learner) (dispatchRouter time delay)
      (withFuture (routedLessonStart prepared time) (globalDispatchClocks time)) run.final :=
  run.lead.append run.dispatch

/-- The same network reads its actual selector. Its first teacher FIRE
    issues a token to the selected learner port, then that token arrives. -/
theorem dispatched_lesson_exists {learner teacher ε delay}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε)
    (prepared : Bool) (time : ℝ)
    (bounds : ∀ f, (3 / 10 : ℝ) ≤ delay f ∧ delay f ≤ 2 / 5) :
    Nonempty (DispatchedLesson learner teacher prepared time delay) := by
  obtain ⟨lesson⟩ := routed_lesson_run_exists box prepared time bounds
  obtain ⟨orderedBox, physical, _⟩ := routed_lesson_physical (prepared := prepared) (time := time) box
  have atHandoff := lesson.execution.physical_invariant orderedBox physical
  have future : ∀ d ∈ globalDispatchClocks time, lesson.final.time ≤ d.due := by
    rw [lesson.complete.1]
    norm_num [globalDispatchClocks, dispatchClocks, Delivery.head]
  let framed := lesson.execution.withFuture (globalDispatchClocks time) future
  have framedTransverse := future_transverse lesson.execution _ future lesson.transversal
  have frameLedger : framed.ledger = lesson.execution.ledger := lesson.execution.withFuture_ledger _ _
  obtain ⟨lead, _, _, leadTransverse⟩ := framed.retarget_router_transversal
    (dispatchRouter time delay) (by
      intro event member
      rw [frameLedger] at member
      have early := (lesson.execution.emission_time_bounds _ member).2
      rw [lesson.complete.1] at early
      by_cases head : event.1 = 0
      · rcases event with ⟨i, f⟩
        change i = 0 at head
        subst i
        simp [dispatchRouter, lessonSelectorRouter, prependRouted,
          show ¬ time + 50 ≤ f by linarith]
      · simp [dispatchRouter, head])
  let learnerStart := lesson.final.cellProjection 1 []
  let teacherStart := lesson.final.cellProjection 0 (dispatchClocks time)
  have teacherPhysical : PhysicalInvariant (fun _ : Fin 1 => teacher) teacherStart :=
    local_physical atHandoff 0 _
  have learnerPhysical : PhysicalInvariant learner learnerStart := by
    have equal : (fun _ : Fin 1 => (prependParameters (fun _ => teacher) learner) 1) = learner := by
      funext i
      rw [Subsingleton.elim i 0]
      rfl
    rw [← equal]
    exact local_physical atHandoff 1 _
  obtain ⟨teacherTrace⟩ := teacher_dispatch_exists (prepared := prepared) (time := time)
    box.extend_new teacherPhysical
    (fun i => ⟨lesson.teacherReady.ready, lesson.teacherReady.charge, lesson.teacherReady.auxiliary⟩)
    (fun _ => lesson.teacherRawNone) lesson.complete.1 rfl
    (by
      change lesson.final.x 0 (.z 2) = _
      cases prepared <;> simpa using lesson.teacherGains 2)
  let F := teacherTrace.fire.final.time
  let H := F + delay F
  have Fafter : time + 50 < F := by
    have early := teacherTrace.window.1
    cases prepared <;> simp [dispatchTime] at early <;> linarith
  have Hafter : F < H := by dsimp [H]; linarith [(bounds F).1]
  obtain ⟨wait⟩ := learner_wait_exists (θ := learner) (T := F) lesson.learnerDispatch rfl
    (by change lesson.final.time + 19 < F; rw [lesson.complete.1]; linarith)
  let teacherLead := teacherTrace.lead.append teacherTrace.fire.portBeforeExecution
  have teacherLeadSilent : teacherLead.ledger.emissions = [] := by
    simp [teacherLead, Execution.emissions_append, teacherTrace.silent, teacherTrace.fire.portBefore_emissions]
  have beforeClock : teacherTrace.fire.portBefore.time = F := rfl
  obtain ⟨pre⟩ := wait.execution.prepend_independent_exists teacherLead rfl
    (wait.complete.1.trans beforeClock.symm)
  have preSilent := no_emissions_of_product pre wait.silent teacherLeadSilent
  obtain ⟨preTrace, preLedger, _, preTransverse⟩ := pre.execution.retarget_router_transversal
    (dispatchRouter time delay) (by simp [preSilent])
  have preSource : learnerStart.prependQueued teacherStart (independentHeadQueue learnerStart teacherStart) =
      withFuture lesson.final (globalDispatchClocks time) := by
    rw [projections_prepend]
    simp [independentHeadQueue, learnerStart, teacherStart, Snapshot.cellProjection, globalDispatchClocks,
      Snapshot.requeue, withFuture, lesson.pendingEmpty]
  have teacherPending : teacherTrace.fire.portBefore.pending = laterClock prepared time :=
    teacherTrace.fire.firstSilent.queue_preserved.trans teacherTrace.remaining
  have prePending := pending_of_product pre wait.empty teacherPending
  let before := wait.final.prependQueued teacherTrace.fire.portBefore pre.pending
  let after := (setMain before 0 .fast).requeue (before.pending ++ dispatchRouter time delay 0 before.time)
  let jump : Jump (dispatchRouter time delay) before after :=
    .fire before 0 (teacherTrace.fire.firstSilent.main_ready 0) teacherTrace.fire.threshold
  have actualClock : before.time = F := wait.complete.1
  have jumpEmissions : jump.ledger.emissions = [(0, F)] := by
    change [(0, before.time)] = _
    rw [actualClock]
  have jumpPositive : jump.ContactTransversal (prependParameters (fun _ => teacher) learner) := by
    change 0 < field (prependParameters (fun _ => teacher) learner) before before.x before.time 0 .q
    rw [actualClock, ← beforeClock, field_prependQueued_head]
    exact teacherTrace.fire.contact_field_positive
  let wire : Delivery 1 := ⟨0, dispatchPort prepared, H⟩
  let receiving := wait.final.requeue [wire]
  have receivingPhysical : PhysicalInvariant learner receiving := by
    have endPhysical := wait.execution.physical_invariant box.extend_old learnerPhysical
    exact ⟨endPhysical.region,endPhysical.gain_cap,endPhysical.recovery_cap,endPhysical.reserve⟩
  have receivingReady : ∀ i, ReadyCoordinates receiving i := fun i =>
    ⟨(wait.ready i).ready,(wait.ready i).charge,(wait.ready i).auxiliary⟩
  obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := fun _ _ => []) box.extend_old receiving wire []
    receivingPhysical (by intro i p origin active; exact False.elim (by
      change wait.final.raw i p = some origin at active; rw [wait.rawNone i p] at active; contradiction))
    receivingReady wait.rawNone (by change wait.final.time < H; rw [wait.complete.1]; exact Hafter)
    rfl (by simp)
  obtain ⟨cut⟩ := teacherTrace.fast.execution.before_flow_cut_exists H Hafter.le
    (by rw [teacherTrace.fast.date]; dsimp [H]; linarith [(bounds F).2])
  have cutSilent := (List.append_eq_nil_iff.mp (cut.emissions.symm.trans teacherTrace.fast.emissions)).1
  have cutNoDelivery := (List.append_eq_nil_iff.mp (cut.deliveries.symm.trans teacherTrace.fast.deliveries)).1
  obtain ⟨post⟩ := arrival.execution.prepend_independent_exists cut.cut
    wait.complete.1 (arrival.date.trans cut.date.symm)
  have postSilent := no_emissions_of_product post arrival.emissions cutSilent
  obtain ⟨postTrace, postLedger, postDeliveries, postTransverse⟩ := post.execution.retarget_router_transversal
    (dispatchRouter time delay) (by simp [postSilent])
  have postSource : receiving.prependQueued teacherTrace.fire.final
      (independentHeadQueue receiving teacherTrace.fire.final) = after := by
    have pending : teacherTrace.fire.final.pending = laterClock prepared time := by
      rw [teacherTrace.fire.pending, teacherTrace.remaining, List.append_nil]
    have queue : independentHeadQueue receiving teacherTrace.fire.final =
        pre.pending ++ dispatchRouter time delay 0 before.time := by
      rw [actualClock, teacher_route_at_fire teacherTrace, prePending]
      simp [independentHeadQueue, receiving, Snapshot.requeue, pending, wire, H, F, Delivery.succ]
    rw [queue, teacherTrace.fire.port_final_empty, Snapshot.prependQueued_setMain_head]
    rfl
  let startDispatch := preTrace.cast_source preSource.symm
  let finishDispatch := postTrace.cast_source postSource.symm
  let startFire := startDispatch.append (.cons (.jump jump) (.nil _))
  let dispatch := startFire.append finishDispatch
  have postComplete := post.complete (arrival.complete (by simp)) cut.complete
  have complete : CompleteThrough dispatch H :=
    ⟨postComplete.1, no_jump_retarget_router postComplete.2.1 _, postComplete.2.2⟩
  have preFires : startDispatch.ledger.emissions = [] := by
    rw [Execution.cast_source_ledger, preLedger, preSilent]
  have postFires : finishDispatch.ledger.emissions = [] := by
    rw [Execution.cast_source_ledger, postLedger, postSilent]
  refine ⟨{
    lesson := lesson, lead := lead, leadTransverse := leadTransverse.2 framedTransverse
    final := _, dispatch := dispatch, fire := F, complete := complete
    transverse := ?_, onlyFire := ?_, chosen := ?_, wire := ?_, earlySlot := ?_
  }⟩
  · apply (startFire.contactsTransversal_append finishDispatch).2
    refine ⟨(startDispatch.contactsTransversal_append _).2 ⟨?_,⟨jumpPositive,trivial⟩⟩, ?_⟩
    · apply (preTrace.contactsTransversal_cast_source preSource.symm).2
      apply preTransverse.2
      apply pre.contacts_transversal wait.transverse
      exact (teacherTrace.lead.contactsTransversal_append _).2
        ⟨teacherTrace.transverse, by
          simp [FirstLearnedFire.portBeforeExecution, Execution.ContactsTransversal]⟩
    · apply (postTrace.contactsTransversal_cast_source postSource.symm).2
      exact postTransverse.2 (post.contacts_transversal arrival.contacts_transversal
        (cut.isPrefix.contacts_transversal teacherTrace.fast.contacts_transversal))
  · simp [dispatch, startFire, Execution.emissions_append, preFires, postFires,
      Execution.ledger, Move.ledger, Ledger.add, Ledger.zero, jumpEmissions]
  · exact arrival.raw_active
  · change (⟨1, dispatchPort prepared, H⟩ : Delivery 2) ∈ (startFire.append finishDispatch).deliveries
    rw [Execution.deliveries_append]
    apply List.mem_append_right
    rw [Execution.cast_source_deliveries, postDeliveries]
    have counts : (post.execution.deliveries : Multiset (Delivery 2)) =
        ([⟨1, dispatchPort prepared, H⟩] : List (Delivery 2)) := by
      calc
        _ = (arrival.execution.deliveries.map Delivery.succ : Multiset (Delivery 2)) +
            (cut.cut.deliveries.map (Delivery.head (n := 1)) : Multiset (Delivery 2)) := post.trace.deliveries
        _ = _ := by simp [arrival.deliveries, cutNoDelivery, wire, Delivery.succ]
    exact (Multiset.coe_eq_coe.mp counts).mem_iff.mpr (by simp)
  · have window := teacherTrace.window
    cases prepared <;> simp [dispatchTime] at window ⊢ <;> dsimp [F] <;> linarith

private theorem dispatch_router_strict {time : ℝ} {delay : ℝ → ℝ}
    (positive : ∀ t, 0 < delay t) : StrictCausalRouter (dispatchRouter time delay) := by
  intro i t d member
  by_cases head : i = 0
  · by_cases openClock : time + 50 ≤ t
    · simp [dispatchRouter, head, openClock] at member
      subst d
      exact lt_add_of_pos_right t (positive t)
    · simp [dispatchRouter, head, openClock] at member
  · apply lesson_router_strict positive i t d
    simpa [dispatchRouter, head] using member

private theorem dispatch_physical {learner teacher ε prepared time}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε) :
    PhysicalBox (prependParameters (fun _ => teacher) learner) ε ∧
    PhysicalInvariant (prependParameters (fun _ => teacher) learner)
      (withFuture (routedLessonStart prepared time) (globalDispatchClocks time)) ∧
    InitiallyBelowReady (withFuture (routedLessonStart prepared time) (globalDispatchClocks time)) := by
  obtain ⟨orderedBox, physical, initial⟩ := routed_lesson_physical (prepared := prepared) (time := time) box
  exact ⟨orderedBox, ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩, initial⟩

theorem DispatchedLesson.contacts_transversal {learner teacher prepared time delay}
    (run : DispatchedLesson learner teacher prepared time delay) : run.execution.ContactsTransversal :=
  (run.lead.contactsTransversal_append run.dispatch).2 ⟨run.leadTransverse, run.transverse⟩

/-- One actual upward-crossing history runs from the lesson's original
    state through receipt of the teacher's selected next pulse. -/
theorem dispatched_lesson_crossing_exists {learner teacher ε delay}
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε)
    (prepared : Bool) (time : ℝ)
    (bounds : ∀ f, (3 / 10 : ℝ) ≤ delay f ∧ delay f ≤ 2 / 5) :
    ∃ (run : DispatchedLesson learner teacher prepared time delay)
      (crossing : CrossingExecution (prependParameters (fun _ => teacher) learner)
        (dispatchRouter time delay)
        (withFuture (routedLessonStart prepared time) (globalDispatchClocks time)) run.final),
      crossing.execution = run.execution.toWeak ∧
      CrossingCompleteThrough crossing (run.fire + delay run.fire) := by
  obtain ⟨run⟩ := dispatched_lesson_exists box prepared time bounds
  obtain ⟨orderedBox, physical, initial⟩ := dispatch_physical (prepared := prepared) (time := time) box
  exact ⟨run, run.execution.toCrossing initial orderedBox physical run.contacts_transversal, rfl,
    run.complete.toCrossing run.execution initial orderedBox physical run.contacts_transversal⟩

/-- At the receipt horizon, all complete crossing executions have the
    same physical endpoint and FIREs, including the selected raw input. -/
theorem DispatchedLesson.every_crossing_complete {learner teacher ε prepared time delay final}
    (run : DispatchedLesson learner teacher prepared time delay)
    (box : @PhysicalBox 2 (extendParameters learner teacher) ε)
    (positive : ∀ f, 0 < delay f)
    (crossing : CrossingExecution (prependParameters (fun _ => teacher) learner)
      (dispatchRouter time delay)
      (withFuture (routedLessonStart prepared time) (globalDispatchClocks time)) final)
    (complete : CrossingCompleteThrough crossing (run.fire + delay run.fire)) :
    run.final.ObservationalEq final ∧
      run.execution.ledger.emissions.Perm crossing.execution.ledger.emissions := by
  obtain ⟨orderedBox, physical, initial⟩ := dispatch_physical (prepared := prepared) (time := time) box
  obtain ⟨native, same⟩ := crossing.execution.toNative_of_transverse_completion run.execution
    (dispatch_router_strict positive) orderedBox physical run.complete run.contacts_transversal (le_of_eq complete.1)
  have weakComplete := complete.toWeak_of_native crossing native same initial orderedBox physical
  exact run.execution.observational_unique_weak orderedBox crossing.execution physical
    run.complete run.contacts_transversal weakComplete

end RecursiveLearning.Native
