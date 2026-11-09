import LessonProbe
import KernelR.HybridIndependentHeadProduct

/-! Native validation of full two-block lessons. Each delivered pulse is
recorded by its own exposed ERROR phase. Preparation and practice have
separate counters. The test reads the two final physical gains. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid

def lessonPorts (lesson : Lesson) : List Port :=
  List.replicate lesson.preparation 0 ++ List.replicate lesson.practice 1

noncomputable def lessonDeliveries (origin : ℝ) : List Port → List (Delivery 1)
  | [] => []
  | p :: ps => ⟨0, p, origin + 1 / 2⟩ :: lessonDeliveries (origin + 8) ps

theorem lesson_delivery_time {origin : ℝ} {ports : List Port} {d : Delivery 1}
    (member : d ∈ lessonDeliveries origin ports) : origin + 1 / 2 ≤ d.due := by
  induction ports generalizing origin with
  | nil => simp [lessonDeliveries] at member
  | cons p ps ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact le_rfl
    · linarith [ih tail]

structure LessonDoseRun (θ : Fin 1 → Parameters) (start : Snapshot 1) (ports : List Port) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) start final
  complete : CompleteThrough execution (start.time + 8 * ports.length)
  transverse : execution.ContactsTransversal
  deliveries : execution.deliveries = lessonDeliveries start.time ports
  silent : execution.ledger.emissions = []
  gains : ∀ p, final.x 0 (.z p) = start.x 0 (.z p) + (3 / 5 : ℝ) * ports.count p
  recovery : final.x 0 .b = start.x 0 .b
  ready : ReadyCoordinates final 0
  rawNone : ∀ p, final.raw 0 p = none
  empty : final.pending = []

/-- Each listed delivery causes exactly one dose at its target port.
The bound leaves every input in the weak regime until its last dose. -/
theorem lesson_dose_run_exists {θ ε start ports} (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ start) (valid : RawValid start)
    (ready : ReadyCoordinates start 0) (rawNone : ∀ p, start.raw 0 p = none)
    (queue : start.pending = lessonDeliveries start.time ports)
    (headroom : ∀ p, start.x 0 (.z p) + (3 / 5 : ℝ) * ports.count p ≤ 3 / 5) :
    Nonempty (LessonDoseRun θ start ports) := by
  induction ports generalizing start with
  | nil =>
    have empty : start.pending = [] := queue
    have noJump : ∀ u, IsEmpty (Jump (fun _ _ => []) start u) := by
      apply ready_no_jump start
      · intro i; rw [Subsingleton.elim i 0]; exact ready.ready
      · intro i p; rw [Subsingleton.elim i 0]; exact (ready.auxiliary p).1
      · intro i p; rw [Subsingleton.elim i 0]; exact rawNone p
      · intro i; rw [Subsingleton.elim i 0]; linarith [ready.charge.2]
      · intro i p; rw [Subsingleton.elim i 0]; linarith [(ready.auxiliary p).2.2]
      · simp [empty]
    refine ⟨⟨start, .nil _, ?_, trivial, rfl, rfl, ?_, rfl, ready, rawNone, empty⟩⟩
    · simp only [List.length_nil, Nat.cast_zero, mul_zero, add_zero]
      exact ⟨rfl, noJump, by simp [empty]⟩
    · intro p
      simp
  | cons p ps ih =>
    let clock := start.time
    have gain_nonpositive : start.x 0 (.z p) ≤ 0 := by
      have head := headroom p
      have count : (1 : ℝ) ≤ ((p :: ps).count p : ℝ) := by
        exact_mod_cast (show 1 ≤ (p :: ps).count p by simp)
      linarith
    obtain ⟨dose⟩ := port_dose_exists (route := fun _ _ => []) (port := p)
      (due := clock + 1 / 2) (later := lessonDeliveries (clock + 8) ps)
      box physical valid ready rawNone (by dsimp [clock]; linarith) queue
      (by intro d hd; linarith [lesson_delivery_time hd])
      (by
        have expBound := Real.exp_le_exp.mpr gain_nonpositive
        rw [Real.exp_zero] at expBound
        linarith)
      (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 6 / 5 by norm_num)])
    have date : dose.final.time = clock + 8 := by rw [dose.complete.1]; ring
    have tailQueue : dose.final.pending = lessonDeliveries dose.final.time ps := by
      rw [date]
      exact dose.pending
    have accounting (q : Port) :
        dose.final.x 0 (.z q) + (3 / 5 : ℝ) * ps.count q =
          start.x 0 (.z q) + (3 / 5 : ℝ) * (p :: ps).count q := by
      rw [dose.gain]
      by_cases eq : q = p
      · subst q
        simp only [ite_true, List.count_cons_self, Nat.cast_add, Nat.cast_one]
        ring
      · simp [eq, Ne.symm eq]
    obtain ⟨tail⟩ := ih dose.physical dose.rawValid dose.ready dose.rawNone tailQueue
      (fun q => by rw [accounting]; exact headroom q)
    refine ⟨⟨tail.final, dose.execution.append tail.execution, ?_,
      (Execution.contactsTransversal_append _ _).2 ⟨dose.transversal, tail.transverse⟩,
      ?_, ?_, ?_, tail.recovery.trans dose.recovery, tail.ready, tail.rawNone, tail.empty⟩⟩
    · have finish : dose.final.time + 8 * (ps.length : ℝ) = start.time + 8 * (↑(p :: ps).length : ℝ) := by
        rw [date]; dsimp [clock]; simp only [Nat.cast_add, Nat.cast_one]; ring
      exact ⟨tail.complete.1.trans finish, tail.complete.2.1, by rw [← finish]; exact tail.complete.2.2⟩
    · rw [Execution.deliveries_append, dose.deliveries, tail.deliveries, date]
      rfl
    · rw [Execution.emissions_append, dose.emissions, tail.silent]
      rfl
    · intro q
      rw [tail.gains, accounting]

/-- A learner's two gain counters start at -2.4. The actual READY state and
sensor dynamics come from R. The source sends the preparation block first. -/
noncomputable def nativeLessonStart (time : ℝ) (lesson : Lesson) : Snapshot 1 :=
  { preparedTeacher time with
    x := fun i c => match c with
      | .z _ => -(12 / 5 : ℝ)
      | other => (preparedTeacher time).x i other
    pending := lessonDeliveries time (lessonPorts lesson) }

/-- The threshold of each gain counter specifies the learner's need in
units of exposed ERROR doses. This is a terminal state observation. -/
def NativeRetains {n} (state : Snapshot n) (i : Fin n) (needs : Learner) : Prop :=
  -(12 / 5 : ℝ) + (3 / 5 : ℝ) * needs.preparationLeft ≤ state.x i (.z 0) ∧
  -(12 / 5 : ℝ) + (3 / 5 : ℝ) * needs.practiceLeft ≤ state.x i (.z 1)

theorem lessonPorts_count (lesson : Lesson) :
    (lessonPorts lesson).count 0 = lesson.preparation ∧
    (lessonPorts lesson).count 1 = lesson.practice ∧
    (lessonPorts lesson).count 2 = 0 := by
  simp [lessonPorts, List.count_append, List.count_replicate]

private theorem lessonPorts_length (lesson : Lesson) :
    (lessonPorts lesson).length = lesson.cost := by simp [lessonPorts, Lesson.cost]

private theorem lessonDeliveries_length (origin : ℝ) (ports : List Port) :
    (lessonDeliveries origin ports).length = ports.length := by
  induction ports generalizing origin with
  | nil => rfl
  | cons p ps ih => simp [lessonDeliveries, ih]

theorem native_lesson_initial (time : ℝ) (lesson : Lesson) :
    InitiallyBelowReady (nativeLessonStart time lesson) := by
  intro i c ready
  cases c with
  | q => norm_num [nativeLessonStart, preparedTeacher]
  | m p => norm_num [nativeLessonStart, preparedTeacher]
  | z _ => exact False.elim ready
  | b => exact False.elim ready
  | energy => exact False.elim ready

theorem native_lesson_physical {θ ε} (box : @PhysicalBox 1 θ ε) (time : ℝ) (lesson : Lesson) :
    PhysicalInvariant θ (nativeLessonStart time lesson) := by
  let prepared := preparedTeacher_physical box time []
  refine ⟨prepared.region, ?_, prepared.recovery_cap, prepared.reserve⟩
  intro i p
  have cap := prepared.gain_cap i p
  change (0 : ℝ) ≤ Real.log ((θ i).cap p) at cap
  change -(12 / 5 : ℝ) ≤ Real.log ((θ i).cap p)
  linarith

theorem native_lesson_exists {θ ε} (box : @PhysicalBox 1 θ ε) (time : ℝ)
    (lesson : Lesson) (prep : lesson.preparation ≤ 4) (practice : lesson.practice ≤ 4) :
    Nonempty (LessonDoseRun θ (nativeLessonStart time lesson) (lessonPorts lesson)) := by
  apply lesson_dose_run_exists box (native_lesson_physical box time lesson)
    (by simp [RawValid, nativeLessonStart, preparedTeacher])
    ⟨rfl, by norm_num [nativeLessonStart, preparedTeacher], fun p =>
      ⟨rfl, by norm_num [nativeLessonStart, preparedTeacher, RestBand]⟩⟩ (fun _ => rfl) rfl
  intro p
  obtain ⟨a,b,c⟩ := lessonPorts_count lesson
  have prep' : (lesson.preparation : ℝ) ≤ 4 := by exact_mod_cast prep
  have practice' : (lesson.practice : ℝ) ≤ 4 := by exact_mod_cast practice
  fin_cases p
  · change -(12 / 5 : ℝ) + 3 / 5 * (lessonPorts lesson).count 0 ≤ 3 / 5
    rw [a]; linarith
  · change -(12 / 5 : ℝ) + 3 / 5 * (lessonPorts lesson).count 1 ≤ 3 / 5
    rw [b]; linarith
  · change -(12 / 5 : ℝ) + 3 / 5 * (lessonPorts lesson).count 2 ≤ 3 / 5
    rw [c]; norm_num

theorem LessonDoseRun.native_lesson_retains {θ time lesson}
    (run : LessonDoseRun θ (nativeLessonStart time lesson) (lessonPorts lesson)) (needs : Learner) :
    NativeRetains run.final 0 needs ↔ (lesson.train needs).retained = true := by
  rw [Lesson.retained_iff]
  obtain ⟨prep, practice, _⟩ := lessonPorts_count lesson
  rw [NativeRetains, run.gains 0, run.gains 1, prep, practice]
  simp only [nativeLessonStart]
  constructor
  · intro h
    have a : (needs.preparationLeft : ℝ) ≤ lesson.preparation := by linarith [h.1]
    have b : (needs.practiceLeft : ℝ) ≤ lesson.practice := by linarith [h.2]
    exact ⟨by exact_mod_cast a, by exact_mod_cast b⟩
  · intro h
    have a : (needs.preparationLeft : ℝ) ≤ lesson.preparation := by exact_mod_cast h.1
    have b : (needs.practiceLeft : ℝ) ≤ lesson.practice := by exact_mod_cast h.2
    constructor <;> linarith

theorem LessonDoseRun.crossing_lesson {θ ε time lesson}
    (run : LessonDoseRun θ (nativeLessonStart time lesson) (lessonPorts lesson))
    (box : PhysicalBox θ ε) :
    ∃ crossing : CrossingExecution θ (fun _ _ => []) (nativeLessonStart time lesson) run.final,
      crossing.execution = run.execution.toWeak ∧
      CrossingCompleteThrough crossing (time + 8 * lesson.cost) ∧
      run.execution.deliveries.length = lesson.cost := by
  have initial := native_lesson_initial time lesson
  have physical := native_lesson_physical box time lesson
  have complete : CompleteThrough run.execution (time + 8 * lesson.cost) := by
    simpa only [lessonPorts_length, nativeLessonStart, preparedTeacher] using run.complete
  refine ⟨run.execution.toCrossing initial box physical run.transverse, rfl,
    complete.toCrossing run.execution initial box physical run.transverse, ?_⟩
  rw [run.deliveries, lessonDeliveries_length, lessonPorts_length]

/-- The source delivers exactly the lesson's full pulse count. Its terminal
physical test agrees with the discrete learner for every choice of needs. -/
theorem native_lesson_crossing_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (time : ℝ) (lesson : Lesson) (prep : lesson.preparation ≤ 4) (practice : lesson.practice ≤ 4) :
    ∃ (final : Snapshot 1)
      (native : Execution θ (fun _ _ => []) (nativeLessonStart time lesson) final)
      (crossing : CrossingExecution θ (fun _ _ => []) (nativeLessonStart time lesson) final),
      CrossingCompleteThrough crossing (time + 8 * lesson.cost) ∧
      crossing.execution = native.toWeak ∧ native.deliveries.length = lesson.cost ∧
      ∀ needs, NativeRetains final 0 needs ↔ (lesson.train needs).retained = true := by
  obtain ⟨run⟩ := native_lesson_exists box time lesson prep practice
  obtain ⟨crossing, same, complete, count⟩ := run.crossing_lesson box
  exact ⟨run.final, run.execution, crossing, complete, same, count, run.native_lesson_retains⟩

/-- Count actual delivery events at a chosen physical cell. -/
def lessonReceipts {n} (events : List (Delivery n)) (cell : Fin n) : Nat :=
  (events.filter (fun token => token.cell == cell)).length

private theorem local_receipts {events : List (Delivery 1)} :
    lessonReceipts events 0 = events.length := by
  simp [lessonReceipts, Subsingleton.elim (_ : Fin 1) 0]

theorem CausalTraceBalance.head_receipts {n globalE globalD tailE tailD headE headD}
    (balance : @CausalTraceBalance n globalE globalD tailE tailD headE headD) :
    lessonReceipts globalD 0 = headD.length := by
  have perm : globalD.Perm (tailD.map Delivery.succ ++ headD.map Delivery.head) :=
    Multiset.coe_eq_coe.mp (balance.deliveries.trans (Multiset.coe_add _ _).symm)
  unfold lessonReceipts
  rw [(perm.filter _).length_eq, List.filter_append, List.filter_map, List.filter_map]
  simp [Delivery.succ, Delivery.head, Function.comp_def]

theorem CausalTraceBalance.tail_receipts {n globalE globalD tailE tailD headE headD}
    (balance : @CausalTraceBalance n globalE globalD tailE tailD headE headD) (i : Fin n) :
    lessonReceipts globalD i.succ = lessonReceipts tailD i := by
  have perm : globalD.Perm (tailD.map Delivery.succ ++ headD.map Delivery.head) :=
    Multiset.coe_eq_coe.mp (balance.deliveries.trans (Multiset.coe_add _ _).symm)
  unfold lessonReceipts
  rw [(perm.filter _).length_eq, List.filter_append, List.filter_map, List.filter_map]
  rw [List.length_append, List.length_map, List.length_map]
  change (tailD.filter (fun d => d.cell.succ == i.succ)).length +
    (headD.filter (fun _ => (0 : Fin (n + 1)) == i.succ)).length =
      (tailD.filter (fun d => d.cell == i)).length
  have shifted (d : Delivery n) : (d.cell.succ == i.succ) = (d.cell == i) := by
    apply Bool.eq_iff_iff.mpr
    simp [Fin.succ_inj]
  have absent : ((0 : Fin (n + 1)) == i.succ) = false :=
    beq_eq_false_iff_ne.mpr (Ne.symm (Fin.succ_ne_zero i))
  simp [shifted, absent]

/-- Extend a completed lesson to a shared later horizon while carrying
its actual charge, reserve and memories. -/
theorem LessonDoseRun.finish_at {θ time lesson T}
    (run : LessonDoseRun θ (nativeLessonStart time lesson) (lessonPorts lesson))
    (later : time + 8 * lesson.cost < T) :
    ∃ e : Execution θ (fun _ _ => []) (nativeLessonStart time lesson) (quietAt run.final T),
      CompleteThrough e T ∧ e.ContactsTransversal ∧ e.deliveries.length = lesson.cost ∧
      e.ledger.emissions = [] ∧
      ∀ needs, NativeRetains (quietAt run.final T) 0 needs ↔ (lesson.train needs).retained = true := by
  have after : run.final.time < T := by
    rw [run.complete.1, lessonPorts_length]
    exact later
  obtain ⟨wait, complete, transverse, silent, deliveries⟩ := quiet_ready_tail_exists (θ := θ) after
    (fun i => by rw [Subsingleton.elim i 0]; exact run.ready)
    (fun i p => by rw [Subsingleton.elim i 0]; exact run.rawNone p) run.empty
  refine ⟨run.execution.append wait, complete,
    (Execution.contactsTransversal_append _ _).2 ⟨run.transverse, transverse⟩, ?_, ?_, ?_⟩
  · rw [Execution.deliveries_append, run.deliveries, deliveries, List.append_nil,
      lessonDeliveries_length, lessonPorts_length]
  · rw [Execution.emissions_append, run.silent, silent]
    rfl
  · intro needs
    exact run.native_lesson_retains needs

/-- A bank of independent native learners, each with its own pulse count.
The calendars are inputs. They can be checked together in one execution. -/
noncomputable def lessonBankStart (time : ℝ) : {n : ℕ} → (Fin n → Lesson) → Snapshot n
  | 0, _ => ⟨time, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, []⟩
  | n + 1, lessons =>
      let head := nativeLessonStart time (lessons 0)
      let tail := lessonBankStart time (fun i : Fin n => lessons i.succ)
      tail.prependQueued head (independentHeadQueue tail head)

theorem lessonBankStart_date (time : ℝ) (n : ℕ) (lessons : Fin n → Lesson) :
    (lessonBankStart time lessons).time = time := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih _

private theorem lesson_bank_physical {n θ ε} (box : @PhysicalBox n θ ε)
    (time : ℝ) (lessons : Fin n → Lesson) :
    PhysicalInvariant θ (lessonBankStart time lessons) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i
  | succ n ih =>
    have headBox : PhysicalBox (fun _ : Fin 1 => θ 0) ε := ⟨box.1, fun _ p => box.2 0 p⟩
    have tailBox : PhysicalBox (fun i : Fin n => θ i.succ) ε := ⟨box.1, fun i p => box.2 i.succ p⟩
    have head := native_lesson_physical headBox time (lessons 0)
    have tail := ih tailBox (fun i => lessons i.succ)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; cases i using Fin.cases with
      | zero => exact head.region 0
      | succ i => exact tail.region i
    · intro i p; cases i using Fin.cases with
      | zero => exact head.gain_cap 0 p
      | succ i => exact tail.gain_cap i p
    · intro i; cases i using Fin.cases with
      | zero => exact head.recovery_cap 0
      | succ i => exact tail.recovery_cap i
    · intro i; cases i using Fin.cases with
      | zero => exact head.reserve 0
      | succ i => exact tail.reserve i

private theorem lesson_bank_initial {n} (time : ℝ) (lessons : Fin n → Lesson) :
    InitiallyBelowReady (lessonBankStart time lessons) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i c h
    cases i using Fin.cases with
    | zero => exact native_lesson_initial time (lessons 0) 0 c h
    | succ i => exact ih _ i c h

private theorem lesson_bank_execution {n θ ε} (box : @PhysicalBox n θ ε)
    (time : ℝ) (lessons : Fin n → Lesson) (capacity : ∀ i, (lessons i).preparation ≤ 4 ∧ (lessons i).practice ≤ 4)
    {T : ℝ} (later : time < T) (after : ∀ i, time + 8 * (lessons i).cost < T) :
    ∃ (final : Snapshot n) (e : Execution θ (fun _ _ => []) (lessonBankStart time lessons) final),
      CompleteThrough e T ∧ e.ContactsTransversal ∧ e.ledger.emissions = [] ∧
      ∀ i, lessonReceipts e.deliveries i = (lessons i).cost ∧
        ∀ needs, NativeRetains final i needs ↔ ((lessons i).train needs).retained = true := by
  induction n with
  | zero =>
    let start := lessonBankStart time lessons
    let final : Snapshot 0 := quietAt start T
    have future : ∀ d ∈ start.pending, T ≤ d.due := by simp [start, lessonBankStart]
    let flow : Flow θ start final := quietFlow start later (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) future
    let e : Execution θ (fun _ _ => []) start final := .cons (.flow flow) (.nil _)
    have noJump : ∀ u, IsEmpty (Jump (fun _ _ => []) final u) := by
      apply ready_no_jump final (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
        (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      simp [final, start, quietAt, lessonBankStart]
    exact ⟨final, e, ⟨rfl, noJump, by simp [final, start, quietAt, lessonBankStart]⟩, trivial, rfl, fun i => Fin.elim0 i⟩
  | succ n ih =>
    let θH : Fin 1 → Parameters := fun _ => θ 0
    let θT : Fin n → Parameters := fun i => θ i.succ
    have headBox : PhysicalBox θH ε := ⟨box.1, fun _ p => box.2 0 p⟩
    have tailBox : PhysicalBox θT ε := ⟨box.1, fun i p => box.2 i.succ p⟩
    obtain ⟨run⟩ := native_lesson_exists headBox time (lessons 0) (capacity 0).1 (capacity 0).2
    obtain ⟨head, headComplete, headPositive, headCount, headSilent, headRetention⟩ := run.finish_at (after 0)
    obtain ⟨_, tail, tailComplete, tailPositive, tailSilent, tailResults⟩ :=
      ih tailBox (fun i => lessons i.succ) (fun i => capacity i.succ) (fun i => after i.succ)
    obtain ⟨weave, complete⟩ := tail.prepend_independent_complete head
      (lessonBankStart_date time n _) tailComplete headComplete
    have emptyRoute : prependRouted (fun (_ : Fin n) (_ : ℝ) => []) (fun _ _ => []) = (fun _ _ => []) := by
      funext i t
      cases i using Fin.cases <;> rfl
    have params : prependParameters θH θT = θ := prependParameters_reconstruct θ
    have silent : weave.execution.ledger.emissions = [] := by
      apply List.perm_nil.mp
      apply Multiset.coe_eq_coe.mp
      rw [weave.trace.emissions, tailSilent, headSilent]
      rfl
    have transfer {s u : Snapshot (n + 1)} (e : Execution (prependParameters θH θT)
          (prependRouted (fun (_ : Fin n) (_ : ℝ) => []) (fun _ _ => [])) s u) :
        ∃ e' : Execution θ (fun _ _ => []) s u, CompleteThrough e T → CompleteThrough e' T ∧
          (e.ContactsTransversal → e'.ContactsTransversal) ∧
          e'.ledger = e.ledger ∧ e'.deliveries = e.deliveries := by
      generalize hp : prependParameters θH θT = p at e params
      generalize hr : prependRouted (fun (_ : Fin n) (_ : ℝ) => []) (fun _ _ => []) = r at e emptyRoute
      cases params
      cases emptyRoute
      exact ⟨e, fun hc => ⟨hc, id, rfl, rfl⟩⟩
    obtain ⟨execution, prop⟩ := transfer weave.execution
    obtain ⟨done, transverse, ledger, deliveries⟩ := prop complete
    refine ⟨_, execution, done, transverse (weave.contacts_transversal tailPositive headPositive),
      (congrArg Ledger.emissions ledger).trans silent, ?_⟩
    intro i
    have counted := congrArg (fun ds => lessonReceipts ds i) deliveries
    cases i using Fin.cases with
    | zero => exact ⟨counted.trans ((CausalTraceBalance.head_receipts weave.trace).trans headCount), headRetention⟩
    | succ i => exact ⟨counted.trans ((CausalTraceBalance.tail_receipts weave.trace i).trans (tailResults i).1), (tailResults i).2⟩

/-- The entire bank is a single complete upward-crossing R execution.
Every counted pulse is an actual input delivery to its physical learner. -/
theorem native_lesson_bank_crossing {n θ ε} (box : @PhysicalBox n θ ε)
    (time : ℝ) (lessons : Fin n → Lesson) (capacity : ∀ i, (lessons i).preparation ≤ 4 ∧ (lessons i).practice ≤ 4)
    {T : ℝ} (later : time < T) (after : ∀ i, time + 8 * (lessons i).cost < T) :
    ∃ (final : Snapshot n) (e : Execution θ (fun _ _ => []) (lessonBankStart time lessons) final)
      (crossing : CrossingExecution θ (fun _ _ => []) (lessonBankStart time lessons) final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing T ∧
      ∀ i, lessonReceipts e.deliveries i = (lessons i).cost ∧
        ∀ needs, NativeRetains final i needs ↔ ((lessons i).train needs).retained = true := by
  obtain ⟨final, e, complete, positive, _, result⟩ := lesson_bank_execution box time lessons capacity later after
  have init := lesson_bank_initial time lessons
  have phys := lesson_bank_physical box time lessons
  exact ⟨final, e, e.toCrossing init box phys positive, rfl,
    complete.toCrossing e init box phys positive, result⟩

/-- The three deployed lessons and the two too-short alternatives. -/
def improvementLessons (i : Fin 5) : Lesson :=
  ![⟨4, 4⟩, ⟨3, 4⟩, ⟨3, 3⟩, ⟨2, 4⟩, ⟨3, 2⟩] i

/-- All three full deployed lessons retain the skill for the held-out
learner with needs (3,3). The two proposed further reductions fail that
learner and a validation learner. These five trials share one physical
execution with independently prepared learner cells. -/
theorem native_lesson_improvement_trials {θ ε} (box : @PhysicalBox 5 θ ε) (time : ℝ) :
    ∃ (final : Snapshot 5)
      (e : Execution θ (fun _ _ => []) (lessonBankStart time improvementLessons) final)
      (crossing : CrossingExecution θ (fun _ _ => []) (lessonBankStart time improvementLessons) final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing (time + 65) ∧
      (List.ofFn fun i : Fin 5 => lessonReceipts e.deliveries i) = [8, 7, 6, 6, 5] ∧
      (∀ i : Fin 3, ∀ needs, needs ∈ Example.heldOut ++ Example.experiment.validation →
        NativeRetains final (Fin.castLE (by decide) i) needs) ∧
      ¬ NativeRetains final 3 ⟨3, 2⟩ ∧ ¬ NativeRetains final 4 ⟨2, 3⟩ := by
  obtain ⟨final, e, crossing, same, complete, trials⟩ := native_lesson_bank_crossing box time
    improvementLessons (fun i => by fin_cases i <;> decide) (T := time + 65) (by linarith)
    (fun i => by fin_cases i <;> norm_num [improvementLessons, Lesson.cost])
  refine ⟨final, e, crossing, same, complete, ?_, ?_, ?_, ?_⟩
  · simp only [funext (fun i => (trials i).1)]
    decide
  · intro i needs member
    apply ((trials (Fin.castLE (by decide) i)).2 needs).2
    simp only [Example.heldOut, Example.experiment, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> fin_cases i <;> decide
  · rw [(trials 3).2]
    decide
  · rw [(trials 4).2]
    decide

end RecursiveLearning.Native
