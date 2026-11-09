import ScheduledCircuit

/-! A certified decision report can commit a credit and dispatch a lesson.
Both receiver cells start with empty input queues. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid

noncomputable def branchCreditContacts {n} (sender : Fin n) (window : ReportWindow)
    (clock : ℝ) (port : Port) : HeadRoutes n :=
  forwardReport sender window [⟨0, port, clock + 1⟩]

noncomputable def branchLessonContacts {n} (sender : Fin n) (window : ReportWindow)
    (clock : ℝ) (lesson : Lesson) : HeadRoutes (n + 1) :=
  forwardReport sender.succ window (lessonDeliveries clock (lessonPorts lesson))

noncomputable def branchStart {n} (s : Snapshot n) : Snapshot (n + 1 + 1) :=
  addEmptyLearner (queueHead s ((preparedTeacher s.time).requeue []))

noncomputable def branchRouter {n} (route : Router n) (sender : Fin n) (window : ReportWindow)
    (clock : ℝ) (port : Port) (lesson : Lesson) : Router (n + 1 + 1) :=
  prependRouted (prependRouted route (branchCreditContacts sender window clock port))
    (branchLessonContacts sender window clock lesson)

structure BranchCommit {n θ route s u} (prior : @Execution n θ route s u)
    (θC θL : Fin 1 → Parameters) (sender : Fin n) (window : ReportWindow) (clock T : ℝ)
    (port : Port) (proposal : Lesson) (accepted : Bool) where
  final : Snapshot (n + 1 + 1)
  execution : Execution (prependParameters θL (prependParameters θC θ))
    (branchRouter route sender window clock port proposal) (branchStart s) final
  complete : CompleteThrough execution T
  transverse : prior.ContactsTransversal → execution.ContactsTransversal
  creditReceipts : lessonReceipts execution.deliveries (0 : Fin (n + 1)).succ = if accepted then 1 else 0
  credit : ∀ p, final.x (0 : Fin (n + 1)).succ (.z p) =
    if p = port ∧ accepted then 3 / 5 else 0
  lessonReceipts : RecursiveLearning.Native.lessonReceipts execution.deliveries 0 =
    if accepted then proposal.cost else 0
  previousValues : ∀ i, final.x i.succ.succ = u.x i
  previousTimes : ∀ i, execution.emissionTimes i.succ.succ = prior.emissionTimes i
  previousReceipts : ∀ i, RecursiveLearning.Native.lessonReceipts execution.deliveries i.succ.succ =
    RecursiveLearning.Native.lessonReceipts prior.deliveries i

/-- One accepted decision triggers one credit and the declared lesson.
An inactive branch delivers zero tokens to both of its action cells.
Earlier reports and deliveries are carried into the enlarged trace. -/
theorem compose_report_commit {n θ θC θL ε route s u T clock}
    (send : @Execution n θ route s u) (done : CompleteThrough send T)
    (creditBox : @PhysicalBox 1 θC ε) (lessonBox : @PhysicalBox 1 θL ε)
    (sender : Fin n) (window : ReportWindow) (bit : Bool) (reported : Reports send sender window bit)
    (port : Port) (proposal : Lesson) (capacity : proposal.preparation ≤ 4 ∧ proposal.practice ≤ 4)
    (future : s.time < clock) (margin : window.stop ≤ clock)
    (horizon : clock + 8 * proposal.cost + 10 < T) :
    Nonempty (BranchCommit send θC θL sender window clock T port proposal bit) := by
  let due := clock + 1
  let creditDate := due - 7 / 20
  let flag : Option ℝ := if bit then some creditDate else none
  have costNonneg : (0 : ℝ) ≤ proposal.cost := by positivity
  obtain ⟨credit⟩ := credit_response_exists creditBox (time := s.time) (T := T) (credit := port) (fire := flag)
    (by linarith) (fun F h => by
      cases bit
      · simp [flag] at h
      · have eq : creditDate = F := by simpa [flag] using h
        rw [← eq]
        dsimp [creditDate, due]
        constructor <;> linarith)
  let creditSource := (preparedTeacher s.time).requeue
    (flag.toList.map (fun F => ⟨0, port, F + 7 / 20⟩))
  have creditQueue : creditSource.pending = if bit then [⟨0, port, due⟩] else [] := by
    have date : creditDate + 7 / 20 = due := by dsimp [creditDate]; ring
    cases bit <;> simp [creditSource, Snapshot.requeue, flag, date]
  have creditInput : send.headInputQueue (branchCreditContacts sender window clock port) = creditSource.pending :=
    (forward_report_inputs send sender window [⟨0, port, due⟩] bit reported).trans creditQueue.symm
  have creditCausal : StrictHeadRoutes (branchCreditContacts sender window clock port) :=
    forward_report_strict sender window (by
      intro d h
      obtain rfl := List.mem_singleton.mp h
      change window.stop ≤ clock + 1
      linarith)
  have creditDelivered : credit.execution.deliveries.length = if bit then 1 else 0 := by
    have dueBefore : ∀ d ∈ creditSource.pending, d.due ≤ T := by
      rw [creditQueue]
      cases bit
      · simp
      · intro d h
        obtain rfl := List.mem_singleton.mp h
        dsimp [due]
        linarith
    have perm := credit.execution.deliveries_perm_sources T credit.complete dueBefore (fun _ _ => rfl)
    calc
      _ = creditSource.pending.length := perm.length_eq
      _ = _ := by rw [creditQueue]; cases bit <;> rfl
  obtain ⟨committed⟩ := compose_scheduled_receiver send credit.execution done credit.complete rfl []
    (branchCreditContacts sender window clock port) creditCausal (List.Perm.of_eq creditInput)
  have committedDone := committed.complete done credit.complete
  have carriedReport : Reports committed.execution sender.succ window bit := by
    unfold Reports ReportWindow.dates
    rw [committed.tail_emission_times]
    exact reported
  let taught := if bit then proposal else ⟨0, 0⟩
  have cap : taught.preparation ≤ 4 ∧ taught.practice ≤ 4 := by
    cases bit <;> simp [taught, capacity]
  have lessonHorizon : clock + 8 * taught.cost < T := by
    cases bit <;> simp [taught, Lesson.cost] at * <;> linarith
  obtain ⟨lesson⟩ := native_lesson_exists lessonBox clock taught cap.1 cap.2
  obtain ⟨tail, tailDone, tailTransverse, tailCount, _, _⟩ := lesson.finish_at lessonHorizon
  obtain ⟨lead, leadTransverse, _, leadDeliveries⟩ := native_lesson_wait (θ := θL) future taught
  let learn := lead.append tail
  have delivered : learn.deliveries.length = taught.cost := by
    rw [Execution.deliveries_append, leadDeliveries, List.nil_append, tailCount]
  let learnStart : Snapshot 1 := {nativeLessonStart clock taught with time := s.time}
  have learnQueue : committed.execution.headInputQueue (branchLessonContacts sender window clock proposal) =
      learnStart.pending := by
    rw [branchLessonContacts, forward_report_inputs committed.execution sender.succ window _ bit carriedReport]
    cases bit <;> rfl
  have learnCausal : StrictHeadRoutes (branchLessonContacts sender window clock proposal) :=
    forward_report_strict sender.succ window (fun d h => by linarith [lesson_delivery_time h])
  obtain ⟨whole⟩ := compose_scheduled_receiver committed.execution learn committedDone tailDone rfl []
    (branchLessonContacts sender window clock proposal) learnCausal (List.Perm.of_eq learnQueue)
  let e : Execution (prependParameters θL (prependParameters θC θ))
      (branchRouter route sender window clock port proposal) (branchStart s) _ := whole.execution
  refine ⟨⟨_, e, whole.complete committedDone tailDone, ?_, ?_, ?_, ?_,
    fun _ => rfl, ?_, ?_⟩⟩
  · intro h
    exact whole.contacts_transversal (committed.contacts_transversal h credit.positive)
      ((Execution.contactsTransversal_append _ _).2 ⟨leadTransverse, tailTransverse⟩)
  · change lessonReceipts whole.execution.deliveries (0 : Fin (n + 1)).succ = _
    rw [CausalTraceBalance.tail_receipts whole.trace, CausalTraceBalance.head_receipts committed.trace]
    exact creditDelivered
  · intro p
    change credit.final.x 0 (.z p) = _
    rw [credit.written]
    cases bit <;> rfl
  · change lessonReceipts whole.execution.deliveries 0 = _
    rw [CausalTraceBalance.head_receipts whole.trace]
    exact delivered.trans (by cases bit <;> rfl)
  · intro i
    exact (whole.tail_emission_times i.succ).trans (committed.tail_emission_times i)
  · intro i
    exact (CausalTraceBalance.tail_receipts whole.trace i.succ).trans
      (CausalTraceBalance.tail_receipts committed.trace i)


/-- Every complete crossing execution has the same endpoint, dates and
delivery multiset as the constructed branch. The native representative
has the very same weak steps as the crossing execution. -/
theorem BranchCommit.crossing {n θ θC θL ε route s u sender window clock T port proposal bit}
    {send : @Execution n θ route s u} (b : BranchCommit send θC θL sender window clock T port proposal bit)
    (physical : PhysicalInvariant θ s) (initial : InitiallyBelowReady s)
    (causal : StrictCausalRouter route) (transverse : send.ContactsTransversal)
    (box : PhysicalBox θ ε) (creditBox : PhysicalBox θC ε) (lessonBox : PhysicalBox θL ε)
    (margin : window.stop ≤ clock) :
    let parameters := prependParameters θL (prependParameters θC θ)
    let wiring := branchRouter route sender window clock port proposal
    ∃ crossing : CrossingExecution parameters wiring (branchStart s) b.final,
      crossing.execution = b.execution.toWeak ∧ CrossingCompleteThrough crossing T ∧
      ∀ otherFinal (other : CrossingExecution parameters wiring (branchStart s) otherFinal),
        CrossingCompleteThrough other T →
        ∃ native : Execution parameters wiring (branchStart s) otherFinal,
          native.toWeak = other.execution ∧ otherFinal.ObservationalEq b.final ∧
          native.deliveries.Perm b.execution.deliveries ∧
          ∀ i, other.execution.emissionTimes i = b.execution.emissionTimes i := by
  have allBox := prepend_box (prepend_box box creditBox) lessonBox
  have allPhysical : PhysicalInvariant (prependParameters θL (prependParameters θC θ)) (branchStart s) :=
    prepend_physical (prepend_physical physical (preparedTeacher_physical creditBox s.time []) _)
      (native_lesson_physical lessonBox s.time ⟨0, 0⟩) _
  have creditInitial : InitiallyBelowReady ((preparedTeacher s.time).requeue []) := by
    intro i c h
    cases c with
    | q => change (1 / 10 : ℝ) < 1; norm_num
    | m p => change (1 / 40 : ℝ) < 1; norm_num
    | z _ => exact False.elim h
    | b => exact False.elim h
    | energy => exact False.elim h
  have allInitial : InitiallyBelowReady (branchStart s) := by
    intro i c h
    cases i using Fin.cases with
    | zero => exact native_lesson_initial s.time ⟨0, 0⟩ 0 c h
    | succ i =>
      cases i using Fin.cases with
      | zero => exact creditInitial 0 c h
      | succ i => exact initial i c h
  have creditCausal : StrictHeadRoutes (branchCreditContacts sender window clock port) :=
    forward_report_strict sender window (by
      intro d h
      obtain rfl := List.mem_singleton.mp h
      change window.stop ≤ clock + 1
      linarith)
  have lessonCausal : StrictHeadRoutes (branchLessonContacts sender window clock proposal) :=
    forward_report_strict sender.succ window (fun d h => by linarith [lesson_delivery_time h])
  have strict := prepend_routed_causal (prepend_routed_causal causal creditCausal) lessonCausal
  have pos := b.transverse transverse
  refine ⟨b.execution.toCrossing allInitial allBox allPhysical pos, rfl,
    b.complete.toCrossing b.execution allInitial allBox allPhysical pos, ?_⟩
  intro otherFinal other done
  obtain ⟨native, same⟩ := other.execution.toNative_of_transverse_completion b.execution strict
    allBox allPhysical b.complete pos (le_of_eq done.1)
  have weak := done.toWeak_of_native other native same allInitial allBox allPhysical
  obtain ⟨state, emissions⟩ :=
    b.execution.observational_unique_weak allBox other.execution allPhysical b.complete pos weak
  have ledger : native.ledger = other.execution.ledger := by rw [← same, Execution.toWeak_ledger]
  have queues := Multiset.coe_eq_coe.mpr state.symm.pending
  have issued := Multiset.coe_eq_coe.mpr
    (emissions.symm.flatMap_right (fun event => branchRouter route sender window clock port proposal event.1 event.2))
  have balanced := native.token_balance.trans
    ((congrArg (fun m : Multiset (Delivery (n + 1 + 1)) => ((branchStart s).pending : Multiset _) + m)
      (by simpa only [ledger] using issued)).trans b.execution.token_balance.symm)
  have receipts : native.deliveries.Perm b.execution.deliveries := by
    apply Multiset.coe_eq_coe.mp
    exact add_left_cancel (by simpa only [queues] using balanced)
  exact ⟨native, same, state.symm, receipts,
    fun i => (b.execution.emissionTimes_unique_weak other.execution allBox allPhysical b.complete pos weak i).symm⟩


/-- Compile a decision over physical learner reports and attach its guarded
action. Inactive actions deliver neither a lesson nor a credit. -/
theorem ReportCircuit.run_guarded_branch {n m θ θC θL ε} (c : ReportCircuit n m)
    (box : @PhysicalBox m θ ε) (creditBox : @PhysicalBox 1 θC ε) (lessonBox : @PhysicalBox 1 θL ε)
    (time : ℝ) (kinds passed : Fin n → Bool) (decision : Fin m) (port : Port)
    (proposal : Lesson) (capacity : proposal.preparation ≤ 4 ∧ proposal.practice ≤ 4) :
    let layout := c.compile (learnerReportLayout time kinds passed)
    let clock := layout.last + 1
    let T := clock + 8 * proposal.cost + 46
    ∃ (run : CompiledRun θ layout T (c.eval passed))
      (action : BranchCommit run.execution θC θL decision (layout.windows decision) clock T port proposal
        (c.eval passed decision))
      (crossing : CrossingExecution (prependParameters θL (prependParameters θC θ))
        (branchRouter layout.route decision (layout.windows decision) clock port proposal)
        (branchStart layout.start) action.final),
      crossing.execution = action.execution.toWeak ∧ CrossingCompleteThrough crossing T := by
  let layout := c.compile (learnerReportLayout time kinds passed)
  let clock := layout.last + 1
  let T := clock + 8 * proposal.cost + 46
  have timeBound : (trialBankStart time kinds passed).time < time + 66 := by
    rw [trial_bank_clock]
    linarith
  have timed := c.compile_timed (layout := learnerReportLayout time kinds passed)
    ⟨timeBound, fun _ => le_rfl⟩
  have costNonneg : (0 : ℝ) ≤ proposal.cost := by positivity
  have enough : layout.last + 45 < T := by dsimp [T, clock]; linarith
  obtain ⟨run⟩ := c.run_with_learners box time kinds passed enough
  have margin : (layout.windows decision).stop ≤ clock := by dsimp [clock]; linarith [timed.2 decision]
  obtain ⟨action⟩ := compose_report_commit run.execution run.complete creditBox lessonBox decision
    (layout.windows decision) (c.eval passed decision) (run.reports decision) port proposal capacity
    (by dsimp [clock]; linarith [timed.1]) margin (by dsimp [T]; linarith)
  obtain ⟨crossing, eq, done, _⟩ := action.crossing run.physical run.initial run.causal run.positive
    box creditBox lessonBox margin
  exact ⟨run, action, crossing, eq, done⟩

end RecursiveLearning.Native
