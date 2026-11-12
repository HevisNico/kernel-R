import Teaching.NativeAcceptance

/-! A real acceptance FIRE issues the full next lesson to a fresh R learner. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid

noncomputable def acceptanceLessonContacts (time : ℝ) (lesson : Lesson) : HeadRoutes 1 :=
  fun _ F => if F < time + 26 then lessonDeliveries (time + 30) (lessonPorts lesson) else []

/-- The receiver's physical birth data is the same on acceptance and rejection. -/
noncomputable def acceptanceLessonStart (time : ℝ) (third : Bool) : Snapshot 2 :=
  let tester := acceptanceStart time third
  tester.prependQueued (nativeLessonStart time ⟨0, 0⟩) (tester.pending.map Delivery.succ)

theorem native_lesson_wait {θ : Fin 1 → Parameters} {time clock : ℝ} (later : time < clock) (lesson : Lesson) :
    ∃ e : Execution θ (fun _ _ => [])
      { nativeLessonStart clock lesson with time := time }
      (nativeLessonStart clock lesson),
      e.ContactsTransversal ∧ e.ledger.emissions = [] ∧ e.deliveries = [] := by
  let v := nativeLessonStart clock lesson
  let u : Snapshot 1 := {v with time := time}
  have future : ∀ d ∈ u.pending, clock ≤ d.due := by
    intro d hd
    change d ∈ lessonDeliveries clock (lessonPorts lesson) at hd
    linarith [lesson_delivery_time hd]
  let flow : Flow θ u (quietAt u clock) :=
    quietFlow u later (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun i => by change (1 / 10 : ℝ) < 1; norm_num)
      (fun i p => by change (1 / 40 : ℝ) < 1; norm_num) future
  have wait : quietAt u clock = v := by
    suffices vals : (quietAt u clock).x = v.x by
      change { v with x := _ } = v
      exact congrArg (fun x => {v with x := x}) vals
    funext i c
    cases c <;> simp [u, v, quietAt, quietValues, nativeLessonStart, preparedTeacher, relax]
  have transport {target : Snapshot 1} (eq : quietAt u clock = target) :
      ∃ e : Execution θ (fun _ _ => []) u target,
        e.ContactsTransversal ∧ e.ledger.emissions = [] ∧ e.deliveries = [] := by
    cases eq
    exact ⟨.cons (.flow flow) (.nil _), trivial, rfl, rfl⟩
  exact transport wait

/-- The subsequent lesson is a fixed proposal. The native counter's
acceptance FIRE releases its entire source sequence. Without that FIRE
the learner receives no lesson pulse. -/
theorem native_acceptance_dispatches_lesson {θT θL ε} (testBox : @PhysicalBox 1 θT ε)
    (learnerBox : @PhysicalBox 1 θL ε) (time : ℝ) (lesson : Lesson)
    (capacity : lesson.preparation ≤ 4 ∧ lesson.practice ≤ 4) (third : Bool) :
    let θ := prependParameters θL θT
    let route := prependRouted (fun _ _ => []) (acceptanceLessonContacts time lesson)
    let start := acceptanceLessonStart time third
    ∃ (final : Snapshot 2) (e : Execution θ route start final)
      (crossing : CrossingExecution θ route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing (time + 95) ∧
      lessonReceipts e.deliveries 0 = (if third then lesson.cost else 0) ∧
      ∀ needs, NativeRetains final 0 needs ↔
        ((if third then lesson else ⟨0, 0⟩ : Lesson).train needs).retained = true := by
  obtain ⟨test⟩ := acceptance_signal_exists testBox time third
  obtain ⟨waitTest, testComplete, waitPositive, waitSilent, _⟩ :=
    quiet_ready_tail_exists (θ := θT) (T := time + 95)
      (by rw [test.complete.1]; linarith) test.ready test.rawNone test.empty
  let tester := test.execution.append waitTest
  have fires : tester.ledger.emissions = test.fire.toList.map (fun F => (0, F)) := by
    rw [Execution.emissions_append, test.emissions, waitSilent, List.append_nil]
  let candidate : Lesson := if third then lesson else ⟨0, 0⟩
  let learner := nativeLessonStart (time + 30) candidate
  have capacity' : candidate.preparation ≤ 4 ∧ candidate.practice ≤ 4 := by
    cases third
    · norm_num [candidate]
    · exact capacity
  have after : (time + 30) + 8 * candidate.cost < time + 95 := by
    have h : (candidate.cost : ℝ) ≤ 8 := by
      exact_mod_cast (show candidate.cost ≤ 8 from Nat.add_le_add capacity'.1 capacity'.2)
    linarith
  obtain ⟨run⟩ := native_lesson_exists learnerBox (time + 30) candidate capacity'.1 capacity'.2
  obtain ⟨lessonRun, learnerComplete, lessonPositive, lessonCount, _, learns⟩ := run.finish_at after
  obtain ⟨waitLearner, initialPositive, _, initialSilent⟩ :=
    native_lesson_wait (θ := θL) (clock := time + 30) (by linarith) candidate
  let receiver := waitLearner.append lessonRun
  have sourceCount : receiver.deliveries.length = candidate.cost := by
    rw [Execution.deliveries_append, initialSilent, List.nil_append, lessonCount]
  let contacts := acceptanceLessonContacts time lesson
  have queue : ({learner with time := time} : Snapshot 1).pending = tester.headInputQueue contacts := by
    rw [Execution.headInputQueue, fires, List.flatMap_map]
    cases h : test.fire with
    | none =>
      have low : third = false := by simpa [h] using test.reports.symm
      simp [learner, candidate, low, nativeLessonStart, lessonPorts, lessonDeliveries]
    | some F =>
      have high : third = true := by simpa [h] using test.reports.symm
      simp [learner, candidate, high, nativeLessonStart, contacts, acceptanceLessonContacts,
        (test.window F h).2]
  have strict : StrictHeadRoutes contacts := by
    intro i F d hd
    by_cases before : F < time + 26
    · have member : d ∈ lessonDeliveries (time + 30) (lessonPorts lesson) := by
        simpa [contacts, acceptanceLessonContacts, before] using hd
      linarith [lesson_delivery_time member]
    · simp [contacts, acceptanceLessonContacts, before] at hd
  have balance := HeadQueueBalance.initial tester ({learner with time := time} : Snapshot 1) contacts queue
  obtain ⟨weave⟩ := tester.prepend_causal_result receiver rfl
    (testComplete.1.trans learnerComplete.1.symm) contacts strict _ balance
  have complete := weave.complete testComplete learnerComplete
  have positive := weave.contacts_transversal
    ((Execution.contactsTransversal_append _ _).2 ⟨test.transverse, waitPositive⟩)
    ((Execution.contactsTransversal_append _ _).2 ⟨initialPositive, lessonPositive⟩)
  have count : lessonReceipts weave.execution.deliveries 0 = (if third then lesson.cost else 0) := by
    refine (CausalTraceBalance.head_receipts weave.trace).trans (sourceCount.trans ?_)
    cases third <;> rfl
  have box : PhysicalBox (prependParameters θL θT) ε := by
    refine ⟨testBox.1, ?_⟩
    intro i p
    cases i using Fin.cases with
    | zero => exact learnerBox.2 0 p
    | succ i => exact testBox.2 i p
  have physical : PhysicalInvariant (prependParameters θL θT) (acceptanceLessonStart time third) := by
    have learnerPhys := native_lesson_physical learnerBox time ⟨0, 0⟩
    have counterPhys := acceptance_counter_physical testBox time third
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; cases i using Fin.cases with
      | zero => exact learnerPhys.region 0
      | succ j => exact counterPhys.region j
    · intro i p; cases i using Fin.cases with
      | zero => exact learnerPhys.gain_cap 0 p
      | succ j => exact counterPhys.gain_cap j p
    · intro i; cases i using Fin.cases with
      | zero => exact learnerPhys.recovery_cap 0
      | succ j => exact counterPhys.recovery_cap j
    · intro i; cases i using Fin.cases with
      | zero => exact learnerPhys.reserve 0
      | succ j => exact counterPhys.reserve j
  have initial : InitiallyBelowReady (acceptanceLessonStart time third) := by
    intro i c h
    cases c with
    | q =>
      cases i using Fin.cases <;> change (1 / 10 : ℝ) < 1 <;> norm_num
    | m p =>
      cases i using Fin.cases <;> change (1 / 40 : ℝ) < 1 <;> norm_num
    | z _ => exact False.elim h
    | b => exact False.elim h
    | energy => exact False.elim h
  exact ⟨_, weave.execution, weave.execution.toCrossing initial box physical positive, rfl,
    complete.toCrossing weave.execution initial box physical positive, count, learns⟩

/-- The same fixed router either sends all six practice-focused lesson
pulses or sends nothing, depending on the actual native threshold test. -/
theorem native_acceptance_dispatches_six {θT θL ε} (testBox : @PhysicalBox 1 θT ε)
    (learnerBox : @PhysicalBox 1 θL ε) (time : ℝ) (third : Bool) :
    let θ := prependParameters θL θT
    let route := prependRouted (fun _ _ => []) (acceptanceLessonContacts time ⟨3, 3⟩)
    let start := acceptanceLessonStart time third
    ∃ (final : Snapshot 2) (e : Execution θ route start final)
      (crossing : CrossingExecution θ route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing (time + 95) ∧
      lessonReceipts e.deliveries 0 = (if third then 6 else 0) ∧
      (NativeRetains final 0 ⟨3, 3⟩ ↔ third = true) := by
  obtain ⟨final, e, crossing, same, complete, receipts, retention⟩ :=
    native_acceptance_dispatches_lesson testBox learnerBox time ⟨3, 3⟩ (by decide) third
  refine ⟨final, e, crossing, same, complete, receipts, ?_⟩
  rw [retention]
  cases third <;> decide

end RecursiveLearning.Native
