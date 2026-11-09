import CalibratedDecisionTree

/-! Blind finite search. The two hidden needs are encoded by the birth
gain of the port under test. The candidate lessons, wires, source queue
and clocks are identical for every hidden profile. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid


/-- Two independently unknown requirements, each either three or four. -/
structure HiddenNeed where
  morePreparation : Bool
  morePractice : Bool

def hiddenCount (more : Bool) : ℕ := if more then 4 else 3

def HiddenNeed.needs (h : HiddenNeed) : Learner :=
  ⟨hiddenCount h.morePreparation, hiddenCount h.morePractice⟩

def HiddenNeed.minimumLesson (h : HiddenNeed) : Lesson :=
  ⟨h.needs.preparationLeft, h.needs.practiceLeft⟩

theorem HiddenNeed.minimum_correct (h : HiddenNeed) :
    (h.minimumLesson.train h.needs).retained = true ∧
      ∀ lesson : Lesson, (lesson.train h.needs).retained = true →
        h.minimumLesson.preparation ≤ lesson.preparation ∧
        h.minimumLesson.practice ≤ lesson.practice ∧
        h.minimumLesson.cost ≤ lesson.cost := by
  refine ⟨(Lesson.retained_iff _ _).mpr ⟨le_rfl, le_rfl⟩, ?_⟩
  intro lesson retained
  have limits := (Lesson.retained_iff _ _).mp retained
  exact ⟨limits.1, limits.2, Nat.add_le_add limits.1 limits.2⟩

/-- After three actual doses the gain is 0.6 for need three, and zero
for need four. The read uses the same physical dynamics in both cases. -/
noncomputable def hiddenBirthGain (more : Bool) : ℝ :=
  -(3 / 5 : ℝ) * (hiddenCount more - 1 : ℕ)

private def probeNeeds (lesson : Lesson) (practice more : Bool) : Learner :=
  if practice then ⟨lesson.preparation, hiddenCount more⟩
  else ⟨hiddenCount more, lesson.practice⟩

private noncomputable def hiddenTrial (lesson : Lesson) (practice more : Bool)
    (cap : lesson.preparation ≤ 4 ∧ lesson.practice ≤ 4)
    (three : (lessonPorts lesson).count (trialPort practice) = 3) : AdaptiveTrial where
  lesson := lesson
  testPractice := practice
  passes := !more
  needs := probeNeeds lesson practice more
  birthGain := hiddenBirthGain more
  nonpositive := by cases more <;> norm_num [hiddenBirthGain, hiddenCount]
  capacity := cap
  gainTest := by
    dsimp only
    rw [three]
    cases more <;> norm_num [hiddenBirthGain, hiddenCount]
  correct := by
    apply Bool.eq_iff_iff.mpr
    rw [Lesson.retained_iff]
    cases practice
    · have count : lesson.preparation = 3 := (lessonPorts_count lesson).1.symm.trans three
      cases more <;> simp [probeNeeds, hiddenCount, count]
    · have count : lesson.practice = 3 := (lessonPorts_count lesson).2.1.symm.trans three
      cases more <;> simp [probeNeeds, hiddenCount, count]

private noncomputable def prepTrial (h : HiddenNeed) : AdaptiveTrial :=
  hiddenTrial ⟨3, 4⟩ false h.morePreparation (by decide) (by decide)

private noncomputable def lowPracticeTrial (h : HiddenNeed) : AdaptiveTrial :=
  hiddenTrial ⟨3, 3⟩ true h.morePractice (by decide) (by decide)

private noncomputable def highPracticeTrial (h : HiddenNeed) : AdaptiveTrial :=
  hiddenTrial ⟨4, 3⟩ true h.morePractice (by decide) (by decide)

/-- The initial eight-pulse reference lesson starts the search. Its
report is a common control signal, independent of the hidden learner. -/
noncomputable def blindSeedLayout (time : ℝ) : ReportLayout 1 :=
  ⟨scheduledTrial time ⟨4, 4⟩ 0 (-(9 / 5 : ℝ)), fun _ _ => [],
    fun _ => ⟨time + 65, time + 66⟩, time + 66⟩

private theorem blind_seed_exists {θ ε time T} (box : @PhysicalBox 1 θ ε)
    (horizon : time + 96 < T) :
    Nonempty (CompiledRun θ (blindSeedLayout time) T (fun _ => true)) := by
  obtain ⟨run, fire, flag, window, dates, _⟩ := staged_lesson_read_exists_of_gain
    box (time := time) (clock := time) le_rfl horizon ⟨4, 4⟩ 0 true
    (by decide) (-(9 / 5)) (by norm_num) (by
      change -(9 / 5 : ℝ) + (3 / 5) * (lessonPorts ⟨4, 4⟩).count 0 = 3 / 5
      rw [(lessonPorts_count ⟨4, 4⟩).1]
      norm_num)
  have hp := readout_learner_physical_of_gain box time ⟨4, 4⟩ 0 (-(9 / 5)) (by norm_num)
  have physical : PhysicalInvariant θ (blindSeedLayout time).start :=
    ⟨hp.region, hp.gain_cap, hp.recovery_cap, hp.reserve⟩
  have initial : InitiallyBelowReady (blindSeedLayout time).start := by
    intro i c h
    cases c with
    | q => change (1 / 10 : ℝ) < 1; norm_num
    | m p => change (1 / 40 : ℝ) < 1; norm_num
    | z _ => exact False.elim h
    | b => exact False.elim h
    | energy => exact False.elim h
  have report (i : Fin 1) : Reports run.execution i ((blindSeedLayout time).windows i) true := by
    rw [Subsingleton.elim i 0]
    unfold Reports ReportWindow.dates
    rw [dates]
    cases h : fire with
    | none => simp [h] at flag
    | some F =>
      obtain ⟨early, late⟩ := window F h
      simp [blindSeedLayout, ReportWindow.accepts, early.le, late]
  exact ⟨⟨run.final, run.execution, run.complete, run.positive, report, physical, initial,
    fun _ _ _ mem => (List.not_mem_nil mem).elim⟩⟩

private noncomputable def tryPreparation (h : HiddenNeed) : AdaptiveProgram 1 2 :=
  (AdaptiveProgram.inputs : AdaptiveProgram 1 1).trial 0 (prepTrial h)

private noncomputable def prepDecision (h : HiddenNeed) : AdaptiveProgram 1 3 :=
  (tryPreparation h).notGate 0

private noncomputable def tryLowPractice (h : HiddenNeed) : AdaptiveProgram 1 4 :=
  (prepDecision h).trial 1 (lowPracticeTrial h)

private noncomputable def tryBothBranches (h : HiddenNeed) : AdaptiveProgram 1 5 :=
  (tryLowPractice h).trial 1 (highPracticeTrial h)

private noncomputable def lowPracticeFailure (h : HiddenNeed) : AdaptiveProgram 1 6 :=
  (tryBothBranches h).notGate 1

private noncomputable def chooseThreeFour (h : HiddenNeed) : AdaptiveProgram 1 7 :=
  (lowPracticeFailure h).andGate 4 [0]

private noncomputable def highPracticeFailure (h : HiddenNeed) : AdaptiveProgram 1 8 :=
  (chooseThreeFour h).notGate 2

private noncomputable def blindDecisions (h : HiddenNeed) : AdaptiveProgram 1 9 :=
  (highPracticeFailure h).andGate 5 [0]

private noncomputable def commitThreeThree (h : HiddenNeed) : AdaptiveProgram 1 11 :=
  (blindDecisions h).commit 5 0 ⟨3, 3⟩ (by decide)

private noncomputable def commitThreeFour (h : HiddenNeed) : AdaptiveProgram 1 13 :=
  (commitThreeThree h).commit 4 0 ⟨3, 4⟩ (by decide)

private noncomputable def commitFourThree (h : HiddenNeed) : AdaptiveProgram 1 15 :=
  (commitThreeFour h).commit 8 0 ⟨4, 3⟩ (by decide)

noncomputable def blindSearchProgram (h : HiddenNeed) : AdaptiveProgram 1 17 :=
  (commitFourThree h).commit 6 0 ⟨4, 4⟩ (by decide)

noncomputable def blindSearchLayout (time : ℝ) (h : HiddenNeed) : ReportLayout 17 :=
  (blindSearchProgram h).compile (blindSeedLayout time)

/-- Compilation uses a single representative to fix the routing and
schedule. Every profile also has the same initial delivery queue. -/
theorem blind_search_same_compilation (time : ℝ) (h h' : HiddenNeed) :
    (blindSearchLayout time h).SameWiring (blindSearchLayout time h') ∧
    (blindSearchLayout time h).start.pending = (blindSearchLayout time h').start.pending := by
  have prep : (tryPreparation h).SamePlan (tryPreparation h') := .trial .inputs (fun _ => rfl)
  have tries : (tryBothBranches h).SamePlan (tryBothBranches h') :=
    .trial (.trial (.notGate prep) (fun _ => rfl)) (fun _ => rfl)
  have decisions : (blindDecisions h).SamePlan (blindDecisions h') :=
    .andGate (.notGate (.andGate (.notGate tries)))
  have plan : (blindSearchProgram h).SamePlan (blindSearchProgram h') :=
    .commit (.commit (.commit (.commit decisions)))
  exact plan.compile_same_sources ⟨⟨rfl, rfl, rfl⟩, rfl⟩

/-- The compiler can fix these clocks and wires before seeing the birth
gains. The representative's continuous values are used only as a template. -/
noncomputable def blindCompiled (time : ℝ) : ReportLayout 17 :=
  blindSearchLayout time ⟨false, false⟩

theorem blind_search_birth_gains (time : ℝ) (h : HiddenNeed) :
    let s := (blindSearchLayout time h).start
    s.x 15 (.z 0) = hiddenBirthGain h.morePreparation ∧
    s.x 13 (.z 1) = hiddenBirthGain h.morePractice ∧
    s.x 12 (.z 1) = hiddenBirthGain h.morePractice := by
  exact ⟨rfl, rfl, rfl⟩

def blindCandidate : Fin 4 → Lesson := ![⟨3, 3⟩, ⟨3, 4⟩, ⟨4, 3⟩, ⟨4, 4⟩]

def HiddenNeed.code (h : HiddenNeed) : Fin 4 :=
  match h.morePreparation, h.morePractice with
  | false, false => 0
  | false, true => 1
  | true, false => 2
  | true, true => 3

theorem HiddenNeed.candidate_is_minimum (h : HiddenNeed) :
    blindCandidate h.code = h.minimumLesson := by
  rcases h with ⟨p, q⟩
  cases p <;> cases q <;> rfl

def blindLessonCell : Fin 4 → Fin 17 := ![6, 4, 2, 0]
def blindCreditCell : Fin 4 → Fin 17 := ![7, 5, 3, 1]

/-- The terminal physical observations identify the hidden need by the
unique lesson delivered and the unique credit dose. -/
def BlindSelection (h : HiddenNeed) (final : Snapshot 17) (deliveries : List (Delivery 17)) : Prop :=
  lessonReceipts deliveries 15 = 8 ∧
  lessonReceipts deliveries 13 = (if h.morePreparation then 0 else 7) ∧
  lessonReceipts deliveries 12 = (if h.morePreparation then 8 else 0) ∧
  ∀ i,
    lessonReceipts deliveries (blindLessonCell i) = (if i = h.code then (blindCandidate i).cost else 0) ∧
    lessonReceipts deliveries (blindCreditCell i) = (if i = h.code then 1 else 0) ∧
    (∀ p, final.x (blindCreditCell i) (.z p) = if p = 0 ∧ i = h.code then 3 / 5 else 0) ∧
    (∀ needs, NativeRetains final (blindLessonCell i) needs ↔
      ((if i = h.code then blindCandidate i else ⟨0, 0⟩).train needs).retained = true)

theorem BlindSelection.selected_retains {h final deliveries} (selected : BlindSelection h final deliveries) :
    NativeRetains final (blindLessonCell h.code) h.needs := by
  apply ((selected.2.2.2 h.code).2.2.2 h.needs).mpr
  simp only [eq_self, ite_true, h.candidate_is_minimum]
  exact h.minimum_correct.1

private noncomputable def blindGuard (h : HiddenNeed) (i : Fin 4) : Bool :=
  let bits := (blindDecisions h).eval (fun _ => true)
  ![bits 5, bits 2, bits 4, bits 0] i

private theorem blind_guard_correct (h : HiddenNeed) (i : Fin 4) :
    blindGuard h i = decide (i = h.code) := by
  rcases h with ⟨p, q⟩
  cases p <;> cases q <;> fin_cases i <;> decide

private theorem low_trial_enabled (h : HiddenNeed) :
    (prepDecision h).eval (fun _ => true) 1 = !h.morePreparation := by
  rcases h with ⟨p, q⟩
  cases p <;> cases q <;> decide

private theorem high_trial_enabled (h : HiddenNeed) :
    (tryLowPractice h).eval (fun _ => true) 1 = h.morePreparation := by
  rcases h with ⟨p, q⟩
  cases p <;> cases q <;> decide

private def blindActionEffect (final : Snapshot 17) (deliveries : List (Delivery 17))
    (i : Fin 4) (accepted : Bool) : Prop :=
  lessonReceipts deliveries (blindLessonCell i) = (if accepted then (blindCandidate i).cost else 0) ∧
  lessonReceipts deliveries (blindCreditCell i) = (if accepted then 1 else 0) ∧
  (∀ p, final.x (blindCreditCell i) (.z p) = if p = 0 ∧ accepted then 3 / 5 else 0) ∧
  (∀ needs, NativeRetains final (blindLessonCell i) needs ↔
    ((if accepted then blindCandidate i else ⟨0, 0⟩).train needs).retained = true)

private theorem blind_effects {h : HiddenNeed} {final : Snapshot 17} {deliveries : List (Delivery 17)}
    (effects : (blindSearchProgram h).Effects (fun _ => true) (fun i p => final.x i (.z p))
      (lessonReceipts deliveries)) : BlindSelection h final deliveries := by
  simp only [blindSearchProgram, commitFourThree, commitThreeFour, commitThreeThree,
    AdaptiveProgram.Effects] at effects
  obtain ⟨l44, c44, z44, r44, l43, c43, z43, r43, l34, c34, z34, r34, l33, c33, z33, r33, trials⟩ := effects
  have actions (i : Fin 4) : blindActionEffect final deliveries i (blindGuard h i) := by
    fin_cases i
    · exact ⟨l33, c33, z33, r33⟩
    · exact ⟨l34, c34, z34, r34⟩
    · exact ⟨l43, c43, z43, r43⟩
    · exact ⟨l44, c44, z44, r44⟩
  simp only [blindDecisions, highPracticeFailure, chooseThreeFour, lowPracticeFailure, tryBothBranches,
    tryLowPractice, prepDecision, tryPreparation, AdaptiveProgram.Effects] at trials
  obtain ⟨t43, t33, t34, _⟩ := trials
  have small : lessonReceipts deliveries 13 =
      (if (prepDecision h).eval (fun _ => true) 1 then 7 else 0) := t33
  have large : lessonReceipts deliveries 12 =
      (if (tryLowPractice h).eval (fun _ => true) 1 then 8 else 0) := t43
  rw [low_trial_enabled] at small
  rw [high_trial_enabled] at large
  refine ⟨t34, ?_, large, ?_⟩
  · cases hp : h.morePreparation <;> simpa [hp] using small
  · intro i
    have result := actions i
    rw [blind_guard_correct h i] at result
    simpa [blindActionEffect] using result

/-- One previously compiled router recovers the unknown requirement from
physical trials. The selected branch alone receives its minimum lesson
and one credit dose. Complete crossing runs agree on all deliveries. -/
theorem blind_search_recovers_need {θ ε} (box : @PhysicalBox 17 θ ε)
    (time : ℝ) (h : HiddenNeed) :
    let start := (blindSearchLayout time h).start
    let compiled := blindCompiled time
    let T := compiled.last + 76
    ∃ (final : Snapshot 17) (e : Execution θ compiled.route start final)
      (crossing : CrossingExecution θ compiled.route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing T ∧
      BlindSelection h final e.deliveries ∧
      ((blindCandidate h.code).train h.needs).retained = true ∧
      (∀ lesson : Lesson, (lesson.train h.needs).retained = true →
        (blindCandidate h.code).cost ≤ lesson.cost) ∧
      ∀ v (other : CrossingExecution θ compiled.route start v), CrossingCompleteThrough other T →
        ∃ native : Execution θ compiled.route start v, native.toWeak = other.execution ∧
          v.ObservationalEq final ∧ native.deliveries.Perm e.deliveries ∧
          ∀ i, other.execution.emissionTimes i = e.emissionTimes i := by
  let p := blindSearchProgram h
  let layout := blindSearchLayout time h
  let T := (blindCompiled time).last + 76
  have wiring := (blind_search_same_compilation time h ⟨false, false⟩).1
  have sameRoute : layout.route = (blindCompiled time).route := wiring.1
  have sameLast : layout.last = (blindCompiled time).last := wiring.2.2
  have timed : (blindSeedLayout time).WellTimed := by
    refine ⟨?_, fun _ => le_rfl⟩
    change time < time + 66
    linarith
  have later : time + 96 < T := by
    have low := p.layout_last_mono (blindSeedLayout time)
    change time + 66 ≤ layout.last at low
    rw [sameLast] at low
    dsimp [T]
    linarith
  obtain ⟨seed⟩ := blind_seed_exists (p.initial_box box) later
  obtain ⟨run, effects⟩ := p.run seed box timed (by
    change layout.last + 75 < (blindCompiled time).last + 76
    rw [sameLast]
    linarith)
  obtain ⟨crossing, same, done, every⟩ := complete_crossing_accounting run.execution run.complete
    run.positive box run.physical run.initial run.causal
  have minimum := h.minimum_correct
  rw [← h.candidate_is_minimum] at minimum
  dsimp only
  rw [← sameRoute]
  exact ⟨run.final, run.execution, crossing, same, done, blind_effects effects, minimum.1,
    fun lesson retained => (minimum.2 lesson retained).2.2, every⟩


/-- The four-profile search also instantiates the generic tree compiler. -/
noncomputable def blindNeedTree : CalibratedTree HiddenNeed :=
  let prep : CalibratedProbe HiddenNeed :=
    ⟨⟨3, 4⟩, false, prepTrial, fun _ => rfl, fun _ => rfl⟩
  let small : CalibratedProbe HiddenNeed :=
    ⟨⟨3, 3⟩, true, lowPracticeTrial, fun _ => rfl, fun _ => rfl⟩
  let large : CalibratedProbe HiddenNeed :=
    ⟨⟨4, 3⟩, true, highPracticeTrial, fun _ => rfl, fun _ => rfl⟩
  .ask (.lesson prep)
    (.ask (.lesson small) (.leaf ⟨⟨3, 3⟩, 0, by decide⟩) (.leaf ⟨⟨3, 4⟩, 0, by decide⟩))
    (.ask (.lesson large) (.leaf ⟨⟨4, 3⟩, 0, by decide⟩) (.leaf ⟨⟨4, 4⟩, 0, by decide⟩))

theorem blind_need_tree_selects_minimum (h : HiddenNeed) :
    (blindNeedTree.select h).action.lesson = h.minimumLesson := by
  rcases h with ⟨p, q⟩
  cases p <;> cases q <;> rfl

end RecursiveLearning.Native
