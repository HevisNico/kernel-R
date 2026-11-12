import ReusableController.AdaptiveSystem

/-! A second fixed benchmark: periodic signed error, four order/stop policies,
and a short deployment horizon. Early stopping wins despite a larger retained
lesson. This is not a coordinate exchange of the first benchmark. -/
namespace ReusableController.Adaptive.SecondBenchmark
open RecursiveLearning

inductive Choice where
  | practiceContinue | preparationContinue | practiceStop | preparationStop
  deriving DecidableEq, Repr

def need : Learner := ⟨2, 3⟩
def start : State := initial ⟨10, 6⟩

/-- The error changes sign with the attempt index, including retries. -/
def oracle : LessonOracle := fun index lesson =>
  lessonMargin need lesson + if index % 3 = 0 then -1 else 1

def policies : Choice → Policy
  | .practiceContinue => ⟨true, 3, 4, false⟩
  | .preparationContinue => ⟨false, 3, 4, false⟩
  | .practiceStop => ⟨true, 3, 4, true⟩
  | .preparationStop => ⟨false, 3, 4, true⟩

def result (p : Choice) : State := executePolicy oracle 1 (policies p) start
def trueCost (p : Choice) : Nat := policyCost oracle 1 start 2 2 (policies p)

/-- All reports have nonzero error; the winning policy is overestimated. -/
def report (p : Choice) : Int :=
  (trueCost p : Int) + if p = .preparationStop then 1 else -1

def charge (p : Choice) : Nat := trueCost p + 3

def menu : PolicyMenu Choice :=
  ⟨.practiceContinue, [.preparationContinue, .practiceStop, .preparationStop], by decide⟩

theorem menu_covers_family (p : Choice) : p ∈ menu.seed :: menu.alternatives := by
  cases p <;> decide

theorem oracle_accurate : LessonAccurate need oracle 1 := by
  intro index lesson
  unfold oracle
  split <;> omega

theorem oracle_error_nonzero (index : Nat) (lesson : Lesson) :
    oracle index lesson ≠ lessonMargin need lesson := by
  unfold oracle
  split <;> omega

theorem oracle_error_changes_sign (lesson : Lesson) :
    oracle 0 lesson - lessonMargin need lesson = -1 ∧
    oracle 1 lesson - lessonMargin need lesson = 1 ∧
    oracle 2 lesson - lessonMargin need lesson = 1 := by
  simp [oracle]
  omega

theorem cost_reports_accurate : CostAccurate trueCost report 1 := by
  intro p
  cases p <;> decide

theorem cost_report_error_nonzero (p : Choice) : report p ≠ (trueCost p : Int) := by
  cases p <;> decide

theorem policies_fuel (p : Choice) : (policies p).fuel = 12 := by
  cases p <;> rfl

theorem initial_ready : Ready need start := by unfold Ready; decide

theorem all_results_ready (p : Choice) : Ready need (result p) :=
  (policy_search_contract (policies p).fuel oracle_accurate initial_ready).1

theorem practice_continue_result :
    (result .practiceContinue).lesson = ⟨4, 3⟩ ∧
    (result .practiceContinue).trialPulses = 129 ∧
    (result .practiceContinue).attempts = 12 ∧
    (result .practiceContinue).accepted = 9 ∧
    (result .practiceContinue).preparationBlocked = false ∧
    (result .practiceContinue).practiceBlocked = true := by decide

theorem preparation_continue_result :
    (result .preparationContinue).lesson = ⟨2, 4⟩ ∧
    (result .preparationContinue).trialPulses = 121 ∧
    (result .preparationContinue).attempts = 12 ∧
    (result .preparationContinue).accepted = 10 ∧
    (result .preparationContinue).preparationBlocked = true ∧
    (result .preparationContinue).practiceBlocked = false := by decide

theorem practice_stop_result :
    (result .practiceStop).lesson = ⟨8, 3⟩ ∧
    (result .practiceStop).trialPulses = 87 ∧
    (result .practiceStop).attempts = 7 ∧
    (result .practiceStop).accepted = 5 ∧
    (result .practiceStop).preparationBlocked = false ∧
    (result .practiceStop).practiceBlocked = true := by decide

theorem preparation_stop_result :
    (result .preparationStop).lesson = ⟨4, 6⟩ ∧
    (result .preparationStop).trialPulses = 84 ∧
    (result .preparationStop).attempts = 7 ∧
    (result .preparationStop).accepted = 6 ∧
    (result .preparationStop).preparationBlocked = false ∧
    (result .preparationStop).practiceBlocked = false := by decide

/-- The seventh probe is feasible but indeterminate, and remains paid. -/
theorem winning_stop_is_ambiguous :
    ((⟨3, 6⟩ : Lesson).train need).retained = true ∧
    oracle 6 ⟨3, 6⟩ = 0 ∧ assess 1 (oracle 6 ⟨3, 6⟩) = .unknown ∧
    (result .preparationStop).trialPulses = 15 + 14 + 13 + 12 + 11 + 10 + 9 := by decide

theorem true_costs :
    trueCost .practiceContinue = 167 ∧ trueCost .preparationContinue = 157 ∧
    trueCost .practiceStop = 123 ∧ trueCost .preparationStop = 118 := by decide

theorem reported_costs :
    report .practiceContinue = 166 ∧ report .preparationContinue = 156 ∧
    report .practiceStop = 122 ∧ report .preparationStop = 119 := by decide

theorem validation_charges :
    charge .practiceContinue = 170 ∧ charge .preparationContinue = 160 ∧
    charge .practiceStop = 126 ∧ charge .preparationStop = 121 := by decide

/-- Stopping saves more search work than it adds to two subsequent uses. -/
theorem stopping_tradeoff :
    (result .preparationContinue).work 2 = 145 ∧
    (result .preparationStop).work 2 = 98 ∧
    (result .preparationContinue).lesson.cost = 6 ∧
    (result .preparationStop).lesson.cost = 10 ∧
    trueCost .preparationStop < trueCost .preparationContinue := by decide

theorem winner_strictly_best (p : Choice) (different : p ≠ .preparationStop) :
    trueCost .preparationStop < trueCost p := by
  cases p <;> first | decide | exact False.elim (different rfl)

def environment : Evaluation Choice where
  need := need
  initialLesson := ⟨10, 6⟩
  oracle := oracle
  lessonTolerance := 1
  policies := policies
  report := report
  costTolerance := 1
  overhead := 2
  deployments := 2
  validationOverhead := 3

theorem environment_sound : environment.Sound :=
  ⟨by decide, oracle_accurate, cost_reports_accurate⟩

def selected : SelectState Choice := selectMenu 1 report charge menu start
def completed : Session environment := adaptAndSearch environment menu

theorem selection_result :
    selected.incumbent = .preparationStop ∧ selected.score = 119 ∧
    selected.adoptions = 3 ∧ selected.trials = 4 ∧
    selected.spent = 577 ∧ selected.pending = [] ∧ selected.live = start := by decide

theorem selected_true_nondegradation : trueCost selected.incumbent ≤ trueCost menu.seed :=
  selectMenu_trueCost menu start cost_reports_accurate

theorem complete_two_level_result :
    completed.memory.incumbent = .preparationStop ∧ completed.memory.pending = [] ∧
    completed.memory.spent = 577 ∧ completed.memory.trials = 4 ∧
    completed.memory.adoptions = 3 ∧ completed.memory.live.lesson = ⟨4, 6⟩ ∧
    completed.memory.live.trialPulses = 84 ∧ completed.memory.live.attempts = 7 ∧
    completed.memory.spent + completed.memory.live.work 2 = 675 := by decide

theorem complete_two_level_ready : Ready need completed.memory.live :=
  (adapt_and_search_contract environment menu environment_sound).1

theorem complete_two_level_budget :
    completed.memory.spent ≤ 1004 ∧ completed.memory.live.attempts ≤ 12 ∧
    completed.memory.live.trialPulses ≤ 192 ∧
    completed.memory.spent + completed.memory.live.work 2 ≤ 1220 := by
  exact two_level_budget environment menu environment_sound (F := 12)
    (fun p => Nat.le_of_eq (policies_fuel p))

theorem twelve_episodes_amortize :
    selected.spent + 12 * trueCost selected.incumbent ≤ 12 * trueCost menu.seed := by
  apply selection_amortization trueCost
    (selectInit report charge menu.seed menu.alternatives start) selected 12
  · exact selected_true_nondegradation
  · decide

theorem eleven_episodes_do_not_amortize :
    ¬ (selected.spent + 11 * trueCost selected.incumbent ≤ 11 * trueCost menu.seed) := by decide

theorem amortization_exact_threshold (episodes : Nat) :
    (selected.spent + episodes * trueCost selected.incumbent ≤ episodes * trueCost menu.seed) ↔
      12 ≤ episodes := by
  change (577 + episodes * 118 ≤ episodes * 167) ↔ 12 ≤ episodes
  omega

/-- The live search belongs to the first amortized episode. Include its two
lesson uses, then eleven further complete search-and-deployment episodes. -/
theorem completed_then_eleven_episodes_amortize :
    completed.memory.spent + completed.memory.live.work 2 +
      2 * completed.memory.live.lesson.cost + 11 * trueCost completed.memory.incumbent = 1993 ∧
    12 * trueCost menu.seed = 2004 ∧
    completed.memory.spent + completed.memory.live.work 2 +
      2 * completed.memory.live.lesson.cost + 11 * trueCost completed.memory.incumbent ≤
        12 * trueCost menu.seed := by decide

/-- A changed deployment horizon is a different benchmark and requires its
own validation. At twenty uses, the previous early-stop winner loses. -/
def longerHorizonCost (p : Choice) : Nat := policyCost oracle 1 start 2 20 (policies p)

theorem longer_horizon_costs :
    longerHorizonCost .practiceContinue = 293 ∧
    longerHorizonCost .preparationContinue = 265 ∧
    longerHorizonCost .practiceStop = 321 ∧
    longerHorizonCost .preparationStop = 298 := by decide

theorem longer_horizon_winner (p : Choice) (different : p ≠ .preparationContinue) :
    longerHorizonCost .preparationContinue < longerHorizonCost p := by
  cases p <;> first | decide | exact False.elim (different rfl)

end ReusableController.Adaptive.SecondBenchmark
