import ReusableController.AdaptiveSystem

/-! Executable bounded-error examples. Both report layers have nonzero error;
all objective values come from the actual level-1 search, not a supplied score
table. Finite fuel can stop with a valid nonoptimal lesson. -/
namespace ReusableController.Adaptive.Examples
open RecursiveLearning

def need : Learner := ⟨3, 3⟩
def start : State := initial ⟨4, 8⟩

def oracle : LessonOracle := fun _ lesson => lessonMargin need lesson + 1

def policies (practiceFirst : Bool) : Policy :=
  ⟨practiceFirst, 1, 6, false⟩

def result (p : Bool) : State := executePolicy oracle 1 (policies p) start

def trueCost (p : Bool) : Nat := policyCost oracle 1 start 1 10 (policies p)

def report (p : Bool) : Int := (trueCost p : Int) + if p then -1 else 1

/-- A policy validation pays its complete benchmark, plus one declared
resource unit covering the report and selection action. -/
def charge (p : Bool) : Nat := trueCost p + 1

def menu : PolicyMenu Bool := ⟨false, [true], by decide⟩

def selected : SelectState Bool := selectMenu 1 report charge menu start

theorem oracle_accurate : LessonAccurate need oracle 1 := by
  intro index lesson
  change lessonMargin need lesson - 1 ≤ lessonMargin need lesson + 1 ∧
    lessonMargin need lesson + 1 ≤ lessonMargin need lesson + 1
  omega

theorem oracle_error_nonzero (index : Nat) (lesson : Lesson) :
    oracle index lesson - lessonMargin need lesson = 1 := by
  simp only [oracle]
  omega

theorem cost_reports_accurate : CostAccurate trueCost report 1 := by
  intro p
  cases p <;> decide

theorem policies_fuel (p : Bool) : (policies p).fuel = 6 := by
  cases p <;> rfl

theorem initial_ready : Ready need start := by unfold Ready; decide

theorem preparation_first_result :
    (result false).lesson = ⟨3, 8⟩ ∧
    (result false).trialPulses = 61 ∧
    (result false).attempts = 6 ∧
    (result false).accepted = 1 ∧
    (result false).preparationBlocked = false ∧
    (result false).practiceBlocked = false := by decide

theorem practice_first_result :
    (result true).lesson = ⟨4, 3⟩ ∧
    (result true).trialPulses = 51 ∧
    (result true).attempts = 6 ∧
    (result true).accepted = 5 ∧
    (result true).preparationBlocked = false ∧
    (result true).practiceBlocked = false := by decide

theorem true_costs : trueCost false = 177 ∧ trueCost true = 127 := by decide

theorem reported_costs : report false = 178 ∧ report true = 126 := by decide

theorem both_results_ready (p : Bool) : Ready need (result p) :=
  (policy_search_contract (policies p).fuel oracle_accurate initial_ready).1

/-- The budget theorem applies to the actual run with ambiguity present. -/
theorem policies_within_budget (p : Bool) :
    (result p).attempts ≤ 6 ∧ (result p).trialPulses ≤ 6 * start.lesson.cost := by
  have contract := policy_search_contract (policy := policies p) (policies p).fuel oracle_accurate initial_ready
  have attempts := contract.2.2.2.2.1
  have pulses := contract.2.2.2.2.2
  simpa [result, executePolicy, policies_fuel, start, initial] using And.intro attempts pulses

theorem objective_uniform_bound (p : Bool) : trueCost p ≤ 198 := by
  have bound := policy_cost_bound (policy := policies p) (F := 6) (overhead := 1)
    (deployments := 10) oracle_accurate (show ((⟨4, 8⟩ : Lesson).train need).retained = true by decide)
    (by simp [policies_fuel])
  simpa [trueCost, start, Lesson.cost] using bound

theorem charged_uniform_bound (p : Bool) : charge p ≤ 199 := by
  have bound := objective_uniform_bound p
  unfold charge
  omega

theorem policy_adopted :
    selected.incumbent = true ∧ selected.score = 126 ∧
    selected.adoptions = 1 ∧ selected.trials = 2 ∧
    selected.spent = 306 ∧ selected.pending = [] ∧ selected.live = start := by decide

/-- The adopted policy actually controls the next level-1 search. -/
theorem adopted_policy_executes :
    (executePolicy oracle 1 (policies selected.incumbent) selected.live).lesson = ⟨4, 3⟩ ∧
    (executePolicy oracle 1 (policies selected.incumbent) selected.live).trialPulses = 51 := by decide

theorem selected_true_nondegradation : trueCost selected.incumbent ≤ trueCost menu.seed :=
  selectMenu_trueCost menu start cost_reports_accurate

theorem selected_menu_budget : selected.spent ≤ menu.count * 199 :=
  selectMenu_budget menu start charged_uniform_bound

/-- An episode is the fixed benchmark: policy search plus ten fresh lesson
uses. Repeating episodes amortizes the separately charged policy selection. -/
theorem seven_episodes_amortize :
    selected.spent + 7 * trueCost selected.incumbent ≤ 7 * trueCost menu.seed := by
  apply selection_amortization trueCost (selectInit report charge menu.seed menu.alternatives start)
    selected 7
  · exact selected_true_nondegradation
  · decide

theorem six_episodes_do_not_amortize :
    ¬ (selected.spent + 6 * trueCost selected.incumbent ≤ 6 * trueCost menu.seed) := by decide

/-- Stopping on uncertainty is a policy option, not a false impossibility bit. -/
def stopPolicy : Policy := ⟨false, 1, 6, true⟩

theorem stopping_on_ambiguity :
    (executePolicy oracle 1 stopPolicy start).attempts = 2 ∧
    (executePolicy oracle 1 stopPolicy start).trialPulses = 21 ∧
    (executePolicy oracle 1 stopPolicy start).lesson = ⟨3, 8⟩ ∧
    (executePolicy oracle 1 stopPolicy start).preparationBlocked = false := by decide

def negativeOracle : LessonOracle := fun _ lesson => lessonMargin need lesson - 1

theorem negative_oracle_accurate : LessonAccurate need negativeOracle 1 := by
  intro index lesson
  change lessonMargin need lesson - 1 ≤ lessonMargin need lesson - 1 ∧
    lessonMargin need lesson - 1 ≤ lessonMargin need lesson + 1
  omega

/-- A truly feasible unit candidate can receive a negative reading. It is
unknown at tolerance one; permanently blocking here would break Ready. -/
theorem feasible_negative_reading :
    ((⟨3, 4⟩ : Lesson).train need).retained = true ∧
    negativeOracle 0 ⟨3, 4⟩ = -1 ∧ assess 1 (negativeOracle 0 ⟨3, 4⟩) = .unknown ∧
    (noisyAttempt negativeOracle 1 (initial ⟨4, 4⟩) .preparation).preparationBlocked = false ∧
    (noisyAttempt negativeOracle 1 (initial ⟨4, 4⟩) .preparation).lesson = ⟨4, 4⟩ ∧
    ¬ Ready need (block (initial ⟨4, 4⟩) .preparation) := by unfold Ready; decide

/-- A rejected larger decrement would not justify a unit impossibility bit. -/
theorem bulk_failure_is_not_unit_failure :
    ((⟨2, 4⟩ : Lesson).train need).retained = false ∧
    ((⟨3, 4⟩ : Lesson).train need).retained = true := by decide

/-- At the exact 2τ margin the true cost can tie. -/
theorem margin_two_allows_real_tie :
    selectionAccept 1 11 9 = true ∧
    ((10 : Int) - 1 ≤ 11 ∧ 11 ≤ 10 + 1) ∧
    ((10 : Int) - 1 ≤ 9 ∧ 9 ≤ 10 + 1) ∧
    ¬ (10 : Nat) < 10 := by decide

/-- A margin of only τ permits a worsening policy, while the actual rule
rejects these same accurate reports. -/
theorem margin_one_permits_regression :
    ((10 : Int) - 1 ≤ 11 ∧ 11 ≤ 10 + 1) ∧
    ((11 : Int) - 1 ≤ 10 ∧ 10 ≤ 11 + 1) ∧
    (10 : Int) + 1 ≤ 11 ∧ 10 < 11 ∧
    selectionAccept 1 11 10 = false ∧ (10 : Nat) < 11 := by decide

theorem zero_error_tie_is_rejected : selectionAccept 0 10 10 = false := by decide

def environment : Evaluation Bool where
  need := need
  initialLesson := ⟨4, 8⟩
  oracle := oracle
  lessonTolerance := 1
  policies := policies
  report := report
  costTolerance := 1
  overhead := 1
  deployments := 10
  validationOverhead := 1

theorem environment_sound : environment.Sound :=
  ⟨by decide, oracle_accurate, cost_reports_accurate⟩

def completed : Session environment := adaptAndSearch environment menu

/-- Selection is connected to an actual live search, with both accounts kept. -/
theorem complete_two_level_result :
    completed.memory.incumbent = true ∧ completed.memory.pending = [] ∧
    completed.memory.spent = 306 ∧ completed.memory.trials = 2 ∧
    completed.memory.live.lesson = ⟨4, 3⟩ ∧
    completed.memory.live.trialPulses = 51 ∧ completed.memory.live.attempts = 6 ∧
    completed.memory.spent + completed.memory.live.work 1 = 363 := by decide

theorem complete_two_level_ready : Ready need completed.memory.live :=
  (adapt_and_search_contract environment menu environment_sound).1

theorem complete_two_level_budget :
    completed.memory.spent ≤ 398 ∧ completed.memory.live.attempts ≤ 6 ∧
    completed.memory.live.trialPulses ≤ 72 ∧
    completed.memory.spent + completed.memory.live.work 1 ≤ 476 := by
  exact two_level_budget environment menu environment_sound (F := 6) (fun _ => Nat.le_refl 6)

/-- The live search is the first of the seven amortized episodes. Its ten
lesson uses are charged here, followed by six further fresh episodes. -/
theorem completed_then_six_episodes_amortize :
    completed.memory.spent + completed.memory.live.work 1 +
      10 * completed.memory.live.lesson.cost + 6 * trueCost completed.memory.incumbent ≤
        7 * trueCost menu.seed := by decide

end ReusableController.Adaptive.Examples
