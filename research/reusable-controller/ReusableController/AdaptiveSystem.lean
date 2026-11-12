import ReusableController.NoisySearch
import ReusableController.Selection

/-! Two levels with immutable evaluation parameters. Benchmark trials use
fresh states; adoption never replaces the retained live lesson or its bits. -/
namespace ReusableController.Adaptive
open RecursiveLearning

structure Evaluation (P : Type) where
  need : Learner
  initialLesson : Lesson
  oracle : LessonOracle
  lessonTolerance : Nat
  policies : P → Policy
  report : P → Int
  costTolerance : Nat
  overhead : Nat
  deployments : Nat
  validationOverhead : Nat

def Evaluation.trueCost {P} (fixed : Evaluation P) (p : P) : Nat :=
  policyCost fixed.oracle fixed.lessonTolerance (initial fixed.initialLesson)
    fixed.overhead fixed.deployments (fixed.policies p)

/-- Every validation pays its actual search, declared deployment episodes
and additional measurement/selection overhead, including the baseline. -/
def Evaluation.charge {P} (fixed : Evaluation P) (p : P) : Nat :=
  fixed.trueCost p + fixed.validationOverhead

structure Evaluation.Sound {P} (fixed : Evaluation P) : Prop where
  initial : (fixed.initialLesson.train fixed.need).retained = true
  lessons : LessonAccurate fixed.need fixed.oracle fixed.lessonTolerance
  scores : CostAccurate fixed.trueCost fixed.report fixed.costTolerance

/-- The environment is a type parameter, not a mutable field. A transition
returns Session fixed, so it cannot substitute another evaluation system. -/
structure Session {P : Type} (fixed : Evaluation P) where
  memory : SelectState P

def Session.evaluator {P fixed} (_ : @Session P fixed) : Evaluation P := fixed

def Session.lessonRule {P fixed} (_ : @Session P fixed) : Nat → Int → Verdict := assess

def Session.adoptionRule {P fixed} (_ : @Session P fixed) : Nat → Int → Int → Bool := selectionAccept

def beginSession {P} (fixed : Evaluation P) (menu : PolicyMenu P) : Session fixed :=
  ⟨selectInit fixed.report fixed.charge menu.seed menu.alternatives (initial fixed.initialLesson)⟩

def choosePolicy {P fixed} (s : @Session P fixed) : Session fixed :=
  ⟨selectStep fixed.costTolerance fixed.report fixed.charge s.memory⟩

def searchCurrent {P fixed} (s : @Session P fixed) : Session fixed :=
  ⟨{ s.memory with live := (executePolicy fixed.oracle fixed.lessonTolerance
    (fixed.policies s.memory.incumbent) s.memory.live) }⟩

inductive Action where
  | search | select
  deriving DecidableEq, Repr

def act {P fixed} (action : Action) (s : @Session P fixed) : Session fixed :=
  match action with
  | .search => searchCurrent s
  | .select => choosePolicy s

def actMany {P fixed} : List Action → @Session P fixed → Session fixed
  | [], s => s
  | action :: actions, s => actMany actions (act action s)

/-- Both evaluators and both acceptance rules survive arbitrary action traces.
No identity test on functions, or promise by the policy proposer, is needed. -/
theorem evaluation_immutable {P fixed} (actions : List Action) (s : @Session P fixed) :
    (actMany actions s).evaluator = s.evaluator ∧
    (actMany actions s).lessonRule = s.lessonRule ∧
    (actMany actions s).adoptionRule = s.adoptionRule := ⟨rfl, rfl, rfl⟩

theorem act_invariants {P fixed} (action : Action) (s : @Session P fixed)
    (sound : fixed.Sound) (ready : Ready fixed.need s.memory.live) :
    Ready fixed.need (act action s).memory.live ∧
      (s.memory.live.preparationBlocked = true → (act action s).memory.live.preparationBlocked = true) ∧
      (s.memory.live.practiceBlocked = true → (act action s).memory.live.practiceBlocked = true) := by
  cases action with
  | select =>
    simpa only [act, choosePolicy, selectStep_live] using
      (show Ready fixed.need s.memory.live ∧
        (s.memory.live.preparationBlocked = true → s.memory.live.preparationBlocked = true) ∧
        (s.memory.live.practiceBlocked = true → s.memory.live.practiceBlocked = true) from ⟨ready, id, id⟩)
  | search =>
    have result := policy_search_contract (policy := fixed.policies s.memory.incumbent)
      (fixed.policies s.memory.incumbent).fuel sound.lessons ready
    exact ⟨result.1, result.2.1, result.2.2.1⟩

theorem any_policy_history_safe {P fixed} (actions : List Action) (s : @Session P fixed)
    (sound : fixed.Sound) (ready : Ready fixed.need s.memory.live) :
    Ready fixed.need (actMany actions s).memory.live ∧
      (s.memory.live.preparationBlocked = true → (actMany actions s).memory.live.preparationBlocked = true) ∧
      (s.memory.live.practiceBlocked = true → (actMany actions s).memory.live.practiceBlocked = true) := by
  induction actions generalizing s with
  | nil => exact ⟨ready, id, id⟩
  | cons action actions ih =>
    obtain ⟨next, bp, bq⟩ := act_invariants action s sound ready
    obtain ⟨final, fp, fq⟩ := ih (act action s) next
    exact ⟨final, fun h => fp (bp h), fun h => fq (bq h)⟩

theorem act_cache {P fixed} (action : Action) (s : @Session P fixed)
    (cache : s.memory.score = fixed.report s.memory.incumbent) :
    (act action s).memory.score = fixed.report (act action s).memory.incumbent := by
  cases action with
  | search => exact cache
  | select => exact selectStep_cache _ _ _ cache

theorem any_policy_history_cost {P fixed} (actions : List Action) (s : @Session P fixed)
    (sound : fixed.Sound) (cache : s.memory.score = fixed.report s.memory.incumbent) :
    fixed.trueCost (actMany actions s).memory.incumbent ≤ fixed.trueCost s.memory.incumbent := by
  induction actions generalizing s with
  | nil => exact Nat.le_refl _
  | cons action actions ih =>
    have next := ih (act action s) (act_cache action s cache)
    apply Nat.le_trans next
    cases action with
    | search => exact Nat.le_refl _
    | select => exact selectStep_trueCost sound.scores cache

def selectAll {P fixed} (s : @Session P fixed) : Session fixed :=
  ⟨selectFinish fixed.costTolerance fixed.report fixed.charge s.memory⟩

/-- A complete finite two-level operation: evaluate the menu, adopt safely,
then actually search using the retained policy on the unchanged live state. -/
def adaptAndSearch {P} (fixed : Evaluation P) (menu : PolicyMenu P) : Session fixed :=
  searchCurrent (selectAll (beginSession fixed menu))

theorem adapt_and_search_contract {P} (fixed : Evaluation P) (menu : PolicyMenu P)
    (sound : fixed.Sound) :
    Ready fixed.need (adaptAndSearch fixed menu).memory.live ∧
    (adaptAndSearch fixed menu).memory.pending = [] ∧
    (adaptAndSearch fixed menu).memory.trials = menu.count ∧
    (adaptAndSearch fixed menu).memory.incumbent ∈ menu.seed :: menu.alternatives ∧
    fixed.trueCost (adaptAndSearch fixed menu).memory.incumbent ≤ fixed.trueCost menu.seed := by
  have live : (selectAll (beginSession fixed menu)).memory.live = initial fixed.initialLesson :=
    selectRun_live _ _ _ _ _
  have ready : Ready fixed.need (selectAll (beginSession fixed menu)).memory.live := by
    rw [live]
    exact initial_ready sound.initial
  exact ⟨(act_invariants .search (selectAll (beginSession fixed menu)) sound ready).1,
    selectFinish_exhausted _ _ _ _, selectMenu_trials _ _ _ menu _,
    selectMenu_member _ _ _ menu _, selectMenu_trueCost menu _ sound.scores⟩

def Evaluation.validationBound {P} (fixed : Evaluation P) (F : Nat) : Nat :=
  F * fixed.initialLesson.cost + fixed.overhead * F +
    fixed.deployments * fixed.initialLesson.cost + fixed.validationOverhead

theorem Evaluation.charge_bounded {P} {fixed : Evaluation P} (sound : fixed.Sound) {F : Nat}
    (fuel : ∀ p, (fixed.policies p).fuel ≤ F) (p : P) : fixed.charge p ≤ fixed.validationBound F :=
  Nat.add_le_add_right (policy_cost_bound sound.lessons sound.initial (fuel p)) _

/-- Selection and live-search budgets are separate. This includes the
incumbent's initial validation, every rejected trial and every ambiguous
lesson trial; no saving is credited before it has been paid for. -/
theorem two_level_budget {P} (fixed : Evaluation P) (menu : PolicyMenu P)
    (sound : fixed.Sound) {F : Nat} (fuel : ∀ p, (fixed.policies p).fuel ≤ F) :
    (adaptAndSearch fixed menu).memory.spent ≤ menu.count * fixed.validationBound F ∧
    (adaptAndSearch fixed menu).memory.live.attempts ≤ F ∧
    (adaptAndSearch fixed menu).memory.live.trialPulses ≤ F * fixed.initialLesson.cost ∧
    (adaptAndSearch fixed menu).memory.spent +
      (adaptAndSearch fixed menu).memory.live.work fixed.overhead ≤
        menu.count * fixed.validationBound F +
          F * fixed.initialLesson.cost + fixed.overhead * F := by
  have budget := selectMenu_budget (tau := fixed.costTolerance) (report := fixed.report)
    menu (initial fixed.initialLesson) (Evaluation.charge_bounded sound fuel)
  let selected := selectAll (beginSession fixed menu)
  have live : selected.memory.live = initial fixed.initialLesson := selectRun_live _ _ _ _ _
  have ready : Ready fixed.need selected.memory.live := by rw [live]; exact initial_ready sound.initial
  obtain ⟨_, _, _, _, tries, pulses⟩ :=
    policy_search_contract (policy := fixed.policies selected.memory.incumbent)
      (fixed.policies selected.memory.incumbent).fuel sound.lessons ready
  have triesBound : (adaptAndSearch fixed menu).memory.live.attempts ≤ F := by
    exact Nat.le_trans tries (by rw [live]; simpa [initial] using fuel selected.memory.incumbent)
  have pulsesBound : (adaptAndSearch fixed menu).memory.live.trialPulses ≤ F * fixed.initialLesson.cost := by
    apply Nat.le_trans pulses
    rw [live]
    simpa only [initial, Nat.zero_add] using
      Nat.mul_le_mul_right fixed.initialLesson.cost (fuel selected.memory.incumbent)
  refine ⟨budget, triesBound, pulsesBound, ?_⟩
  have work := Nat.add_le_add pulsesBound (Nat.mul_le_mul_left fixed.overhead triesBound)
  have total := Nat.add_le_add budget work
  simpa only [State.work, Nat.add_assoc, adaptAndSearch, searchCurrent, selectAll,
    beginSession, selectMenu] using total

end ReusableController.Adaptive
