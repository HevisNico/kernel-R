import ReusableController.Proofs

/-! Discrete bounded-error search. A report is a signed, quantized feasibility
margin. Ambiguity costs a trial but never manufactures a permanent block.
Policies group validated unit edits into bounded batches; they do not infer
unit infeasibility from failure of an unchecked larger decrement. -/
namespace ReusableController.Adaptive
open RecursiveLearning

abbrev LessonOracle := Nat → Lesson → Int

def lessonMargin (need : Learner) (lesson : Lesson) : Int :=
  min ((lesson.preparation : Int) - need.preparationLeft)
    ((lesson.practice : Int) - need.practiceLeft)

def LessonAccurate (need : Learner) (oracle : LessonOracle) (tau : Nat) : Prop :=
  ∀ index lesson, lessonMargin need lesson - (tau : Int) ≤ oracle index lesson ∧
    oracle index lesson ≤ lessonMargin need lesson + (tau : Int)

theorem margin_retained (need : Learner) (lesson : Lesson) :
    0 ≤ lessonMargin need lesson ↔ (lesson.train need).retained = true := by
  rw [lesson.retained_iff]
  unfold lessonMargin
  omega

inductive Verdict where
  | pass | fail | unknown
  deriving DecidableEq, Repr

def assess (tau : Nat) (reading : Int) : Verdict :=
  if (tau : Int) ≤ reading then .pass
  else if reading + (tau : Int) < 0 then .fail else .unknown

theorem assess_pass_sound {need oracle tau index lesson}
    (accurate : LessonAccurate need oracle tau)
    (pass : assess tau (oracle index lesson) = .pass) :
    (lesson.train need).retained = true := by
  apply (margin_retained need lesson).mp
  have bound := accurate index lesson
  simp only [assess] at pass
  split at pass
  · omega
  · split at pass <;> contradiction

theorem assess_fail_sound {need oracle tau index lesson}
    (accurate : LessonAccurate need oracle tau)
    (fail : assess tau (oracle index lesson) = .fail) :
    (lesson.train need).retained = false := by
  have negative : lessonMargin need lesson < 0 := by
    have bound := accurate index lesson
    simp only [assess] at fail
    split at fail
    · contradiction
    · split at fail
      · omega
      · contradiction
  cases result : (lesson.train need).retained with
  | false => rfl
  | true => have := (margin_retained need lesson).mpr result; omega

/-- The oracle and tolerance are arguments, never fields of the mutable
controller state. A unit failure may block; an uncertain reading may not. -/
def noisyAttempt (oracle : LessonOracle) (tau : Nat) (s : State) (axis : Axis) : State :=
  let tried := { s with attempts := s.attempts + 1 }
  match candidate s.lesson axis with
  | none => block tried axis
  | some lesson =>
    let tested := { tried with trialPulses := s.trialPulses + lesson.cost }
    match assess tau (oracle s.attempts lesson) with
    | .pass => commit tested lesson axis
    | .fail => block tested axis
    | .unknown => tested

def ambiguous (oracle : LessonOracle) (tau : Nat) (s : State) (axis : Axis) : Bool :=
  match candidate s.lesson axis with
  | none => false
  | some lesson => decide (assess tau (oracle s.attempts lesson) = .unknown)

theorem unknown_preserves_memory {oracle tau s axis lesson}
    (proposed : candidate s.lesson axis = some lesson)
    (unknown : assess tau (oracle s.attempts lesson) = .unknown) :
    (noisyAttempt oracle tau s axis).lesson = s.lesson ∧
    (noisyAttempt oracle tau s axis).preparationBlocked = s.preparationBlocked ∧
    (noisyAttempt oracle tau s axis).practiceBlocked = s.practiceBlocked ∧
    (noisyAttempt oracle tau s axis).trialPulses = s.trialPulses + lesson.cost := by
  simp [noisyAttempt, proposed, unknown]

theorem noisy_flags_monotone (oracle tau s axis) :
    (s.preparationBlocked = true → (noisyAttempt oracle tau s axis).preparationBlocked = true) ∧
    (s.practiceBlocked = true → (noisyAttempt oracle tau s axis).practiceBlocked = true) := by
  cases proposed : candidate s.lesson axis with
  | none => cases axis <;> simp [noisyAttempt, proposed, block]
  | some lesson =>
    cases decision : assess tau (oracle s.attempts lesson) <;>
      cases axis <;> simp [noisyAttempt, proposed, decision, block, commit]

private theorem candidate_cost_le {before after : Lesson} {axis : Axis}
    (proposed : candidate before axis = some after) : after.cost ≤ before.cost := by
  cases axis <;> simp only [candidate] at proposed
  all_goals
    split at proposed
    · contradiction
    · have equal := Option.some.inj proposed
      rw [← equal]
      simp only [Lesson.cost]
      omega

theorem noisy_attempt_contract {need oracle tau s axis}
    (accurate : LessonAccurate need oracle tau) (ready : Ready need s)
    (available : Unblocked s axis) :
    Ready need (noisyAttempt oracle tau s axis) ∧
    (noisyAttempt oracle tau s axis).lesson.cost ≤ s.lesson.cost ∧
    (noisyAttempt oracle tau s axis).attempts = s.attempts + 1 ∧
    s.trialPulses ≤ (noisyAttempt oracle tau s axis).trialPulses ∧
    (noisyAttempt oracle tau s axis).trialPulses ≤ s.trialPulses + s.lesson.cost ∧
    (noisyAttempt oracle tau s axis).lesson.cost + (noisyAttempt oracle tau s axis).accepted =
      s.lesson.cost + s.accepted := by
  have original := attempt_contract ready available
  have transfer (same : noisyAttempt oracle tau s axis = attempt need s axis) :
      Ready need (noisyAttempt oracle tau s axis) ∧
      (noisyAttempt oracle tau s axis).lesson.cost ≤ s.lesson.cost ∧
      (noisyAttempt oracle tau s axis).attempts = s.attempts + 1 ∧
      s.trialPulses ≤ (noisyAttempt oracle tau s axis).trialPulses ∧
      (noisyAttempt oracle tau s axis).trialPulses ≤ s.trialPulses + s.lesson.cost ∧
      (noisyAttempt oracle tau s axis).lesson.cost + (noisyAttempt oracle tau s axis).accepted =
        s.lesson.cost + s.accepted := by
    rw [same]
    obtain ⟨ok, account, tries, _, lower, upper, prep, prac⟩ := original
    exact ⟨ok, Nat.add_le_add prep prac, tries, lower, upper, account⟩
  cases proposed : candidate s.lesson axis with
  | none => exact transfer (by simp [noisyAttempt, attempt, proposed])
  | some lesson =>
    cases decision : assess tau (oracle s.attempts lesson) with
    | pass => exact transfer (by simp [noisyAttempt, attempt, proposed, decision,
        assess_pass_sound accurate decision])
    | fail => exact transfer (by simp [noisyAttempt, attempt, proposed, decision,
        assess_fail_sound accurate decision])
    | unknown =>
      have candidateCost := candidate_cost_le proposed
      simp only [noisyAttempt, proposed, decision]
      exact ⟨ready, Nat.le_refl _, trivial, Nat.le_add_right _ _, Nat.add_le_add_left candidateCost _, trivial⟩

/-- `step` is a batch of individually validated unit probes. `rounds` limits
those batches. Stopping on ambiguity does not mark a coordinate impossible. -/
structure Policy where
  practiceFirst : Bool
  step : Nat
  rounds : Nat
  stopOnAmbiguity : Bool
  deriving DecidableEq, Repr

def Policy.fuel (policy : Policy) : Nat := policy.step * policy.rounds

def policyChoose (policy : Policy) (s : State) : Option Axis :=
  if policy.practiceFirst then
    if s.practiceBlocked then
      if s.preparationBlocked then none else some .preparation
    else some .practice
  else s.choose

theorem policy_choose_unblocked {policy s axis} (chosen : policyChoose policy s = some axis) :
    Unblocked s axis := by
  cases policy with
  | mk first step rounds stop =>
    cases s with
    | mk lesson pb qb tries accepted pulses =>
      cases first <;> cases pb <;> cases qb <;> cases axis <;>
        simp_all [policyChoose, State.choose, Unblocked]

def policySearch (oracle : LessonOracle) (tau : Nat) (policy : Policy) : Nat → State → State
  | 0, s => s
  | fuel + 1, s =>
    match policyChoose policy s with
    | none => s
    | some axis =>
      let next := noisyAttempt oracle tau s axis
      if policy.stopOnAmbiguity && ambiguous oracle tau s axis then next
      else policySearch oracle tau policy fuel next

def executePolicy (oracle : LessonOracle) (tau : Nat) (policy : Policy) (s : State) : State :=
  policySearch oracle tau policy policy.fuel s

/-- Soundness does not assume that reports are decisive or that policies
make progress on each attempt. Fuel is consumed even on ambiguity. -/
theorem policy_search_contract {need oracle tau policy} (fuel : Nat) {s}
    (accurate : LessonAccurate need oracle tau) (ready : Ready need s) :
    Ready need (policySearch oracle tau policy fuel s) ∧
    (s.preparationBlocked = true → (policySearch oracle tau policy fuel s).preparationBlocked = true) ∧
    (s.practiceBlocked = true → (policySearch oracle tau policy fuel s).practiceBlocked = true) ∧
    (policySearch oracle tau policy fuel s).lesson.cost ≤ s.lesson.cost ∧
    (policySearch oracle tau policy fuel s).attempts ≤ s.attempts + fuel ∧
    (policySearch oracle tau policy fuel s).trialPulses ≤ s.trialPulses + fuel * s.lesson.cost := by
  induction fuel generalizing s with
  | zero => simp [policySearch]; exact ready
  | succ fuel ih =>
    cases chosen : policyChoose policy s with
    | none => simpa [policySearch, chosen] using ready
    | some axis =>
      obtain ⟨ok, cost, tries, _, pulses, _⟩ := noisy_attempt_contract accurate ready
        (policy_choose_unblocked chosen)
      have flags := noisy_flags_monotone oracle tau s axis
      simp only [policySearch, chosen]
      split
      · refine ⟨ok, flags.1, flags.2, cost, by omega, ?_⟩
        rw [Nat.succ_mul]
        omega
      · obtain ⟨endOK, fp, fq, endCost, endTries, endPulses⟩ := ih ok
        have bound := Nat.mul_le_mul_left fuel cost
        refine ⟨endOK, fun h => fp (flags.1 h), fun h => fq (flags.2 h),
          Nat.le_trans endCost cost, by omega, ?_⟩
        rw [Nat.succ_mul]
        omega

/-- A fixed benchmark includes all search trials and a declared number of
fresh deployments of the retained valid lesson. It is not a hardware bound. -/
def policyCost (oracle : LessonOracle) (tau : Nat) (start : State)
    (overhead deployments : Nat) (policy : Policy) : Nat :=
  let final := executePolicy oracle tau policy start
  final.work overhead + deployments * final.lesson.cost


theorem policy_cost_bound {need oracle tau policy lesson F overhead deployments}
    (accurate : LessonAccurate need oracle tau)
    (passes : (lesson.train need).retained = true) (fuel : policy.fuel ≤ F) :
    policyCost oracle tau (initial lesson) overhead deployments policy ≤
      F * lesson.cost + overhead * F + deployments * lesson.cost := by
  obtain ⟨_, _, _, cost, tries, pulses⟩ :=
    policy_search_contract policy.fuel accurate (initial_ready passes)
  have bound := Nat.mul_le_mul_right lesson.cost fuel
  have htries : (executePolicy oracle tau policy (initial lesson)).attempts ≤ F := by
    exact Nat.le_trans tries (by simpa [initial] using fuel)
  have hpulses : (executePolicy oracle tau policy (initial lesson)).trialPulses ≤ F * lesson.cost := by
    exact Nat.le_trans pulses (by simpa [initial] using bound)
  exact Nat.add_le_add
    (Nat.add_le_add hpulses (Nat.mul_le_mul_left overhead htries))
    (Nat.mul_le_mul_left deployments cost)

end ReusableController.Adaptive
