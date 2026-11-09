import Lean

namespace RecursiveLearning

inductive Pulse where
  | prepare
  | practice
  deriving DecidableEq, Repr

/-- A learner must finish preparation before practice pulses can contribute. -/
structure Learner where
  preparationLeft : Nat
  practiceLeft : Nat
  deriving DecidableEq, Repr

def Learner.receive (learner : Learner) : Pulse → Learner
  | .prepare => { learner with preparationLeft := learner.preparationLeft - 1 }
  | .practice =>
      if learner.preparationLeft = 0 then
        { learner with practiceLeft := learner.practiceLeft - 1 }
      else learner

def Learner.retained (learner : Learner) : Bool :=
  decide (learner.preparationLeft = 0 ∧ learner.practiceLeft = 0)

structure Lesson where
  preparation : Nat
  practice : Nat
  deriving DecidableEq, Repr

def Lesson.cost (lesson : Lesson) : Nat :=
  lesson.preparation + lesson.practice

def Lesson.train (lesson : Lesson) (learner : Learner) : Learner :=
  let pulses := List.replicate lesson.preparation Pulse.prepare ++
    List.replicate lesson.practice Pulse.practice
  pulses.foldl Learner.receive learner

def Lesson.passes (lesson : Lesson) (learners : List Learner) : Bool :=
  learners.all fun learner => (lesson.train learner).retained

private theorem Learner.preparation_block (count : Nat) (learner : Learner) :
    (List.replicate count Pulse.prepare).foldl Learner.receive learner =
      { learner with preparationLeft := learner.preparationLeft - count } := by
  induction count generalizing learner with
  | zero => simp
  | succ count ih =>
    simp [List.replicate_succ, Learner.receive, ih, Nat.sub_sub, Nat.add_comm]

private theorem Learner.practice_block (count : Nat) (learner : Learner) :
    (List.replicate count Pulse.practice).foldl Learner.receive learner =
      if learner.preparationLeft = 0 then
        { learner with practiceLeft := learner.practiceLeft - count }
      else learner := by
  induction count generalizing learner with
  | zero => split <;> rfl
  | succ count ih =>
    by_cases ready : learner.preparationLeft = 0 <;>
      simp [List.replicate_succ, Learner.receive, ready, ih, Nat.sub_sub, Nat.add_comm]

/-- A lesson retains the skill exactly for learners whose two needs it meets. -/
theorem Lesson.retained_iff (lesson : Lesson) (learner : Learner) :
    (lesson.train learner).retained = true ↔
      learner.preparationLeft ≤ lesson.preparation ∧ learner.practiceLeft ≤ lesson.practice := by
  unfold Lesson.train
  rw [List.foldl_append, Learner.preparation_block, Learner.practice_block]
  by_cases ready : learner.preparationLeft ≤ lesson.preparation
  · have empty : learner.preparationLeft - lesson.preparation = 0 := by omega
    simp [empty, Learner.retained, ready, Nat.sub_eq_zero_iff_le]
  · have nonempty : learner.preparationLeft - lesson.preparation ≠ 0 := by omega
    simp [nonempty, Learner.retained, ready]

/-- The credits count unit doses. The selector records a single persistent
    change of focus from preparation to practice. -/
structure Memory where
  preparationCredit : Nat
  practiceCredit : Nat
  focusOnPractice : Bool
  deriving DecidableEq, Repr

def Memory.used (memory : Memory) : Nat :=
  memory.preparationCredit + memory.practiceCredit

structure Experiment where
  initialLesson : Lesson
  preparationCap : Nat
  practiceCap : Nat
  validation : List Learner

def Experiment.Within (experiment : Experiment) (memory : Memory) : Prop :=
  memory.preparationCredit ≤ experiment.preparationCap ∧
    memory.practiceCredit ≤ experiment.practiceCap

def Experiment.lesson (experiment : Experiment) (memory : Memory) : Lesson :=
  ⟨experiment.initialLesson.preparation - memory.preparationCredit,
    experiment.initialLesson.practice - memory.practiceCredit⟩

def Experiment.propose (experiment : Experiment) (memory : Memory) : Option Memory :=
  if memory.focusOnPractice then
    if memory.practiceCredit < experiment.practiceCap then
      some { memory with practiceCredit := memory.practiceCredit + 1 }
    else none
  else
    if memory.preparationCredit < experiment.preparationCap then
      some { memory with preparationCredit := memory.preparationCredit + 1 }
    else none

def Experiment.accepts (experiment : Experiment) (before trial : Memory) : Bool :=
  let lesson := experiment.lesson trial
  lesson.passes experiment.validation &&
    decide (lesson.cost < (experiment.lesson before).cost)

/-- Test the accepted lesson with one fewer preparation pulse. -/
def Experiment.preparationProbePasses (experiment : Experiment) (trial : Memory) : Bool :=
  let lesson := experiment.lesson trial
  let probe := { lesson with preparation := lesson.preparation - 1 }
  probe.passes experiment.validation

/-- A failed preparation probe supplies the signal that can switch the selector. -/
def Experiment.commit (experiment : Experiment) (adapt : Bool) (trial : Memory) : Memory :=
  { trial with focusOnPractice :=
      trial.focusOnPractice || (adapt && !(experiment.preparationProbePasses trial)) }

/-- One attempted edit. A rejected or capped proposal commits no memory. -/
def Experiment.step (experiment : Experiment) (adapt : Bool) (before : Memory) : Option Memory :=
  (experiment.propose before).bind fun trial =>
    if experiment.accepts before trial then some (experiment.commit adapt trial) else none

private theorem Experiment.proposal_accounting {experiment : Experiment} {before trial : Memory}
    (bounded : experiment.Within before)
    (proposed : experiment.propose before = some trial) :
    experiment.Within trial ∧ trial.used = before.used + 1 := by
  obtain ⟨prepBound, practiceBound⟩ := bounded
  unfold Experiment.propose at proposed
  split at proposed
  · split at proposed
    · rename_i below
      have equal := Option.some.inj proposed
      subst trial
      exact ⟨⟨prepBound, Nat.succ_le_of_lt below⟩, by simp [Memory.used, Nat.add_assoc]⟩
    · contradiction
  · split at proposed
    · rename_i below
      have equal := Option.some.inj proposed
      subst trial
      exact ⟨⟨Nat.succ_le_of_lt below, practiceBound⟩, by simp [Memory.used]; omega⟩
    · contradiction

/-- Every committed edit preserves the caps, consumes exactly one teaching
    credit, retains the validation skill and strictly lowers lesson cost. -/
theorem Experiment.step_contract {experiment : Experiment} {adapt : Bool}
    {before after : Memory} (bounded : experiment.Within before)
    (accepted : experiment.step adapt before = some after) :
    experiment.Within after ∧ after.used = before.used + 1 ∧
      (experiment.lesson after).passes experiment.validation = true ∧
      (experiment.lesson after).cost < (experiment.lesson before).cost := by
  cases proposal : experiment.propose before with
  | none => simp [Experiment.step, proposal] at accepted
  | some trial =>
    by_cases gate : experiment.accepts before trial = true
    · have equal : experiment.commit adapt trial = after := by
        simpa [Experiment.step, proposal, gate] using accepted
      subst after
      obtain ⟨within, credit⟩ := Experiment.proposal_accounting bounded proposal
      have passesAndCost := Bool.and_eq_true_iff.mp gate
      exact ⟨within, credit, passesAndCost.1, of_decide_eq_true passesAndCost.2⟩
    · simp [Experiment.step, proposal, gate] at accepted

/-- A finite sequence of committed improvements. Rejected probes are separate
    observations and do not count as commits. -/
inductive Run (experiment : Experiment) (adapt : Bool) : Memory → Nat → Memory → Prop where
  | nil (memory) : Run experiment adapt memory 0 memory
  | cons (step : experiment.step adapt before = some next)
      (rest : Run experiment adapt next count after) :
      Run experiment adapt before (count + 1) after

theorem Run.accounting {experiment : Experiment} {adapt : Bool} {before after : Memory}
    {count : Nat} (run : Run experiment adapt before count after)
    (bounded : experiment.Within before) :
    experiment.Within after ∧ after.used = before.used + count ∧
      (experiment.lesson after).cost + count ≤ (experiment.lesson before).cost := by
  induction run with
  | nil => simpa using bounded
  | cons accepted _ ih =>
    obtain ⟨nextBounded, nextCredit, _, lower⟩ := Experiment.step_contract bounded accepted
    obtain ⟨endBounded, endCredit, endCost⟩ := ih nextBounded
    exact ⟨endBounded, by omega, by omega⟩

/-- The remaining headroom in the two dose memories bounds the number of
    further strict improvements, for either feedback setting. -/
theorem Run.count_le_remaining {experiment : Experiment} {adapt : Bool}
    {before after : Memory} {count : Nat} (run : Run experiment adapt before count after)
    (bounded : experiment.Within before) :
    count ≤ experiment.preparationCap - before.preparationCredit +
      (experiment.practiceCap - before.practiceCredit) := by
  obtain ⟨endBounded, credit, _⟩ := run.accounting bounded
  obtain ⟨prepStart, practiceStart⟩ := bounded
  obtain ⟨prepEnd, practiceEnd⟩ := endBounded
  unfold Memory.used at credit
  omega

end RecursiveLearning
