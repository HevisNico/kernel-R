import RecursiveLearning.Model

/-! A reusable DISCRETE controller. No native R execution is asserted here.
The evaluator is the upstream learner, unchanged. Each attempt trains a fresh
copy of that learner. The controller retains its lesson and search state.
Rejected coordinates are remembered; a rejection does not end the search.
-/
namespace ReusableController
open RecursiveLearning

inductive Axis where
  | preparation | practice
  deriving DecidableEq, Repr

structure State where
  lesson : Lesson
  preparationBlocked : Bool := false
  practiceBlocked : Bool := false
  attempts : Nat := 0
  accepted : Nat := 0
  trialPulses : Nat := 0
  deriving DecidableEq, Repr

def State.halted (s : State) : Bool := s.preparationBlocked && s.practiceBlocked

/-- Fixed order: exhaust preparation edits, then practice edits. Only the two
blocked bits change, and each changes from false to true at most once. No
reversible selector write is hidden in this discrete design. -/
def State.choose (s : State) : Option Axis :=
  if s.preparationBlocked then
    if s.practiceBlocked then none else some .practice
  else some .preparation

def candidate (lesson : Lesson) : Axis → Option Lesson
  | .preparation => if lesson.preparation = 0 then none
      else some { lesson with preparation := lesson.preparation - 1 }
  | .practice => if lesson.practice = 0 then none
      else some { lesson with practice := lesson.practice - 1 }

def block (s : State) : Axis → State
  | .preparation => { s with preparationBlocked := true }
  | .practice => { s with practiceBlocked := true }

def commit (s : State) (trial : Lesson) : Axis → State
  | .preparation => { s with lesson := trial, accepted := s.accepted + 1 }
  | .practice => { s with lesson := trial, accepted := s.accepted + 1 }

/-- An unavailable decrement still uses one controller attempt, but no learner
pulses. Every actual validation pays the entire candidate lesson, even on failure.
No held-out learner or future accepted lesson is used by this transition. -/
def attempt (need : Learner) (s : State) (axis : Axis) : State :=
    let tried := { s with attempts := s.attempts + 1 }
    match candidate s.lesson axis with
    | none => block tried axis
    | some lesson =>
      let tested := { tried with trialPulses := s.trialPulses + lesson.cost }
      if (lesson.train need).retained then commit tested lesson axis
      else block tested axis

def round (need : Learner) (s : State) : State :=
  match s.choose with
  | none => s
  | some axis => attempt need s axis

/-- The reusable invariant includes soundness of the blocked-coordinate memory.
It is true initially for any lesson meeting both requirements. -/
def Ready (need : Learner) (s : State) : Prop :=
  need.preparationLeft ≤ s.lesson.preparation ∧
  need.practiceLeft ≤ s.lesson.practice ∧
  (s.preparationBlocked = true → s.lesson.preparation ≤ need.preparationLeft) ∧
  (s.practiceBlocked = true → s.lesson.practice ≤ need.practiceLeft)

def initial (lesson : Lesson) : State := ⟨lesson, false, false, 0, 0, 0⟩

def State.potential (s : State) : Nat :=
  s.lesson.cost + (if s.preparationBlocked then 0 else 1) +
    (if s.practiceBlocked then 0 else 1)

/-- Counted resource units. `overhead` must include the chosen accounting cost
of proposals, reports, writes and reset; it is not a measured circuit bound. -/
def State.work (s : State) (overhead : Nat) : Nat :=
  s.trialPulses + overhead * s.attempts

def run (need : Learner) : Nat → State → State
  | 0, s => s
  | n + 1, s => run need n (round need s)

end ReusableController
