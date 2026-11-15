import Lean

/-! Phase 0 for pattern recognition by learned coincidence. The theorem is a
proposition. The examples evaluate the parameter checker and the predictor. -/
namespace LearnedCoincidence

abbrev Pattern (M : Nat) := Fin M → Bool

def pattern (ports : List (Fin M)) : Pattern M := fun j => ports.contains j

def contains (read target : Pattern M) : Bool :=
  (List.finRange M).all fun j => !target j || read j

def proper (small large : Pattern M) : Bool := contains large small && !contains small large

def incomparable (a b : Pattern M) : Bool := !contains a b && !contains b a

def card (x : Pattern M) : Nat := ((List.finRange M).filter x).length

/-- The largest read that omits port j. -/
def omits (j : Fin M) : Pattern M := fun k => decide (k ≠ j)

structure Parameters (N M : Nat) where
  target : Fin N → Pattern M
  tests : List (Pattern M)
  initialGain : Fin N → Fin M → Nat
  help : Fin N → Nat
  threshold : Fin N → Nat
  trainingError : Fin N → Nat
  testingError : Fin N → Nat
  dose : Nat
  maxWrites : Nat
  rail : Nat

/-- One silent training round writes once on each active target port. -/
def portWrites (p : Parameters N M) (i : Fin N) (j : Fin M) (silentRounds : Nat) : Nat :=
  if p.target i j then silentRounds else 0

def gain (p : Parameters N M) (i : Fin N) (silentRounds : Nat) (j : Fin M) : Nat :=
  p.initialGain i j + p.dose * portWrites p i j silentRounds

def score (p : Parameters N M) (i : Fin N) (silentRounds : Nat) (x : Pattern M) : Nat :=
  p.help i + (((List.finRange M).filter x).map (gain p i silentRounds)).sum

def fires (p : Parameters N M) (i : Fin N) (silentRounds : Nat) (x : Pattern M) (e : Int) : Bool :=
  decide ((p.threshold i : Int) ≤ (score p i silentRounds x : Int) + e)

def admissible (budget : Nat) (e : Int) : Prop := -(budget : Int) ≤ e ∧ e ≤ (budget : Int)

def need (p : Parameters N M) (i : Fin N) : Nat :=
  ((List.range (p.maxWrites + 1)).find? fun k => fires p i k (p.target i) 0).getD (p.maxWrites + 1)

def robustFire (level budget value : Nat) : Bool := decide (level + budget ≤ value)

def robustSilence (level budget value : Nat) : Bool := decide (value + budget < level)

def Parameters.jointTargets (p : Parameters N M) : Bool :=
  (List.finRange N).all fun i => decide (2 ≤ card (p.target i))

def Parameters.heldOut (p : Parameters N M) : Bool :=
  p.tests.all fun x => (List.finRange N).all fun i =>
    !(contains x (p.target i) && contains (p.target i) x)

def Parameters.subpatterns (p : Parameters N M) : Bool :=
  (List.finRange N).all fun i => p.tests.any fun x =>
    decide (0 < card x) && proper x (p.target i)

def Parameters.supersets (p : Parameters N M) : Bool :=
  (List.finRange N).all fun i => p.tests.any fun x => proper (p.target i) x

def Parameters.otherPatterns (p : Parameters N M) : Bool :=
  decide (0 < N) && p.tests.any fun x => (List.finRange N).all fun i => incomparable x (p.target i)

def Parameters.earlySilence (p : Parameters N M) : Bool :=
  (List.finRange N).all fun i => (List.range (need p i)).all fun k =>
    robustSilence (p.threshold i) (p.trainingError i) (score p i k (p.target i))

def Parameters.stops (p : Parameters N M) : Bool :=
  (List.finRange N).all fun i =>
    decide (0 < need p i ∧ need p i ≤ p.maxWrites) &&
    robustFire (p.threshold i) (p.trainingError i) (score p i (need p i) (p.target i))

def Parameters.belowRail (p : Parameters N M) : Bool :=
  (List.finRange N).all fun i => (List.finRange M).all fun j =>
    decide (gain p i (need p i) j < p.rail)

def Parameters.positiveMargin (p : Parameters N M) : Bool :=
  (List.finRange N).all fun i =>
    robustFire (p.threshold i) (p.testingError i) (score p i (need p i) (p.target i))

def Parameters.negativeMargin (p : Parameters N M) : Bool :=
  (List.finRange N).all fun i => ((List.finRange M).filter (p.target i)).all fun j =>
    robustSilence (p.threshold i) (p.testingError i) (score p i (need p i) (omits j))

def Parameters.check (p : Parameters N M) : Bool :=
  decide (0 < p.dose) && p.jointTargets && p.heldOut && p.subpatterns && p.supersets &&
    p.otherPatterns && p.earlySilence && p.stops && p.belowRail && p.positiveMargin && p.negativeMargin

def Parameters.Valid (p : Parameters N M) : Prop := p.check = true

instance (p : Parameters N M) : Decidable p.Valid :=
  inferInstanceAs (Decidable (p.check = true))

/-- The error is sampled at each round. The update uses the local FIRE
decision, with no access to the predicted stopping count. -/
def trainingCount (p : Parameters N M) (errors : Nat → Fin N → Int) (i : Fin N) : Nat → Nat
  | 0 => 0
  | round + 1 =>
    let k := trainingCount p errors i round
    if fires p i k (p.target i) (errors round i) then k else k + 1

def trainingFire (p : Parameters N M) (errors : Nat → Fin N → Int) (round : Nat) (i : Fin N) : Bool :=
  fires p i (trainingCount p errors i round) (p.target i) (errors round i)

def predicted (p : Parameters N M) (x : Pattern M) (i : Fin N) : Bool := contains x (p.target i)

/-- Tests read the same settled memory with writes disabled. -/
def testFire (p : Parameters N M) (trainingErrors : Nat → Fin N → Int)
    (x : Pattern M) (errors : Fin N → Int) (i : Fin N) : Bool :=
  fires p i (trainingCount p trainingErrors i (p.maxWrites + 1)) x (errors i)

/-- The frozen guarded target. In particular, the test conclusion holds for
the entire Boolean cube, so it covers the held-out set without fitting it. -/
def LearnedCoincidenceRecognition : Prop :=
  ∀ (N M : Nat) (p : Parameters N M), p.Valid →
    ∀ (errors : Nat → Fin N → Int), (∀ r i, admissible (p.trainingError i) (errors r i)) →
      (∀ r i, trainingCount p errors i r = min r (need p i) ∧
        trainingFire p errors r i = decide (need p i ≤ r)) ∧
      (∀ r i j, portWrites p i j (trainingCount p errors i r) ≤ p.maxWrites ∧
        gain p i (trainingCount p errors i r) j < p.rail) ∧
      (∀ r, p.maxWrites ≤ r → ∀ i j,
        gain p i (trainingCount p errors i r) j = gain p i (need p i) j) ∧
      (∀ (x : Pattern M) (readErrors : Fin N → Int),
        (∀ i, admissible (p.testingError i) (readErrors i)) →
        ∀ i, testFire p errors x readErrors i = predicted p x i)

private def pilot : Parameters 3 4 where
  target i := if i = 0 then pattern [0, 1] else if i = 1 then pattern [1, 2] else pattern [2, 3]
  tests := [pattern [0], pattern [1], pattern [2], pattern [3], pattern [0, 2], pattern [1, 3],
    pattern [0, 1, 2], pattern [0, 2, 3], pattern [0, 1, 2, 3]]
  initialGain := fun _ _ => 0
  help := fun _ => 0
  threshold := fun _ => 6
  trainingError := fun _ => 1
  testingError := fun _ => 1
  dose := 4
  maxWrites := 2
  rail := 9

private def atFirst (new old : Nat) : Fin 3 → Nat := fun i => if i = 0 then new else old

/-- Accepted before training. A held-out triple predicts two active outputs. -/
example : pilot.Valid ∧
    (List.finRange 3).map (need pilot) = [1, 1, 1] ∧
    (List.finRange 3).map (predicted pilot (pattern [0, 1, 2])) = [true, true, false] := by
  decide +kernel

example : ({pilot with dose := 0}).check = false := by decide +kernel
example : ({pilot with target := fun _ => pattern [0]}).jointTargets = false := by decide +kernel
example : ({pilot with tests := pilot.target 0 :: pilot.tests}).heldOut = false := by decide +kernel
example : ({pilot with tests := pilot.tests.filter fun x => decide (1 < card x)}).subpatterns = false := by
  decide +kernel
example : ({pilot with tests := pilot.tests.filter fun x => decide (card x ≤ 2)}).supersets = false := by
  decide +kernel
example : ({pilot with tests := [pattern [0], pattern [1], pattern [2], pattern [3],
    pattern [0, 1, 2, 3]]}).otherPatterns = false := by decide +kernel

/-- At the first cell, the clean crossing is at two writes. With error +2,
the prior score 8 reaches the threshold 10 one round too soon. -/
example : ({pilot with threshold := atFirst 10 6, trainingError := atFirst 2 1}).earlySilence = false ∧
    fires {pilot with threshold := atFirst 10 6} 0 1 (pilot.target 0) 2 = true := by
  decide +kernel

example : ({pilot with maxWrites := 0}).stops = false := by decide +kernel
example : ({pilot with trainingError := atFirst 3 1}).stops = false ∧
    fires pilot 0 1 (pilot.target 0) (-3) = false := by decide +kernel
example : ({pilot with rail := 4}).belowRail = false := by decide +kernel
example : ({pilot with threshold := atFirst 7 6, testingError := atFirst 2 1}).positiveMargin = false ∧
    fires {pilot with threshold := atFirst 7 6} 0 1 (pattern [0, 1, 2]) (-2) = false := by
  decide +kernel
example : ({pilot with testingError := atFirst 2 1}).negativeMargin = false ∧
    fires pilot 0 1 (pattern [0]) 2 = true := by decide +kernel

/-- Untrained reads are silent on a held-out triple that should hit two cells. -/
example : (List.finRange 3).map (fun i => fires pilot i 0 (pattern [0, 1, 2]) 0) =
    [false, false, false] := by decide +kernel

end LearnedCoincidence

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, info) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      if info.isAxiom then
        throwError "Unexpected local axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
