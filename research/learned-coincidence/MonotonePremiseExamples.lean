import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.Example

open TwoLayer (SlotTiming ReadObservation)

private def term (a : Fin 2) : Pattern 4 :=
  if a = 0 then pattern [0, 1] else pattern [2, 3]

def cascade : Cascade 2 1 4 where
  first := {
    target := term, tests := [], initialGain := fun _ _ => 0, help := fun _ => 0,
    threshold := fun _ => 6, trainingError := fun _ => 1, testingError := fun _ => 1,
    dose := 4, maxWrites := 1, rail := 5
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ _ => 0, help := fun _ => 0, threshold := fun _ => 3,
    trainingError := fun _ => 1, testingError := fun _ => 1,
    dose := 5, maxWrites := 1, rail := 6
  }
  delay := fun _ _ => 1 / 2
  heldOut := [pattern [], pattern [0, 1, 2, 3]]

def timing : SlotTiming := ⟨1 / 2, 3, 4⟩

private def read (start : Rat) (x : Pattern M) (score level : Int) : ReadObservation M :=
  datedRead start (Vector.ofFn fun j => if x j then some start else none)
    (if level ≤ score then [start + 1] else []) score

private def firstTestScore (x : Pattern 4) (a : Fin 2) : Int :=
  if a = 0 then (if x 0 then 4 else 0) + (if x 1 then 4 else 0)
  else (if x 2 then 4 else 0) + (if x 3 then 4 else 0)

private def upstream (x : Pattern 4) : Pattern 2 :=
  fun a => if a = 0 then x 0 && x 1 else x 2 && x 3

private def external (word : Fin (2 ^ 4)) : Pattern 4 :=
  fun j => word.val.testBit (3 - j.val)

inductive Perturbation where
  | none
  | silentWithoutRoom
  | firingWithoutRoom
  | submaskAboveMask

/-- The unperturbed OR score table is sub-additive: 8 for the pair and 5
for each singleton. Each perturbation changes just one test row. -/
private def referenceScores (change : Perturbation) (x : Pattern 4) : Vector Int 4 :=
  match change with
  | .none => #v[0, 5, 5, 8]
  | .silentWithoutRoom =>
    if maskIndex x = 0 then #v[2, 5, 5, 8] else #v[0, 5, 5, 8]
  | .firingWithoutRoom =>
    if maskIndex x = 12 then #v[0, 5, 3, 8] else #v[0, 5, 5, 8]
  | .submaskAboveMask =>
    if maskIndex x = 15 then #v[0, 5, 5, 4] else #v[0, 5, 5, 8]

private def lessonStart (n : Fin (lessons cascade).length) : Rat := 20 + 10 * n.val

private def lessonLine (n : Fin (lessons cascade).length) : Fin 2 :=
  if n.val % 2 = 0 then 0 else 1

def trace (change : Perturbation) : TraceTables cascade where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a =>
    read (10 * r.val) (term a) (if r.val = 0 then 0 else 8) 6
  teach := Vector.ofFn fun n => Vector.ofFn fun a =>
    let x := term (lessonLine n)
    read (lessonStart n) x (if a = lessonLine n then 8 else 0) 6
  secondTrain := Vector.ofFn fun n =>
    read (lessonStart n + 3 / 2) (singleton (lessonLine n)) (if n.val < 2 then 0 else 5) 3
  firstTest := Vector.ofFn fun word => Vector.ofFn fun a =>
    read 60 (external word) (firstTestScore (external word) a) 6
  secondTest := Vector.ofFn fun word => Vector.ofFn fun _ =>
    let x := external word
    let y := upstream x
    read (60 + 3 / 2) y ((referenceScores change x).get (maskIndex y)) 3
  scores := Vector.ofFn fun word => Vector.ofFn fun _ => referenceScores change (external word)

def checks (change : Perturbation) : Bool :=
  let t := trace change
  checkCascadeValid cascade &&
  checkTrainingSeparation cascade timing timing t.observations &&
  checkCascadeCalibrationOneSided cascade timing timing t.observations t.scoreAt

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem accepted : checks .none = true := by decide +kernel

/- The silent empty read stays below the threshold at 2, but its
additive score is 0 with budget 1. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
example : checks .silentWithoutRoom = false := by decide +kernel

/- The singleton fires at threshold 3, below its required lower bound 4. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
example : checks .firingWithoutRoom = false := by decide +kernel

/- The pair fires at 4, below the score 5 of a firing singleton. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
example : checks .submaskAboveMask = false := by decide +kernel

example : checkCascadeValid { cascade with second := { cascade.second with threshold := fun _ => 1 } }
    = false := by decide +kernel

example : checkCascadeValid { cascade with second := { cascade.second with threshold := fun _ => 5 } }
    = false := by decide +kernel

example : checkTrainingSeparation cascade timing timing
    { (trace .none).observations with firstTrain := fun r a =>
      { (trace .none).observations.firstTrain r a with start := 0 } } = false := by decide +kernel

/-- Successful checks discharge all three hypotheses of the recognition theorem. -/
example : ∀ x i, ((trace .none).observations.secondTest x i).fired = output cascade i x := by
  have checked := accepted
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 4 cascade
    (cascade_valid_checker_sound _ _ _ _ params) timing timing
    (trace .none).observations (trace .none).scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

end LearnedCoincidence.MonotoneDNF.PremiseCheck.Example
