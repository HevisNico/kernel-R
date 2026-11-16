import LayeredMonotoneExample
import LayeredMonotoneCheckerProofs

namespace LearnedCoincidence.Layered.CheckerExample

open MonotoneDNF (singleton)

private def expected (x : Pattern 4) : Bool := (x 0 && x 1) || (x 2 && x 3)

private def editFinal (choose : Pattern 4 → Bool) (value : Int)
    (edit : (Pattern 2 → Int) → Pattern 2 → Int) (x : Pattern 4) : ReadTrace Example.circuit :=
  let original := Example.test x
  if choose x then
    ⟨original.1, fun i => { original.2.1 i with measuredScore := value },
      fun i => edit (original.2.2 i)⟩
  else original

private def silentOutsideBudget : Pattern 4 → ReadTrace Example.circuit :=
  editFinal (fun x => !expected x) (-2) id

private def firingAnchorBelowBound : Pattern 4 → ReadTrace Example.circuit :=
  editFinal (fun x => x 0 && x 1 && !(x 2 && x 3)) 2
    (fun scores y => if y 0 && !y 1 then 2 else scores y)

private def submaskAboveObserved : Pattern 4 → ReadTrace Example.circuit :=
  editFinal (fun x => x 0 && x 1 && x 2 && x 3) 3
    (fun scores y => if y 0 && y 1 then 3 else scores y)

/-- Change only the silent second AND in the replay of the first OR lesson.
The upper-layer arrivals and all addressed training slots stay intact. -/
private def lowerReplayOutsideBudget : TrainingTrace Example.circuit :=
  let original := Example.train
  ⟨original.1, fun i g r =>
    let upper : ReadTrace Example.copyLayer := original.2.1 i g r
    if g = 0 ∧ r = 0 then
      let lower : ReadTrace Example.firstLayer := upper.1
      let altered : ReadTrace Example.firstLayer :=
        ⟨lower.1, fun j => if j = 1 then { lower.2.1 j with measuredScore := -2 } else lower.2.1 j,
          lower.2.2⟩
      ⟨altered, upper.2⟩
    else upper,
    original.2.2⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem accepted_valid : checkLayeredValid Example.circuit = true := by decide +kernel
private theorem accepted_calendar :
    checkLayeredSeparation Example.circuit Example.train Example.test = true := by decide +kernel
private theorem accepted_training :
    checkLayeredTrainingCalibration Example.circuit Example.train = true := by decide +kernel
private theorem accepted_tests :
    checkLayeredReadCalibration Example.circuit Example.train Example.test = true := by decide +kernel

example : checkLayeredSeparation Example.circuit Example.train (Example.replay 0) = false := by
  decide +kernel

example : checkLayeredReadCalibration Example.circuit Example.train silentOutsideBudget = false := by
  decide +kernel

example : checkLayeredReadCalibration Example.circuit Example.train firingAnchorBelowBound = false := by
  decide +kernel

example : checkLayeredReadCalibration Example.circuit Example.train submaskAboveObserved = false := by
  decide +kernel

example : checkLayeredTrainingCalibration Example.circuit lowerReplayOutsideBudget = false := by
  decide +kernel

/-- The four Boolean certificates give the theorem hypotheses on the saturated trace. -/
example : Example.circuit.Trained Example.train ∧
    ∀ x, observed Example.circuit (Example.test x) = Example.circuit.predict x :=
  layered_monotone_recognition_one_sided 4 3 1 Example.circuit
    (layered_valid_checker_sound 4 3 1 _ accepted_valid) Example.train Example.test
    (layered_separation_checker_sound 4 3 1 _ _ _ accepted_calendar)
    (layered_training_calibration_checker_sound 4 3 1 _ _ accepted_training)
    (layered_read_calibration_checker_sound 4 3 1 _ _ _ accepted_tests)

end LearnedCoincidence.Layered.CheckerExample
