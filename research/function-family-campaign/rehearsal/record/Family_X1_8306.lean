import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member X1, instance 8306.
Shape `Cascade 1 1 1`. Each `checks_*`, `valid_*`, `separation_*` and `calibration_*` theorem asserts a verdict
by `decide +kernel`; the file compiles only if the kernel agrees with every asserted value. -/

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup

open TwoLayer (SlotTiming ReadObservation)

private def term : Fin 1 → Pattern 1 := fun _ => pattern [0]

private def empty1 : ReadObservation 1 := datedRead 0 #v[none] [] 0

def left : SlotTiming := ⟨(1 / 50 : Rat), (11 / 10 : Rat), (22 : Rat)⟩
def right : SlotTiming := ⟨(11 / 10 : Rat), (11 / 5 : Rat), (19 : Rat)⟩

def checks (p : Cascade 1 1 1) (t : TraceTables p) : Bool :=
  checkCascadeValid p &&
  checkTrainingSeparation p left right t.observations &&
  checkCascadeCalibrationOneSided p left right t.observations t.scoreAt

def cascade_X1_8306_K0 : Cascade 1 1 1 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[82446]] : Vector (Vector Nat 1) 1).get a).get j,
    help := fun a => (#v[0] : Vector Nat 1).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[103] : Vector Nat 1).get a,
    testingError := fun a => (#v[103] : Vector Nat 1).get a,
    dose := 7673, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[89676] : Vector Nat 1).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 102, testingError := fun _ => 102,
    dose := 7540, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_X1_8306_K0_ft : List (List (ReadObservation 1)) := [[datedRead (0 : Rat) #v[some (0 : Rat)] [] (82444 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat)] [] (90119 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat)] [] (97793 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat)] [(333923 / 5000 : Rat)] (105466 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat)] [(443923 / 5000 : Rat)] (105466 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat)] [(553923 / 5000 : Rat)] (105466 : Int)]]
private def trace_X1_8306_K0_te : List (List (ReadObservation 1)) := [[datedRead (132 : Rat) #v[some (132 : Rat)] [(663923 / 5000 : Rat)] (105466 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat)] [(773923 / 5000 : Rat)] (105466 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat)] [(883923 / 5000 : Rat)] (105466 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat)] [(993923 / 5000 : Rat)] (105466 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat)] [(1103923 / 5000 : Rat)] (105466 : Int)]]
private def trace_X1_8306_K0_st : List (ReadObservation 1) := [datedRead (671423 / 5000 : Rat) #v[some (671423 / 5000 : Rat)] [] (89675 : Int), datedRead (781423 / 5000 : Rat) #v[some (781423 / 5000 : Rat)] [] (97216 : Int), datedRead (891423 / 5000 : Rat) #v[some (891423 / 5000 : Rat)] [(35817 / 200 : Rat)] (104756 : Int), datedRead (1001423 / 5000 : Rat) #v[some (1001423 / 5000 : Rat)] [(40217 / 200 : Rat)] (104756 : Int), datedRead (1111423 / 5000 : Rat) #v[some (1111423 / 5000 : Rat)] [(44617 / 200 : Rat)] (104756 : Int)]
private def trace_X1_8306_K0_fx : List (List (ReadObservation 1)) := [[datedRead (242 : Rat) #v[none] [] (0 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat)] [(1323923 / 5000 : Rat)] (105466 : Int)]]
private def trace_X1_8306_K0_sx : List (ReadObservation 1) := [datedRead (487 / 2 : Rat) #v[none] [] (0 : Int), datedRead (1331423 / 5000 : Rat) #v[some (1331423 / 5000 : Rat)] [(53417 / 200 : Rat)] (104756 : Int)]
private def trace_X1_8306_K0_sc : List (Vector Int 2) := [#v[(0 : Int), (104756 : Int)], #v[(0 : Int), (104756 : Int)]]

def trace_X1_8306_K0 : TraceTables cascade_X1_8306_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_X1_8306_K0_ft.getD r.val []).getD a.val empty1
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_X1_8306_K0_te.getD n.val []).getD a.val empty1
  secondTrain := Vector.ofFn fun n => trace_X1_8306_K0_st.getD n.val empty1
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_X1_8306_K0_fx.getD w.val []).getD a.val empty1
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_X1_8306_K0_sx.getD w.val empty1
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_X1_8306_K0_sc.getD w.val #v[0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_X1_8306_K0 : checks cascade_X1_8306_K0 trace_X1_8306_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_X1_8306_K0 : checkCascadeValid cascade_X1_8306_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_X1_8306_K0 : checkTrainingSeparation cascade_X1_8306_K0 left right trace_X1_8306_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_X1_8306_K0 : checkCascadeCalibrationOneSided cascade_X1_8306_K0 left right trace_X1_8306_K0.observations trace_X1_8306_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_X1_8306_K0 : ∀ x i, (trace_X1_8306_K0.observations.secondTest x i).fired = output cascade_X1_8306_K0 i x := by
  have checked := checks_X1_8306_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 1 1 1 cascade_X1_8306_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_X1_8306_K0.observations trace_X1_8306_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_X1_8306_K3 : Cascade 1 1 1 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[82446]] : Vector (Vector Nat 1) 1).get a).get j,
    help := fun a => (#v[0] : Vector Nat 1).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[1266] : Vector Nat 1).get a,
    testingError := fun a => (#v[1266] : Vector Nat 1).get a,
    dose := 7673, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[89676] : Vector Nat 1).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 1236, testingError := fun _ => 1236,
    dose := 7540, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_X1_8306_K3_ft : List (List (ReadObservation 1)) := [[datedRead (0 : Rat) #v[some (0 : Rat)] [] (82444 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat)] [] (90119 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat)] [] (97793 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat)] [(333923 / 5000 : Rat)] (105466 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat)] [(443923 / 5000 : Rat)] (105466 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat)] [(553923 / 5000 : Rat)] (105466 : Int)]]
private def trace_X1_8306_K3_te : List (List (ReadObservation 1)) := [[datedRead (132 : Rat) #v[some (132 : Rat)] [(663923 / 5000 : Rat)] (105466 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat)] [(773923 / 5000 : Rat)] (105466 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat)] [(883923 / 5000 : Rat)] (105466 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat)] [(993923 / 5000 : Rat)] (105466 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat)] [(1103923 / 5000 : Rat)] (105466 : Int)]]
private def trace_X1_8306_K3_st : List (ReadObservation 1) := [datedRead (671423 / 5000 : Rat) #v[some (671423 / 5000 : Rat)] [] (89675 : Int), datedRead (781423 / 5000 : Rat) #v[some (781423 / 5000 : Rat)] [] (97216 : Int), datedRead (891423 / 5000 : Rat) #v[some (891423 / 5000 : Rat)] [(35817 / 200 : Rat)] (104756 : Int), datedRead (1001423 / 5000 : Rat) #v[some (1001423 / 5000 : Rat)] [(40217 / 200 : Rat)] (104756 : Int), datedRead (1111423 / 5000 : Rat) #v[some (1111423 / 5000 : Rat)] [(44617 / 200 : Rat)] (104756 : Int)]
private def trace_X1_8306_K3_fx : List (List (ReadObservation 1)) := [[datedRead (242 : Rat) #v[none] [] (0 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat)] [(1323923 / 5000 : Rat)] (105466 : Int)]]
private def trace_X1_8306_K3_sx : List (ReadObservation 1) := [datedRead (487 / 2 : Rat) #v[none] [] (0 : Int), datedRead (1331423 / 5000 : Rat) #v[some (1331423 / 5000 : Rat)] [(53417 / 200 : Rat)] (104756 : Int)]
private def trace_X1_8306_K3_sc : List (Vector Int 2) := [#v[(0 : Int), (104756 : Int)], #v[(0 : Int), (104756 : Int)]]

def trace_X1_8306_K3 : TraceTables cascade_X1_8306_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_X1_8306_K3_ft.getD r.val []).getD a.val empty1
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_X1_8306_K3_te.getD n.val []).getD a.val empty1
  secondTrain := Vector.ofFn fun n => trace_X1_8306_K3_st.getD n.val empty1
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_X1_8306_K3_fx.getD w.val []).getD a.val empty1
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_X1_8306_K3_sx.getD w.val empty1
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_X1_8306_K3_sc.getD w.val #v[0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_X1_8306_K3 : checks cascade_X1_8306_K3 trace_X1_8306_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_X1_8306_K3 : checkCascadeValid cascade_X1_8306_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_X1_8306_K3 : checkTrainingSeparation cascade_X1_8306_K3 left right trace_X1_8306_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_X1_8306_K3 : checkCascadeCalibrationOneSided cascade_X1_8306_K3 left right trace_X1_8306_K3.observations trace_X1_8306_K3.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_X1_8306_K3 : ∀ x i, (trace_X1_8306_K3.observations.secondTest x i).fired = output cascade_X1_8306_K3 i x := by
  have checked := checks_X1_8306_K3
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 1 1 1 cascade_X1_8306_K3
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_X1_8306_K3.observations trace_X1_8306_K3.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
