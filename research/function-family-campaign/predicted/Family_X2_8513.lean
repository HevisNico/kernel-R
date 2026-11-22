import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member X2, instance 8513.
Shape `Cascade 1 1 2`. Each `checks_*`, `valid_*`, `separation_*` and `calibration_*` theorem asserts a verdict
by `decide +kernel`; the file compiles only if the kernel agrees with every asserted value. -/

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup

open TwoLayer (SlotTiming ReadObservation)

private def term : Fin 1 → Pattern 2 := fun _ => pattern [0, 1]

private def empty2 : ReadObservation 2 := datedRead 0 #v[none, none] [] 0
private def empty1 : ReadObservation 1 := datedRead 0 #v[none] [] 0

def left : SlotTiming := ⟨(1 / 50 : Rat), (11 / 10 : Rat), (22 : Rat)⟩
def right : SlotTiming := ⟨(11 / 10 : Rat), (11 / 5 : Rat), (19 : Rat)⟩

def checks (p : Cascade 1 1 2) (t : TraceTables p) : Bool :=
  checkCascadeValid p &&
  checkTrainingSeparation p left right t.observations &&
  checkCascadeCalibrationOneSided p left right t.observations t.scoreAt

def cascade_X2_8513_K0 : Cascade 1 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[36749, 36748]] : Vector (Vector Nat 2) 1).get a).get j,
    help := fun a => (#v[0] : Vector Nat 1).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[198] : Vector Nat 1).get a,
    testingError := fun a => (#v[198] : Vector Nat 1).get a,
    dose := 7494, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[80128] : Vector Nat 1).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 116, testingError := fun _ => 116,
    dose := 8732, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_X2_8513_K0_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), some (0 : Rat)] [] (73496 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), some (22 : Rat)] [] (88487 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), some (44 : Rat)] [(449051 / 10000 : Rat)] (103476 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), some (66 : Rat)] [(669051 / 10000 : Rat)] (103476 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), some (88 : Rat)] [(889051 / 10000 : Rat)] (103476 : Int)]]
private def trace_X2_8513_K0_te : List (List (ReadObservation 2)) := [[datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat)] [(1109051 / 10000 : Rat)] (103476 : Int)], [datedRead (132 : Rat) #v[some (132 : Rat), some (132 : Rat)] [(1329051 / 10000 : Rat)] (103476 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat)] [(1549051 / 10000 : Rat)] (103476 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), some (176 : Rat)] [(1769051 / 10000 : Rat)] (103476 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat)] [(1989051 / 10000 : Rat)] (103476 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), some (220 : Rat)] [(2209051 / 10000 : Rat)] (103476 : Int)]]
private def trace_X2_8513_K0_st : List (ReadObservation 1) := [datedRead (1124051 / 10000 : Rat) #v[some (1124051 / 10000 : Rat)] [] (80127 : Int), datedRead (1344051 / 10000 : Rat) #v[some (1344051 / 10000 : Rat)] [] (88861 : Int), datedRead (1564051 / 10000 : Rat) #v[some (1564051 / 10000 : Rat)] [] (97593 : Int), datedRead (1784051 / 10000 : Rat) #v[some (1784051 / 10000 : Rat)] [(223983 / 1250 : Rat)] (106325 : Int), datedRead (2004051 / 10000 : Rat) #v[some (2004051 / 10000 : Rat)] [(251483 / 1250 : Rat)] (106325 : Int), datedRead (2224051 / 10000 : Rat) #v[some (2224051 / 10000 : Rat)] [(278983 / 1250 : Rat)] (106325 : Int)]
private def trace_X2_8513_K0_fx : List (List (ReadObservation 2)) := [[datedRead (242 : Rat) #v[none, none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat)] [] (51738 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none] [] (51739 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), some (308 : Rat)] [(3089051 / 10000 : Rat)] (103476 : Int)]]
private def trace_X2_8513_K0_sx : List (ReadObservation 1) := [datedRead (487 / 2 : Rat) #v[none] [] (0 : Int), datedRead (575 / 2 : Rat) #v[none] [] (0 : Int), datedRead (531 / 2 : Rat) #v[none] [] (0 : Int), datedRead (3104051 / 10000 : Rat) #v[some (3104051 / 10000 : Rat)] [(388983 / 1250 : Rat)] (106325 : Int)]
private def trace_X2_8513_K0_sc : List (Vector Int 2) := [#v[(0 : Int), (106325 : Int)], #v[(0 : Int), (106325 : Int)], #v[(0 : Int), (106325 : Int)], #v[(0 : Int), (106325 : Int)]]

def trace_X2_8513_K0 : TraceTables cascade_X2_8513_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_X2_8513_K0_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_X2_8513_K0_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_X2_8513_K0_st.getD n.val empty1
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_X2_8513_K0_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_X2_8513_K0_sx.getD w.val empty1
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_X2_8513_K0_sc.getD w.val #v[0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_X2_8513_K0 : checks cascade_X2_8513_K0 trace_X2_8513_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_X2_8513_K0 : checkCascadeValid cascade_X2_8513_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_X2_8513_K0 : checkTrainingSeparation cascade_X2_8513_K0 left right trace_X2_8513_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_X2_8513_K0 : checkCascadeCalibrationOneSided cascade_X2_8513_K0 left right trace_X2_8513_K0.observations trace_X2_8513_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_X2_8513_K0 : ∀ x i, (trace_X2_8513_K0.observations.secondTest x i).fired = output cascade_X2_8513_K0 i x := by
  have checked := checks_X2_8513_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 1 1 2 cascade_X2_8513_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_X2_8513_K0.observations trace_X2_8513_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_X2_8513_K3 : Cascade 1 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[36749, 36748]] : Vector (Vector Nat 2) 1).get a).get j,
    help := fun a => (#v[0] : Vector Nat 1).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[2442] : Vector Nat 1).get a,
    testingError := fun a => (#v[2442] : Vector Nat 1).get a,
    dose := 7494, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[80128] : Vector Nat 1).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 1436, testingError := fun _ => 1436,
    dose := 8732, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_X2_8513_K3_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), some (0 : Rat)] [] (73496 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), some (22 : Rat)] [] (88487 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), some (44 : Rat)] [(449051 / 10000 : Rat)] (103476 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), some (66 : Rat)] [(669051 / 10000 : Rat)] (103476 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), some (88 : Rat)] [(889051 / 10000 : Rat)] (103476 : Int)]]
private def trace_X2_8513_K3_te : List (List (ReadObservation 2)) := [[datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat)] [(1109051 / 10000 : Rat)] (103476 : Int)], [datedRead (132 : Rat) #v[some (132 : Rat), some (132 : Rat)] [(1329051 / 10000 : Rat)] (103476 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat)] [(1549051 / 10000 : Rat)] (103476 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), some (176 : Rat)] [(1769051 / 10000 : Rat)] (103476 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat)] [(1989051 / 10000 : Rat)] (103476 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), some (220 : Rat)] [(2209051 / 10000 : Rat)] (103476 : Int)]]
private def trace_X2_8513_K3_st : List (ReadObservation 1) := [datedRead (1124051 / 10000 : Rat) #v[some (1124051 / 10000 : Rat)] [] (80127 : Int), datedRead (1344051 / 10000 : Rat) #v[some (1344051 / 10000 : Rat)] [] (88861 : Int), datedRead (1564051 / 10000 : Rat) #v[some (1564051 / 10000 : Rat)] [] (97593 : Int), datedRead (1784051 / 10000 : Rat) #v[some (1784051 / 10000 : Rat)] [(223983 / 1250 : Rat)] (106325 : Int), datedRead (2004051 / 10000 : Rat) #v[some (2004051 / 10000 : Rat)] [(251483 / 1250 : Rat)] (106325 : Int), datedRead (2224051 / 10000 : Rat) #v[some (2224051 / 10000 : Rat)] [(278983 / 1250 : Rat)] (106325 : Int)]
private def trace_X2_8513_K3_fx : List (List (ReadObservation 2)) := [[datedRead (242 : Rat) #v[none, none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat)] [] (51738 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none] [] (51739 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), some (308 : Rat)] [(3089051 / 10000 : Rat)] (103476 : Int)]]
private def trace_X2_8513_K3_sx : List (ReadObservation 1) := [datedRead (487 / 2 : Rat) #v[none] [] (0 : Int), datedRead (575 / 2 : Rat) #v[none] [] (0 : Int), datedRead (531 / 2 : Rat) #v[none] [] (0 : Int), datedRead (3104051 / 10000 : Rat) #v[some (3104051 / 10000 : Rat)] [(388983 / 1250 : Rat)] (106325 : Int)]
private def trace_X2_8513_K3_sc : List (Vector Int 2) := [#v[(0 : Int), (106325 : Int)], #v[(0 : Int), (106325 : Int)], #v[(0 : Int), (106325 : Int)], #v[(0 : Int), (106325 : Int)]]

def trace_X2_8513_K3 : TraceTables cascade_X2_8513_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_X2_8513_K3_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_X2_8513_K3_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_X2_8513_K3_st.getD n.val empty1
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_X2_8513_K3_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_X2_8513_K3_sx.getD w.val empty1
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_X2_8513_K3_sc.getD w.val #v[0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_X2_8513_K3 : checks cascade_X2_8513_K3 trace_X2_8513_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_X2_8513_K3 : checkCascadeValid cascade_X2_8513_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_X2_8513_K3 : checkTrainingSeparation cascade_X2_8513_K3 left right trace_X2_8513_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_X2_8513_K3 : checkCascadeCalibrationOneSided cascade_X2_8513_K3 left right trace_X2_8513_K3.observations trace_X2_8513_K3.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_X2_8513_K3 : ∀ x i, (trace_X2_8513_K3.observations.secondTest x i).fired = output cascade_X2_8513_K3 i x := by
  have checked := checks_X2_8513_K3
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 1 1 2 cascade_X2_8513_K3
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_X2_8513_K3.observations trace_X2_8513_K3.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
