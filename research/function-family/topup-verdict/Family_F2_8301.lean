import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F2, instance 8301.
Shape `Cascade 2 1 3`. Each `checks_*`, `valid_*`, `separation_*` and `calibration_*` theorem asserts a verdict
by `decide +kernel`; the file compiles only if the kernel agrees with every asserted value. -/

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup

open TwoLayer (SlotTiming ReadObservation)

private def term (a : Fin 2) : Pattern 3 :=
  if a = 0 then pattern [0, 1] else pattern [0, 2]

private def empty3 : ReadObservation 3 := datedRead 0 #v[none, none, none] [] 0
private def empty2 : ReadObservation 2 := datedRead 0 #v[none, none] [] 0

def left : SlotTiming := ⟨(1 / 50 : Rat), (11 / 10 : Rat), (22 : Rat)⟩
def right : SlotTiming := ⟨(11 / 10 : Rat), (11 / 5 : Rat), (19 : Rat)⟩

def checks (p : Cascade 2 1 3) (t : TraceTables p) : Bool :=
  checkCascadeValid p &&
  checkTrainingSeparation p left right t.observations &&
  checkCascadeCalibrationOneSided p left right t.observations t.scoreAt

def cascade_F2_8301_K0 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[34465, 34465, 0], #v[31009, 0, 31009]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[216, 216] : Vector Nat 2).get a,
    testingError := fun a => (#v[216, 216] : Vector Nat 2).get a,
    dose := 8190, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[74630, 25377] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 504, testingError := fun _ => 504,
    dose := 38316, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F2_8301_K0_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), some (0 : Rat), none] [] (68928 : Int), datedRead (0 : Rat) #v[some (0 : Rat), none, some (0 : Rat)] [] (62016 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), some (22 : Rat), none] [] (85310 : Int), datedRead (22 : Rat) #v[some (22 : Rat), none, some (22 : Rat)] [] (78398 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), some (44 : Rat), none] [(224761 / 5000 : Rat)] (101692 : Int), datedRead (44 : Rat) #v[some (44 : Rat), none, some (44 : Rat)] [] (94780 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), some (66 : Rat), none] [(334761 / 5000 : Rat)] (101692 : Int), datedRead (66 : Rat) #v[some (66 : Rat), none, some (66 : Rat)] [(333949 / 5000 : Rat)] (111160 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), some (88 : Rat), none] [(444761 / 5000 : Rat)] (101692 : Int), datedRead (88 : Rat) #v[some (88 : Rat), none, some (88 : Rat)] [(443949 / 5000 : Rat)] (111160 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [(554761 / 5000 : Rat)] (101692 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none, some (110 : Rat)] [(553949 / 5000 : Rat)] (111160 : Int)]]
private def trace_F2_8301_K0_te : List (List (ReadObservation 3)) := [[datedRead (132 : Rat) #v[some (132 : Rat), some (132 : Rat), none] [(664761 / 5000 : Rat)] (101692 : Int), datedRead (132 : Rat) #v[some (132 : Rat), some (132 : Rat), none] [] (55581 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none, some (154 : Rat)] [] (50846 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none, some (154 : Rat)] [(773949 / 5000 : Rat)] (111160 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), some (176 : Rat), none] [(884761 / 5000 : Rat)] (101692 : Int), datedRead (176 : Rat) #v[some (176 : Rat), some (176 : Rat), none] [] (55581 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none, some (198 : Rat)] [] (50846 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none, some (198 : Rat)] [(993949 / 5000 : Rat)] (111160 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), some (220 : Rat), none] [(1104761 / 5000 : Rat)] (101692 : Int), datedRead (220 : Rat) #v[some (220 : Rat), some (220 : Rat), none] [] (55581 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none, some (242 : Rat)] [] (50846 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none, some (242 : Rat)] [(1213949 / 5000 : Rat)] (111160 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), some (264 : Rat), none] [(1324761 / 5000 : Rat)] (101692 : Int), datedRead (264 : Rat) #v[some (264 : Rat), some (264 : Rat), none] [] (55581 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none, some (286 : Rat)] [] (50846 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none, some (286 : Rat)] [(1433949 / 5000 : Rat)] (111160 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), some (308 : Rat), none] [(1544761 / 5000 : Rat)] (101692 : Int), datedRead (308 : Rat) #v[some (308 : Rat), some (308 : Rat), none] [] (55581 : Int)], [datedRead (330 : Rat) #v[some (330 : Rat), none, some (330 : Rat)] [] (50846 : Int), datedRead (330 : Rat) #v[some (330 : Rat), none, some (330 : Rat)] [(1653949 / 5000 : Rat)] (111160 : Int)]]
private def trace_F2_8301_K0_st : List (ReadObservation 2) := [datedRead (672261 / 5000 : Rat) #v[some (672261 / 5000 : Rat), none] [] (74626 : Int), datedRead (781449 / 5000 : Rat) #v[none, some (781449 / 5000 : Rat)] [] (25374 : Int), datedRead (892261 / 5000 : Rat) #v[some (892261 / 5000 : Rat), none] [(1793241 / 10000 : Rat)] (112947 : Int), datedRead (1001449 / 5000 : Rat) #v[none, some (1001449 / 5000 : Rat)] [] (63695 : Int), datedRead (1112261 / 5000 : Rat) #v[some (1112261 / 5000 : Rat), none] [(2233241 / 10000 : Rat)] (112947 : Int), datedRead (1221449 / 5000 : Rat) #v[none, some (1221449 / 5000 : Rat)] [(2452647 / 10000 : Rat)] (102012 : Int), datedRead (1332261 / 5000 : Rat) #v[some (1332261 / 5000 : Rat), none] [(2673241 / 10000 : Rat)] (112947 : Int), datedRead (1441449 / 5000 : Rat) #v[none, some (1441449 / 5000 : Rat)] [(2892647 / 10000 : Rat)] (102012 : Int), datedRead (1552261 / 5000 : Rat) #v[some (1552261 / 5000 : Rat), none] [(3113241 / 10000 : Rat)] (112947 : Int), datedRead (1661449 / 5000 : Rat) #v[none, some (1661449 / 5000 : Rat)] [(3332647 / 10000 : Rat)] (102012 : Int)]
private def trace_F2_8301_K0_fx : List (List (ReadObservation 3)) := [[datedRead (352 : Rat) #v[none, none, none] [] (0 : Int), datedRead (352 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (440 : Rat) #v[none, none, some (440 : Rat)] [] (0 : Int), datedRead (440 : Rat) #v[none, none, some (440 : Rat)] [] (55580 : Int)], [datedRead (396 : Rat) #v[none, some (396 : Rat), none] [] (50846 : Int), datedRead (396 : Rat) #v[none, some (396 : Rat), none] [] (0 : Int)], [datedRead (484 : Rat) #v[none, some (484 : Rat), some (484 : Rat)] [] (50846 : Int), datedRead (484 : Rat) #v[none, some (484 : Rat), some (484 : Rat)] [] (55580 : Int)], [datedRead (374 : Rat) #v[some (374 : Rat), none, none] [] (50846 : Int), datedRead (374 : Rat) #v[some (374 : Rat), none, none] [] (55581 : Int)], [datedRead (462 : Rat) #v[some (462 : Rat), none, some (462 : Rat)] [] (50846 : Int), datedRead (462 : Rat) #v[some (462 : Rat), none, some (462 : Rat)] [(2313949 / 5000 : Rat)] (111160 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat), none] [(2094761 / 5000 : Rat)] (101692 : Int), datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat), none] [] (55581 : Int)], [datedRead (506 : Rat) #v[some (506 : Rat), some (506 : Rat), some (506 : Rat)] [(2534761 / 5000 : Rat)] (101692 : Int), datedRead (506 : Rat) #v[some (506 : Rat), some (506 : Rat), some (506 : Rat)] [(2533949 / 5000 : Rat)] (111160 : Int)]]
private def trace_F2_8301_K0_sx : List (ReadObservation 2) := [datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (883 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (795 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (971 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (2321449 / 5000 : Rat) #v[none, some (2321449 / 5000 : Rat)] [(4652647 / 10000 : Rat)] (102012 : Int), datedRead (2102261 / 5000 : Rat) #v[some (2102261 / 5000 : Rat), none] [(4213241 / 10000 : Rat)] (112947 : Int), datedRead (2541449 / 5000 : Rat) #v[some (2542261 / 5000 : Rat), some (2541449 / 5000 : Rat)] [(2543687 / 5000 : Rat)] (176638 : Int)]
private def trace_F2_8301_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)]]

def trace_F2_8301_K0 : TraceTables cascade_F2_8301_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F2_8301_K0_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F2_8301_K0_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F2_8301_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F2_8301_K0_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8301_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8301_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F2_8301_K0 : checks cascade_F2_8301_K0 trace_F2_8301_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F2_8301_K0 : checkCascadeValid cascade_F2_8301_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F2_8301_K0 : checkTrainingSeparation cascade_F2_8301_K0 left right trace_F2_8301_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F2_8301_K0 : checkCascadeCalibrationOneSided cascade_F2_8301_K0 left right trace_F2_8301_K0.observations trace_F2_8301_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F2_8301_K0 : ∀ x i, (trace_F2_8301_K0.observations.secondTest x i).fired = output cascade_F2_8301_K0 i x := by
  have checked := checks_F2_8301_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_F2_8301_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F2_8301_K0.observations trace_F2_8301_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F2_8301_K3 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[34465, 34465, 0], #v[31009, 0, 31009]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[2676, 2683] : Vector Nat 2).get a,
    testingError := fun a => (#v[2676, 2683] : Vector Nat 2).get a,
    dose := 8190, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[74630, 25377] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 6282, testingError := fun _ => 6282,
    dose := 38316, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F2_8301_K3_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), some (0 : Rat), none] [] (68928 : Int), datedRead (0 : Rat) #v[some (0 : Rat), none, some (0 : Rat)] [] (62016 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), some (22 : Rat), none] [] (85310 : Int), datedRead (22 : Rat) #v[some (22 : Rat), none, some (22 : Rat)] [] (78398 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), some (44 : Rat), none] [(224761 / 5000 : Rat)] (101692 : Int), datedRead (44 : Rat) #v[some (44 : Rat), none, some (44 : Rat)] [] (94780 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), some (66 : Rat), none] [(334761 / 5000 : Rat)] (101692 : Int), datedRead (66 : Rat) #v[some (66 : Rat), none, some (66 : Rat)] [(333949 / 5000 : Rat)] (111160 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), some (88 : Rat), none] [(444761 / 5000 : Rat)] (101692 : Int), datedRead (88 : Rat) #v[some (88 : Rat), none, some (88 : Rat)] [(443949 / 5000 : Rat)] (111160 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [(554761 / 5000 : Rat)] (101692 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none, some (110 : Rat)] [(553949 / 5000 : Rat)] (111160 : Int)]]
private def trace_F2_8301_K3_te : List (List (ReadObservation 3)) := [[datedRead (132 : Rat) #v[some (132 : Rat), some (132 : Rat), none] [(664761 / 5000 : Rat)] (101692 : Int), datedRead (132 : Rat) #v[some (132 : Rat), some (132 : Rat), none] [] (55581 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none, some (154 : Rat)] [] (50846 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none, some (154 : Rat)] [(773949 / 5000 : Rat)] (111160 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), some (176 : Rat), none] [(884761 / 5000 : Rat)] (101692 : Int), datedRead (176 : Rat) #v[some (176 : Rat), some (176 : Rat), none] [] (55581 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none, some (198 : Rat)] [] (50846 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none, some (198 : Rat)] [(993949 / 5000 : Rat)] (111160 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), some (220 : Rat), none] [(1104761 / 5000 : Rat)] (101692 : Int), datedRead (220 : Rat) #v[some (220 : Rat), some (220 : Rat), none] [] (55581 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none, some (242 : Rat)] [] (50846 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none, some (242 : Rat)] [(1213949 / 5000 : Rat)] (111160 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), some (264 : Rat), none] [(1324761 / 5000 : Rat)] (101692 : Int), datedRead (264 : Rat) #v[some (264 : Rat), some (264 : Rat), none] [] (55581 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none, some (286 : Rat)] [] (50846 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none, some (286 : Rat)] [(1433949 / 5000 : Rat)] (111160 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), some (308 : Rat), none] [(1544761 / 5000 : Rat)] (101692 : Int), datedRead (308 : Rat) #v[some (308 : Rat), some (308 : Rat), none] [] (55581 : Int)], [datedRead (330 : Rat) #v[some (330 : Rat), none, some (330 : Rat)] [] (50846 : Int), datedRead (330 : Rat) #v[some (330 : Rat), none, some (330 : Rat)] [(1653949 / 5000 : Rat)] (111160 : Int)]]
private def trace_F2_8301_K3_st : List (ReadObservation 2) := [datedRead (672261 / 5000 : Rat) #v[some (672261 / 5000 : Rat), none] [] (74626 : Int), datedRead (781449 / 5000 : Rat) #v[none, some (781449 / 5000 : Rat)] [] (25374 : Int), datedRead (892261 / 5000 : Rat) #v[some (892261 / 5000 : Rat), none] [(1793241 / 10000 : Rat)] (112947 : Int), datedRead (1001449 / 5000 : Rat) #v[none, some (1001449 / 5000 : Rat)] [] (63695 : Int), datedRead (1112261 / 5000 : Rat) #v[some (1112261 / 5000 : Rat), none] [(2233241 / 10000 : Rat)] (112947 : Int), datedRead (1221449 / 5000 : Rat) #v[none, some (1221449 / 5000 : Rat)] [(2452647 / 10000 : Rat)] (102012 : Int), datedRead (1332261 / 5000 : Rat) #v[some (1332261 / 5000 : Rat), none] [(2673241 / 10000 : Rat)] (112947 : Int), datedRead (1441449 / 5000 : Rat) #v[none, some (1441449 / 5000 : Rat)] [(2892647 / 10000 : Rat)] (102012 : Int), datedRead (1552261 / 5000 : Rat) #v[some (1552261 / 5000 : Rat), none] [(3113241 / 10000 : Rat)] (112947 : Int), datedRead (1661449 / 5000 : Rat) #v[none, some (1661449 / 5000 : Rat)] [(3332647 / 10000 : Rat)] (102012 : Int)]
private def trace_F2_8301_K3_fx : List (List (ReadObservation 3)) := [[datedRead (352 : Rat) #v[none, none, none] [] (0 : Int), datedRead (352 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (440 : Rat) #v[none, none, some (440 : Rat)] [] (0 : Int), datedRead (440 : Rat) #v[none, none, some (440 : Rat)] [] (55580 : Int)], [datedRead (396 : Rat) #v[none, some (396 : Rat), none] [] (50846 : Int), datedRead (396 : Rat) #v[none, some (396 : Rat), none] [] (0 : Int)], [datedRead (484 : Rat) #v[none, some (484 : Rat), some (484 : Rat)] [] (50846 : Int), datedRead (484 : Rat) #v[none, some (484 : Rat), some (484 : Rat)] [] (55580 : Int)], [datedRead (374 : Rat) #v[some (374 : Rat), none, none] [] (50846 : Int), datedRead (374 : Rat) #v[some (374 : Rat), none, none] [] (55581 : Int)], [datedRead (462 : Rat) #v[some (462 : Rat), none, some (462 : Rat)] [] (50846 : Int), datedRead (462 : Rat) #v[some (462 : Rat), none, some (462 : Rat)] [(2313949 / 5000 : Rat)] (111160 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat), none] [(2094761 / 5000 : Rat)] (101692 : Int), datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat), none] [] (55581 : Int)], [datedRead (506 : Rat) #v[some (506 : Rat), some (506 : Rat), some (506 : Rat)] [(2534761 / 5000 : Rat)] (101692 : Int), datedRead (506 : Rat) #v[some (506 : Rat), some (506 : Rat), some (506 : Rat)] [(2533949 / 5000 : Rat)] (111160 : Int)]]
private def trace_F2_8301_K3_sx : List (ReadObservation 2) := [datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (883 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (795 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (971 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (2321449 / 5000 : Rat) #v[none, some (2321449 / 5000 : Rat)] [(4652647 / 10000 : Rat)] (102012 : Int), datedRead (2102261 / 5000 : Rat) #v[some (2102261 / 5000 : Rat), none] [(4213241 / 10000 : Rat)] (112947 : Int), datedRead (2541449 / 5000 : Rat) #v[some (2542261 / 5000 : Rat), some (2541449 / 5000 : Rat)] [(2543687 / 5000 : Rat)] (176638 : Int)]
private def trace_F2_8301_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)], #v[(0 : Int), (102012 : Int), (112947 : Int), (176638 : Int)]]

def trace_F2_8301_K3 : TraceTables cascade_F2_8301_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F2_8301_K3_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F2_8301_K3_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F2_8301_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F2_8301_K3_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8301_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8301_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F2_8301_K3 : checks cascade_F2_8301_K3 trace_F2_8301_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F2_8301_K3 : checkCascadeValid cascade_F2_8301_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F2_8301_K3 : checkTrainingSeparation cascade_F2_8301_K3 left right trace_F2_8301_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F2_8301_K3 : checkCascadeCalibrationOneSided cascade_F2_8301_K3 left right trace_F2_8301_K3.observations trace_F2_8301_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
