import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F3, instance 8310.
Shape `Cascade 2 1 3`. Each `checks_*`, `valid_*`, `separation_*` and `calibration_*` theorem asserts a verdict
by `decide +kernel`; the file compiles only if the kernel agrees with every asserted value. -/

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup

open TwoLayer (SlotTiming ReadObservation)

private def term (a : Fin 2) : Pattern 3 :=
  if a = 0 then pattern [0] else pattern [1, 2]

private def empty3 : ReadObservation 3 := datedRead 0 #v[none, none, none] [] 0
private def empty2 : ReadObservation 2 := datedRead 0 #v[none, none] [] 0

def left : SlotTiming := ⟨(1 / 50 : Rat), (11 / 10 : Rat), (22 : Rat)⟩
def right : SlotTiming := ⟨(11 / 10 : Rat), (11 / 5 : Rat), (19 : Rat)⟩

def checks (p : Cascade 2 1 3) (t : TraceTables p) : Bool :=
  checkCascadeValid p &&
  checkTrainingSeparation p left right t.observations &&
  checkCascadeCalibrationOneSided p left right t.observations t.scoreAt

def cascade_F3_8310_K0 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[88534, 0, 0], #v[0, 38774, 38774]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[103, 202] : Vector Nat 2).get a,
    testingError := fun a => (#v[103, 202] : Vector Nat 2).get a,
    dose := 7651, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[55257, 44752] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 364, testingError := fun _ => 364,
    dose := 27432, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F3_8310_K0_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none, none] [] (88535 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat), some (0 : Rat)] [] (77546 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none, none] [] (96187 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat), some (22 : Rat)] [] (92851 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none, none] [(224151 / 5000 : Rat)] (103838 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat), some (44 : Rat)] [(112057 / 2500 : Rat)] (108154 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none, none] [(334151 / 5000 : Rat)] (103838 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat), some (66 : Rat)] [(167057 / 2500 : Rat)] (108154 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none, none] [(444151 / 5000 : Rat)] (103838 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat), some (88 : Rat)] [(222057 / 2500 : Rat)] (108154 : Int)]]
private def trace_F3_8310_K0_te : List (List (ReadObservation 3)) := [[datedRead (110 : Rat) #v[some (110 : Rat), none, none] [(554151 / 5000 : Rat)] (103838 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none, none] [] (0 : Int)], [datedRead (132 : Rat) #v[none, some (132 : Rat), some (132 : Rat)] [] (0 : Int), datedRead (132 : Rat) #v[none, some (132 : Rat), some (132 : Rat)] [(332057 / 2500 : Rat)] (108154 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none, none] [(774151 / 5000 : Rat)] (103838 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none, none] [] (0 : Int)], [datedRead (176 : Rat) #v[none, some (176 : Rat), some (176 : Rat)] [] (0 : Int), datedRead (176 : Rat) #v[none, some (176 : Rat), some (176 : Rat)] [(442057 / 2500 : Rat)] (108154 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none, none] [(994151 / 5000 : Rat)] (103838 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none, none] [] (0 : Int)], [datedRead (220 : Rat) #v[none, some (220 : Rat), some (220 : Rat)] [] (0 : Int), datedRead (220 : Rat) #v[none, some (220 : Rat), some (220 : Rat)] [(552057 / 2500 : Rat)] (108154 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none, none] [(1214151 / 5000 : Rat)] (103838 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none, none] [] (0 : Int)], [datedRead (264 : Rat) #v[none, some (264 : Rat), some (264 : Rat)] [] (0 : Int), datedRead (264 : Rat) #v[none, some (264 : Rat), some (264 : Rat)] [(662057 / 2500 : Rat)] (108154 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none, none] [(1434151 / 5000 : Rat)] (103838 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none, none] [] (0 : Int)], [datedRead (308 : Rat) #v[none, some (308 : Rat), some (308 : Rat)] [] (0 : Int), datedRead (308 : Rat) #v[none, some (308 : Rat), some (308 : Rat)] [(772057 / 2500 : Rat)] (108154 : Int)], [datedRead (330 : Rat) #v[some (330 : Rat), none, none] [(1654151 / 5000 : Rat)] (103838 : Int), datedRead (330 : Rat) #v[some (330 : Rat), none, none] [] (0 : Int)], [datedRead (352 : Rat) #v[none, some (352 : Rat), some (352 : Rat)] [] (0 : Int), datedRead (352 : Rat) #v[none, some (352 : Rat), some (352 : Rat)] [(882057 / 2500 : Rat)] (108154 : Int)]]
private def trace_F3_8310_K0_st : List (ReadObservation 2) := [datedRead (561651 / 5000 : Rat) #v[some (561651 / 5000 : Rat), none] [] (55252 : Int), datedRead (335807 / 2500 : Rat) #v[none, some (335807 / 2500 : Rat)] [] (44749 : Int), datedRead (781651 / 5000 : Rat) #v[some (781651 / 5000 : Rat), none] [] (82689 : Int), datedRead (445807 / 2500 : Rat) #v[none, some (445807 / 2500 : Rat)] [] (72185 : Int), datedRead (1001651 / 5000 : Rat) #v[some (1001651 / 5000 : Rat), none] [(2011933 / 10000 : Rat)] (110123 : Int), datedRead (555807 / 2500 : Rat) #v[none, some (555807 / 2500 : Rat)] [] (99619 : Int), datedRead (1221651 / 5000 : Rat) #v[some (1221651 / 5000 : Rat), none] [(2451933 / 10000 : Rat)] (110123 : Int), datedRead (665807 / 2500 : Rat) #v[none, some (665807 / 2500 : Rat)] [(1335281 / 5000 : Rat)] (127050 : Int), datedRead (1441651 / 5000 : Rat) #v[some (1441651 / 5000 : Rat), none] [(2891933 / 10000 : Rat)] (110123 : Int), datedRead (775807 / 2500 : Rat) #v[none, some (775807 / 2500 : Rat)] [(1555281 / 5000 : Rat)] (127050 : Int), datedRead (1661651 / 5000 : Rat) #v[some (1661651 / 5000 : Rat), none] [(3331933 / 10000 : Rat)] (110123 : Int), datedRead (885807 / 2500 : Rat) #v[none, some (885807 / 2500 : Rat)] [(1775281 / 5000 : Rat)] (127050 : Int)]
private def trace_F3_8310_K0_fx : List (List (ReadObservation 3)) := [[datedRead (374 : Rat) #v[none, none, none] [] (0 : Int), datedRead (374 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (462 : Rat) #v[none, none, some (462 : Rat)] [] (0 : Int), datedRead (462 : Rat) #v[none, none, some (462 : Rat)] [] (54077 : Int)], [datedRead (418 : Rat) #v[none, some (418 : Rat), none] [] (0 : Int), datedRead (418 : Rat) #v[none, some (418 : Rat), none] [] (54078 : Int)], [datedRead (506 : Rat) #v[none, some (506 : Rat), some (506 : Rat)] [] (0 : Int), datedRead (506 : Rat) #v[none, some (506 : Rat), some (506 : Rat)] [(1267057 / 2500 : Rat)] (108154 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), none, none] [(1984151 / 5000 : Rat)] (103838 : Int), datedRead (396 : Rat) #v[some (396 : Rat), none, none] [] (0 : Int)], [datedRead (484 : Rat) #v[some (484 : Rat), none, some (484 : Rat)] [(2424151 / 5000 : Rat)] (103838 : Int), datedRead (484 : Rat) #v[some (484 : Rat), none, some (484 : Rat)] [] (54077 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat), none] [(2204151 / 5000 : Rat)] (103838 : Int), datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat), none] [] (54078 : Int)], [datedRead (528 : Rat) #v[some (528 : Rat), some (528 : Rat), some (528 : Rat)] [(2644151 / 5000 : Rat)] (103838 : Int), datedRead (528 : Rat) #v[some (528 : Rat), some (528 : Rat), some (528 : Rat)] [(1322057 / 2500 : Rat)] (108154 : Int)]]
private def trace_F3_8310_K0_sx : List (ReadObservation 2) := [datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (927 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (1270807 / 2500 : Rat) #v[none, some (1270807 / 2500 : Rat)] [(2545281 / 5000 : Rat)] (127050 : Int), datedRead (1991651 / 5000 : Rat) #v[some (1991651 / 5000 : Rat), none] [(3991933 / 10000 : Rat)] (110123 : Int), datedRead (2431651 / 5000 : Rat) #v[some (2431651 / 5000 : Rat), none] [(4871933 / 10000 : Rat)] (110123 : Int), datedRead (2211651 / 5000 : Rat) #v[some (2211651 / 5000 : Rat), none] [(4431933 / 10000 : Rat)] (110123 : Int), datedRead (1325807 / 2500 : Rat) #v[some (2651651 / 5000 : Rat), some (1325807 / 2500 : Rat)] [(2652959 / 5000 : Rat)] (209737 : Int)]
private def trace_F3_8310_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)]]

def trace_F3_8310_K0 : TraceTables cascade_F3_8310_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F3_8310_K0_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F3_8310_K0_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F3_8310_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F3_8310_K0_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8310_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8310_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F3_8310_K0 : checks cascade_F3_8310_K0 trace_F3_8310_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F3_8310_K0 : checkCascadeValid cascade_F3_8310_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F3_8310_K0 : checkTrainingSeparation cascade_F3_8310_K0 left right trace_F3_8310_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F3_8310_K0 : checkCascadeCalibrationOneSided cascade_F3_8310_K0 left right trace_F3_8310_K0.observations trace_F3_8310_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F3_8310_K0 : ∀ x i, (trace_F3_8310_K0.observations.secondTest x i).fired = output cascade_F3_8310_K0 i x := by
  have checked := checks_F3_8310_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_F3_8310_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F3_8310_K0.observations trace_F3_8310_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F3_8310_K3 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[88534, 0, 0], #v[0, 38774, 38774]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[1262, 2506] : Vector Nat 2).get a,
    testingError := fun a => (#v[1262, 2506] : Vector Nat 2).get a,
    dose := 7651, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[55257, 44752] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 4500, testingError := fun _ => 4500,
    dose := 27432, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F3_8310_K3_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none, none] [] (88535 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat), some (0 : Rat)] [] (77546 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none, none] [] (96187 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat), some (22 : Rat)] [] (92851 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none, none] [(224151 / 5000 : Rat)] (103838 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat), some (44 : Rat)] [(112057 / 2500 : Rat)] (108154 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none, none] [(334151 / 5000 : Rat)] (103838 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat), some (66 : Rat)] [(167057 / 2500 : Rat)] (108154 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none, none] [(444151 / 5000 : Rat)] (103838 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat), some (88 : Rat)] [(222057 / 2500 : Rat)] (108154 : Int)]]
private def trace_F3_8310_K3_te : List (List (ReadObservation 3)) := [[datedRead (110 : Rat) #v[some (110 : Rat), none, none] [(554151 / 5000 : Rat)] (103838 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none, none] [] (0 : Int)], [datedRead (132 : Rat) #v[none, some (132 : Rat), some (132 : Rat)] [] (0 : Int), datedRead (132 : Rat) #v[none, some (132 : Rat), some (132 : Rat)] [(332057 / 2500 : Rat)] (108154 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none, none] [(774151 / 5000 : Rat)] (103838 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none, none] [] (0 : Int)], [datedRead (176 : Rat) #v[none, some (176 : Rat), some (176 : Rat)] [] (0 : Int), datedRead (176 : Rat) #v[none, some (176 : Rat), some (176 : Rat)] [(442057 / 2500 : Rat)] (108154 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none, none] [(994151 / 5000 : Rat)] (103838 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none, none] [] (0 : Int)], [datedRead (220 : Rat) #v[none, some (220 : Rat), some (220 : Rat)] [] (0 : Int), datedRead (220 : Rat) #v[none, some (220 : Rat), some (220 : Rat)] [(552057 / 2500 : Rat)] (108154 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none, none] [(1214151 / 5000 : Rat)] (103838 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none, none] [] (0 : Int)], [datedRead (264 : Rat) #v[none, some (264 : Rat), some (264 : Rat)] [] (0 : Int), datedRead (264 : Rat) #v[none, some (264 : Rat), some (264 : Rat)] [(662057 / 2500 : Rat)] (108154 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none, none] [(1434151 / 5000 : Rat)] (103838 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none, none] [] (0 : Int)], [datedRead (308 : Rat) #v[none, some (308 : Rat), some (308 : Rat)] [] (0 : Int), datedRead (308 : Rat) #v[none, some (308 : Rat), some (308 : Rat)] [(772057 / 2500 : Rat)] (108154 : Int)], [datedRead (330 : Rat) #v[some (330 : Rat), none, none] [(1654151 / 5000 : Rat)] (103838 : Int), datedRead (330 : Rat) #v[some (330 : Rat), none, none] [] (0 : Int)], [datedRead (352 : Rat) #v[none, some (352 : Rat), some (352 : Rat)] [] (0 : Int), datedRead (352 : Rat) #v[none, some (352 : Rat), some (352 : Rat)] [(882057 / 2500 : Rat)] (108154 : Int)]]
private def trace_F3_8310_K3_st : List (ReadObservation 2) := [datedRead (561651 / 5000 : Rat) #v[some (561651 / 5000 : Rat), none] [] (55252 : Int), datedRead (335807 / 2500 : Rat) #v[none, some (335807 / 2500 : Rat)] [] (44749 : Int), datedRead (781651 / 5000 : Rat) #v[some (781651 / 5000 : Rat), none] [] (82689 : Int), datedRead (445807 / 2500 : Rat) #v[none, some (445807 / 2500 : Rat)] [] (72185 : Int), datedRead (1001651 / 5000 : Rat) #v[some (1001651 / 5000 : Rat), none] [(2011933 / 10000 : Rat)] (110123 : Int), datedRead (555807 / 2500 : Rat) #v[none, some (555807 / 2500 : Rat)] [] (99619 : Int), datedRead (1221651 / 5000 : Rat) #v[some (1221651 / 5000 : Rat), none] [(2451933 / 10000 : Rat)] (110123 : Int), datedRead (665807 / 2500 : Rat) #v[none, some (665807 / 2500 : Rat)] [(1335281 / 5000 : Rat)] (127050 : Int), datedRead (1441651 / 5000 : Rat) #v[some (1441651 / 5000 : Rat), none] [(2891933 / 10000 : Rat)] (110123 : Int), datedRead (775807 / 2500 : Rat) #v[none, some (775807 / 2500 : Rat)] [(1555281 / 5000 : Rat)] (127050 : Int), datedRead (1661651 / 5000 : Rat) #v[some (1661651 / 5000 : Rat), none] [(3331933 / 10000 : Rat)] (110123 : Int), datedRead (885807 / 2500 : Rat) #v[none, some (885807 / 2500 : Rat)] [(1775281 / 5000 : Rat)] (127050 : Int)]
private def trace_F3_8310_K3_fx : List (List (ReadObservation 3)) := [[datedRead (374 : Rat) #v[none, none, none] [] (0 : Int), datedRead (374 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (462 : Rat) #v[none, none, some (462 : Rat)] [] (0 : Int), datedRead (462 : Rat) #v[none, none, some (462 : Rat)] [] (54077 : Int)], [datedRead (418 : Rat) #v[none, some (418 : Rat), none] [] (0 : Int), datedRead (418 : Rat) #v[none, some (418 : Rat), none] [] (54078 : Int)], [datedRead (506 : Rat) #v[none, some (506 : Rat), some (506 : Rat)] [] (0 : Int), datedRead (506 : Rat) #v[none, some (506 : Rat), some (506 : Rat)] [(1267057 / 2500 : Rat)] (108154 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), none, none] [(1984151 / 5000 : Rat)] (103838 : Int), datedRead (396 : Rat) #v[some (396 : Rat), none, none] [] (0 : Int)], [datedRead (484 : Rat) #v[some (484 : Rat), none, some (484 : Rat)] [(2424151 / 5000 : Rat)] (103838 : Int), datedRead (484 : Rat) #v[some (484 : Rat), none, some (484 : Rat)] [] (54077 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat), none] [(2204151 / 5000 : Rat)] (103838 : Int), datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat), none] [] (54078 : Int)], [datedRead (528 : Rat) #v[some (528 : Rat), some (528 : Rat), some (528 : Rat)] [(2644151 / 5000 : Rat)] (103838 : Int), datedRead (528 : Rat) #v[some (528 : Rat), some (528 : Rat), some (528 : Rat)] [(1322057 / 2500 : Rat)] (108154 : Int)]]
private def trace_F3_8310_K3_sx : List (ReadObservation 2) := [datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (927 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (1270807 / 2500 : Rat) #v[none, some (1270807 / 2500 : Rat)] [(2545281 / 5000 : Rat)] (127050 : Int), datedRead (1991651 / 5000 : Rat) #v[some (1991651 / 5000 : Rat), none] [(3991933 / 10000 : Rat)] (110123 : Int), datedRead (2431651 / 5000 : Rat) #v[some (2431651 / 5000 : Rat), none] [(4871933 / 10000 : Rat)] (110123 : Int), datedRead (2211651 / 5000 : Rat) #v[some (2211651 / 5000 : Rat), none] [(4431933 / 10000 : Rat)] (110123 : Int), datedRead (1325807 / 2500 : Rat) #v[some (2651651 / 5000 : Rat), some (1325807 / 2500 : Rat)] [(2652959 / 5000 : Rat)] (209737 : Int)]
private def trace_F3_8310_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)], #v[(0 : Int), (127050 : Int), (110123 : Int), (209737 : Int)]]

def trace_F3_8310_K3 : TraceTables cascade_F3_8310_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F3_8310_K3_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F3_8310_K3_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F3_8310_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F3_8310_K3_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8310_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8310_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F3_8310_K3 : checks cascade_F3_8310_K3 trace_F3_8310_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F3_8310_K3 : checkCascadeValid cascade_F3_8310_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F3_8310_K3 : checkTrainingSeparation cascade_F3_8310_K3 left right trace_F3_8310_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F3_8310_K3 : checkCascadeCalibrationOneSided cascade_F3_8310_K3 left right trace_F3_8310_K3.observations trace_F3_8310_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
