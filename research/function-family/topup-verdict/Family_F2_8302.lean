import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F2, instance 8302.
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

def cascade_F2_8302_K0 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[33642, 33642, 0], #v[35254, 0, 35254]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[215, 215] : Vector Nat 2).get a,
    testingError := fun a => (#v[215, 215] : Vector Nat 2).get a,
    dose := 8092, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[47389, 52620] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 292, testingError := fun _ => 292,
    dose := 21950, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F2_8302_K0_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), some (0 : Rat), none] [] (67282 : Int), datedRead (0 : Rat) #v[some (0 : Rat), none, some (0 : Rat)] [] (70506 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), some (22 : Rat), none] [] (83468 : Int), datedRead (22 : Rat) #v[some (22 : Rat), none, some (22 : Rat)] [] (86692 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), some (44 : Rat), none] [] (99654 : Int), datedRead (44 : Rat) #v[some (44 : Rat), none, some (44 : Rat)] [(449247 / 10000 : Rat)] (102878 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), some (66 : Rat), none] [(133469 / 2000 : Rat)] (115838 : Int), datedRead (66 : Rat) #v[some (66 : Rat), none, some (66 : Rat)] [(669247 / 10000 : Rat)] (102878 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), some (88 : Rat), none] [(177469 / 2000 : Rat)] (115838 : Int), datedRead (88 : Rat) #v[some (88 : Rat), none, some (88 : Rat)] [(889247 / 10000 : Rat)] (102878 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [(221469 / 2000 : Rat)] (115838 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none, some (110 : Rat)] [(1109247 / 10000 : Rat)] (102878 : Int)]]
private def trace_F2_8302_K0_te : List (List (ReadObservation 3)) := [[datedRead (132 : Rat) #v[some (132 : Rat), some (132 : Rat), none] [(265469 / 2000 : Rat)] (115838 : Int), datedRead (132 : Rat) #v[some (132 : Rat), some (132 : Rat), none] [] (51439 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none, some (154 : Rat)] [] (57920 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none, some (154 : Rat)] [(1549247 / 10000 : Rat)] (102878 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), some (176 : Rat), none] [(353469 / 2000 : Rat)] (115838 : Int), datedRead (176 : Rat) #v[some (176 : Rat), some (176 : Rat), none] [] (51439 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none, some (198 : Rat)] [] (57920 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none, some (198 : Rat)] [(1989247 / 10000 : Rat)] (102878 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), some (220 : Rat), none] [(441469 / 2000 : Rat)] (115838 : Int), datedRead (220 : Rat) #v[some (220 : Rat), some (220 : Rat), none] [] (51439 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none, some (242 : Rat)] [] (57920 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none, some (242 : Rat)] [(2429247 / 10000 : Rat)] (102878 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), some (264 : Rat), none] [(529469 / 2000 : Rat)] (115838 : Int), datedRead (264 : Rat) #v[some (264 : Rat), some (264 : Rat), none] [] (51439 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none, some (286 : Rat)] [] (57920 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none, some (286 : Rat)] [(2869247 / 10000 : Rat)] (102878 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), some (308 : Rat), none] [(617469 / 2000 : Rat)] (115838 : Int), datedRead (308 : Rat) #v[some (308 : Rat), some (308 : Rat), none] [] (51439 : Int)], [datedRead (330 : Rat) #v[some (330 : Rat), none, some (330 : Rat)] [] (57920 : Int), datedRead (330 : Rat) #v[some (330 : Rat), none, some (330 : Rat)] [(3309247 / 10000 : Rat)] (102878 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), some (352 : Rat), none] [(705469 / 2000 : Rat)] (115838 : Int), datedRead (352 : Rat) #v[some (352 : Rat), some (352 : Rat), none] [] (51439 : Int)], [datedRead (374 : Rat) #v[some (374 : Rat), none, some (374 : Rat)] [] (57920 : Int), datedRead (374 : Rat) #v[some (374 : Rat), none, some (374 : Rat)] [(3749247 / 10000 : Rat)] (102878 : Int)]]
private def trace_F2_8302_K0_st : List (ReadObservation 2) := [datedRead (268469 / 2000 : Rat) #v[some (268469 / 2000 : Rat), none] [] (47385 : Int), datedRead (1564247 / 10000 : Rat) #v[none, some (1564247 / 10000 : Rat)] [] (52617 : Int), datedRead (356469 / 2000 : Rat) #v[some (356469 / 2000 : Rat), none] [] (69339 : Int), datedRead (2004247 / 10000 : Rat) #v[none, some (2004247 / 10000 : Rat)] [] (74570 : Int), datedRead (444469 / 2000 : Rat) #v[some (444469 / 2000 : Rat), none] [] (91291 : Int), datedRead (2444247 / 10000 : Rat) #v[none, some (2444247 / 10000 : Rat)] [] (96522 : Int), datedRead (532469 / 2000 : Rat) #v[some (532469 / 2000 : Rat), none] [(534081 / 2000 : Rat)] (113241 : Int), datedRead (2884247 / 10000 : Rat) #v[none, some (2884247 / 10000 : Rat)] [(361479 / 1250 : Rat)] (118472 : Int), datedRead (620469 / 2000 : Rat) #v[some (620469 / 2000 : Rat), none] [(622081 / 2000 : Rat)] (113241 : Int), datedRead (3324247 / 10000 : Rat) #v[none, some (3324247 / 10000 : Rat)] [(416479 / 1250 : Rat)] (118472 : Int), datedRead (708469 / 2000 : Rat) #v[some (708469 / 2000 : Rat), none] [(710081 / 2000 : Rat)] (113241 : Int), datedRead (3764247 / 10000 : Rat) #v[none, some (3764247 / 10000 : Rat)] [(471479 / 1250 : Rat)] (118472 : Int)]
private def trace_F2_8302_K0_fx : List (List (ReadObservation 3)) := [[datedRead (396 : Rat) #v[none, none, none] [] (0 : Int), datedRead (396 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (484 : Rat) #v[none, none, some (484 : Rat)] [] (0 : Int), datedRead (484 : Rat) #v[none, none, some (484 : Rat)] [] (51439 : Int)], [datedRead (440 : Rat) #v[none, some (440 : Rat), none] [] (57919 : Int), datedRead (440 : Rat) #v[none, some (440 : Rat), none] [] (0 : Int)], [datedRead (528 : Rat) #v[none, some (528 : Rat), some (528 : Rat)] [] (57919 : Int), datedRead (528 : Rat) #v[none, some (528 : Rat), some (528 : Rat)] [] (51439 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), none, none] [] (57920 : Int), datedRead (418 : Rat) #v[some (418 : Rat), none, none] [] (51439 : Int)], [datedRead (506 : Rat) #v[some (506 : Rat), none, some (506 : Rat)] [] (57920 : Int), datedRead (506 : Rat) #v[some (506 : Rat), none, some (506 : Rat)] [(5069247 / 10000 : Rat)] (102878 : Int)], [datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat), none] [(925469 / 2000 : Rat)] (115838 : Int), datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat), none] [] (51439 : Int)], [datedRead (550 : Rat) #v[some (550 : Rat), some (550 : Rat), some (550 : Rat)] [(1101469 / 2000 : Rat)] (115838 : Int), datedRead (550 : Rat) #v[some (550 : Rat), some (550 : Rat), some (550 : Rat)] [(5509247 / 10000 : Rat)] (102878 : Int)]]
private def trace_F2_8302_K0_sx : List (ReadObservation 2) := [datedRead (795 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (971 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (883 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (1059 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (5084247 / 10000 : Rat) #v[none, some (5084247 / 10000 : Rat)] [(636479 / 1250 : Rat)] (118472 : Int), datedRead (928469 / 2000 : Rat) #v[some (928469 / 2000 : Rat), none] [(930081 / 2000 : Rat)] (113241 : Int), datedRead (1104469 / 2000 : Rat) #v[some (1104469 / 2000 : Rat), some (5524247 / 10000 : Rat)] [(345414 / 625 : Rat)] (231707 : Int)]
private def trace_F2_8302_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)]]

def trace_F2_8302_K0 : TraceTables cascade_F2_8302_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F2_8302_K0_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F2_8302_K0_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F2_8302_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F2_8302_K0_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8302_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8302_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F2_8302_K0 : checks cascade_F2_8302_K0 trace_F2_8302_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F2_8302_K0 : checkCascadeValid cascade_F2_8302_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F2_8302_K0 : checkTrainingSeparation cascade_F2_8302_K0 left right trace_F2_8302_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F2_8302_K0 : checkCascadeCalibrationOneSided cascade_F2_8302_K0 left right trace_F2_8302_K0.observations trace_F2_8302_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F2_8302_K0 : ∀ x i, (trace_F2_8302_K0.observations.secondTest x i).fired = output cascade_F2_8302_K0 i x := by
  have checked := checks_F2_8302_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_F2_8302_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F2_8302_K0.observations trace_F2_8302_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F2_8302_K3 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[33642, 33642, 0], #v[35254, 0, 35254]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[2654, 2662] : Vector Nat 2).get a,
    testingError := fun a => (#v[2654, 2662] : Vector Nat 2).get a,
    dose := 8092, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[47389, 52620] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 3606, testingError := fun _ => 3606,
    dose := 21950, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F2_8302_K3_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), some (0 : Rat), none] [] (67282 : Int), datedRead (0 : Rat) #v[some (0 : Rat), none, some (0 : Rat)] [] (70506 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), some (22 : Rat), none] [] (83468 : Int), datedRead (22 : Rat) #v[some (22 : Rat), none, some (22 : Rat)] [] (86692 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), some (44 : Rat), none] [] (99654 : Int), datedRead (44 : Rat) #v[some (44 : Rat), none, some (44 : Rat)] [(449247 / 10000 : Rat)] (102878 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), some (66 : Rat), none] [(133469 / 2000 : Rat)] (115838 : Int), datedRead (66 : Rat) #v[some (66 : Rat), none, some (66 : Rat)] [(669247 / 10000 : Rat)] (102878 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), some (88 : Rat), none] [(177469 / 2000 : Rat)] (115838 : Int), datedRead (88 : Rat) #v[some (88 : Rat), none, some (88 : Rat)] [(889247 / 10000 : Rat)] (102878 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [(221469 / 2000 : Rat)] (115838 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none, some (110 : Rat)] [(1109247 / 10000 : Rat)] (102878 : Int)]]
private def trace_F2_8302_K3_te : List (List (ReadObservation 3)) := [[datedRead (132 : Rat) #v[some (132 : Rat), some (132 : Rat), none] [(265469 / 2000 : Rat)] (115838 : Int), datedRead (132 : Rat) #v[some (132 : Rat), some (132 : Rat), none] [] (51439 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none, some (154 : Rat)] [] (57920 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none, some (154 : Rat)] [(1549247 / 10000 : Rat)] (102878 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), some (176 : Rat), none] [(353469 / 2000 : Rat)] (115838 : Int), datedRead (176 : Rat) #v[some (176 : Rat), some (176 : Rat), none] [] (51439 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none, some (198 : Rat)] [] (57920 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none, some (198 : Rat)] [(1989247 / 10000 : Rat)] (102878 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), some (220 : Rat), none] [(441469 / 2000 : Rat)] (115838 : Int), datedRead (220 : Rat) #v[some (220 : Rat), some (220 : Rat), none] [] (51439 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none, some (242 : Rat)] [] (57920 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none, some (242 : Rat)] [(2429247 / 10000 : Rat)] (102878 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), some (264 : Rat), none] [(529469 / 2000 : Rat)] (115838 : Int), datedRead (264 : Rat) #v[some (264 : Rat), some (264 : Rat), none] [] (51439 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none, some (286 : Rat)] [] (57920 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none, some (286 : Rat)] [(2869247 / 10000 : Rat)] (102878 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), some (308 : Rat), none] [(617469 / 2000 : Rat)] (115838 : Int), datedRead (308 : Rat) #v[some (308 : Rat), some (308 : Rat), none] [] (51439 : Int)], [datedRead (330 : Rat) #v[some (330 : Rat), none, some (330 : Rat)] [] (57920 : Int), datedRead (330 : Rat) #v[some (330 : Rat), none, some (330 : Rat)] [(3309247 / 10000 : Rat)] (102878 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), some (352 : Rat), none] [(705469 / 2000 : Rat)] (115838 : Int), datedRead (352 : Rat) #v[some (352 : Rat), some (352 : Rat), none] [] (51439 : Int)], [datedRead (374 : Rat) #v[some (374 : Rat), none, some (374 : Rat)] [] (57920 : Int), datedRead (374 : Rat) #v[some (374 : Rat), none, some (374 : Rat)] [(3749247 / 10000 : Rat)] (102878 : Int)]]
private def trace_F2_8302_K3_st : List (ReadObservation 2) := [datedRead (268469 / 2000 : Rat) #v[some (268469 / 2000 : Rat), none] [] (47385 : Int), datedRead (1564247 / 10000 : Rat) #v[none, some (1564247 / 10000 : Rat)] [] (52617 : Int), datedRead (356469 / 2000 : Rat) #v[some (356469 / 2000 : Rat), none] [] (69339 : Int), datedRead (2004247 / 10000 : Rat) #v[none, some (2004247 / 10000 : Rat)] [] (74570 : Int), datedRead (444469 / 2000 : Rat) #v[some (444469 / 2000 : Rat), none] [] (91291 : Int), datedRead (2444247 / 10000 : Rat) #v[none, some (2444247 / 10000 : Rat)] [] (96522 : Int), datedRead (532469 / 2000 : Rat) #v[some (532469 / 2000 : Rat), none] [(534081 / 2000 : Rat)] (113241 : Int), datedRead (2884247 / 10000 : Rat) #v[none, some (2884247 / 10000 : Rat)] [(361479 / 1250 : Rat)] (118472 : Int), datedRead (620469 / 2000 : Rat) #v[some (620469 / 2000 : Rat), none] [(622081 / 2000 : Rat)] (113241 : Int), datedRead (3324247 / 10000 : Rat) #v[none, some (3324247 / 10000 : Rat)] [(416479 / 1250 : Rat)] (118472 : Int), datedRead (708469 / 2000 : Rat) #v[some (708469 / 2000 : Rat), none] [(710081 / 2000 : Rat)] (113241 : Int), datedRead (3764247 / 10000 : Rat) #v[none, some (3764247 / 10000 : Rat)] [(471479 / 1250 : Rat)] (118472 : Int)]
private def trace_F2_8302_K3_fx : List (List (ReadObservation 3)) := [[datedRead (396 : Rat) #v[none, none, none] [] (0 : Int), datedRead (396 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (484 : Rat) #v[none, none, some (484 : Rat)] [] (0 : Int), datedRead (484 : Rat) #v[none, none, some (484 : Rat)] [] (51439 : Int)], [datedRead (440 : Rat) #v[none, some (440 : Rat), none] [] (57919 : Int), datedRead (440 : Rat) #v[none, some (440 : Rat), none] [] (0 : Int)], [datedRead (528 : Rat) #v[none, some (528 : Rat), some (528 : Rat)] [] (57919 : Int), datedRead (528 : Rat) #v[none, some (528 : Rat), some (528 : Rat)] [] (51439 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), none, none] [] (57920 : Int), datedRead (418 : Rat) #v[some (418 : Rat), none, none] [] (51439 : Int)], [datedRead (506 : Rat) #v[some (506 : Rat), none, some (506 : Rat)] [] (57920 : Int), datedRead (506 : Rat) #v[some (506 : Rat), none, some (506 : Rat)] [(5069247 / 10000 : Rat)] (102878 : Int)], [datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat), none] [(925469 / 2000 : Rat)] (115838 : Int), datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat), none] [] (51439 : Int)], [datedRead (550 : Rat) #v[some (550 : Rat), some (550 : Rat), some (550 : Rat)] [(1101469 / 2000 : Rat)] (115838 : Int), datedRead (550 : Rat) #v[some (550 : Rat), some (550 : Rat), some (550 : Rat)] [(5509247 / 10000 : Rat)] (102878 : Int)]]
private def trace_F2_8302_K3_sx : List (ReadObservation 2) := [datedRead (795 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (971 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (883 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (1059 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (5084247 / 10000 : Rat) #v[none, some (5084247 / 10000 : Rat)] [(636479 / 1250 : Rat)] (118472 : Int), datedRead (928469 / 2000 : Rat) #v[some (928469 / 2000 : Rat), none] [(930081 / 2000 : Rat)] (113241 : Int), datedRead (1104469 / 2000 : Rat) #v[some (1104469 / 2000 : Rat), some (5524247 / 10000 : Rat)] [(345414 / 625 : Rat)] (231707 : Int)]
private def trace_F2_8302_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)], #v[(0 : Int), (118472 : Int), (113241 : Int), (231707 : Int)]]

def trace_F2_8302_K3 : TraceTables cascade_F2_8302_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F2_8302_K3_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F2_8302_K3_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F2_8302_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F2_8302_K3_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8302_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8302_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F2_8302_K3 : checks cascade_F2_8302_K3 trace_F2_8302_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F2_8302_K3 : checkCascadeValid cascade_F2_8302_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F2_8302_K3 : checkTrainingSeparation cascade_F2_8302_K3 left right trace_F2_8302_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F2_8302_K3 : checkCascadeCalibrationOneSided cascade_F2_8302_K3 left right trace_F2_8302_K3.observations trace_F2_8302_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
