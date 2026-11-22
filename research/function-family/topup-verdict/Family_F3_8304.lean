import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F3, instance 8304.
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

def cascade_F3_8304_K0 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[86124, 0, 0], #v[0, 34699, 34699]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[106, 210] : Vector Nat 2).get a,
    testingError := fun a => (#v[106, 210] : Vector Nat 2).get a,
    dose := 7936, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[49057, 50948] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 356, testingError := fun _ => 356,
    dose := 26914, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F3_8304_K0_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none, none] [] (86124 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat), some (0 : Rat)] [] (69396 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none, none] [] (94061 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat), some (22 : Rat)] [] (85270 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none, none] [(56123 / 1250 : Rat)] (101997 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat), some (44 : Rat)] [(28104 / 625 : Rat)] (101144 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none, none] [(83623 / 1250 : Rat)] (101997 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat), some (66 : Rat)] [(41854 / 625 : Rat)] (101144 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none, none] [(111123 / 1250 : Rat)] (101997 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat), some (88 : Rat)] [(55604 / 625 : Rat)] (101144 : Int)]]
private def trace_F3_8304_K0_te : List (List (ReadObservation 3)) := [[datedRead (110 : Rat) #v[some (110 : Rat), none, none] [(138623 / 1250 : Rat)] (101997 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none, none] [] (0 : Int)], [datedRead (132 : Rat) #v[none, some (132 : Rat), some (132 : Rat)] [] (0 : Int), datedRead (132 : Rat) #v[none, some (132 : Rat), some (132 : Rat)] [(83104 / 625 : Rat)] (101144 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none, none] [(193623 / 1250 : Rat)] (101997 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none, none] [] (0 : Int)], [datedRead (176 : Rat) #v[none, some (176 : Rat), some (176 : Rat)] [] (0 : Int), datedRead (176 : Rat) #v[none, some (176 : Rat), some (176 : Rat)] [(110604 / 625 : Rat)] (101144 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none, none] [(248623 / 1250 : Rat)] (101997 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none, none] [] (0 : Int)], [datedRead (220 : Rat) #v[none, some (220 : Rat), some (220 : Rat)] [] (0 : Int), datedRead (220 : Rat) #v[none, some (220 : Rat), some (220 : Rat)] [(138104 / 625 : Rat)] (101144 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none, none] [(303623 / 1250 : Rat)] (101997 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none, none] [] (0 : Int)], [datedRead (264 : Rat) #v[none, some (264 : Rat), some (264 : Rat)] [] (0 : Int), datedRead (264 : Rat) #v[none, some (264 : Rat), some (264 : Rat)] [(165604 / 625 : Rat)] (101144 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none, none] [(358623 / 1250 : Rat)] (101997 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none, none] [] (0 : Int)], [datedRead (308 : Rat) #v[none, some (308 : Rat), some (308 : Rat)] [] (0 : Int), datedRead (308 : Rat) #v[none, some (308 : Rat), some (308 : Rat)] [(193104 / 625 : Rat)] (101144 : Int)]]
private def trace_F3_8304_K0_st : List (ReadObservation 2) := [datedRead (70249 / 625 : Rat) #v[some (70249 / 625 : Rat), none] [] (49054 : Int), datedRead (168083 / 1250 : Rat) #v[none, some (168083 / 1250 : Rat)] [] (50946 : Int), datedRead (97749 / 625 : Rat) #v[some (97749 / 625 : Rat), none] [] (75972 : Int), datedRead (223083 / 1250 : Rat) #v[none, some (223083 / 1250 : Rat)] [] (77863 : Int), datedRead (125249 / 625 : Rat) #v[some (125249 / 625 : Rat), none] [(1006743 / 5000 : Rat)] (102887 : Int), datedRead (278083 / 1250 : Rat) #v[none, some (278083 / 1250 : Rat)] [(22339 / 100 : Rat)] (104778 : Int), datedRead (152749 / 625 : Rat) #v[some (152749 / 625 : Rat), none] [(1226743 / 5000 : Rat)] (102887 : Int), datedRead (333083 / 1250 : Rat) #v[none, some (333083 / 1250 : Rat)] [(26739 / 100 : Rat)] (104778 : Int), datedRead (180249 / 625 : Rat) #v[some (180249 / 625 : Rat), none] [(1446743 / 5000 : Rat)] (102887 : Int), datedRead (388083 / 1250 : Rat) #v[none, some (388083 / 1250 : Rat)] [(31139 / 100 : Rat)] (104778 : Int)]
private def trace_F3_8304_K0_fx : List (List (ReadObservation 3)) := [[datedRead (330 : Rat) #v[none, none, none] [] (0 : Int), datedRead (330 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (0 : Int), datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (50572 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (0 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (50572 : Int)], [datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (0 : Int), datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [(289354 / 625 : Rat)] (101144 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none, none] [(441123 / 1250 : Rat)] (101997 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (0 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [(551123 / 1250 : Rat)] (101997 : Int), datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [] (50572 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [(496123 / 1250 : Rat)] (101997 : Int), datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [] (50572 : Int)], [datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(606123 / 1250 : Rat)] (101997 : Int), datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(303104 / 625 : Rat)] (101144 : Int)]]
private def trace_F3_8304_K0_sx : List (ReadObservation 2) := [datedRead (663 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (580583 / 1250 : Rat) #v[none, some (580583 / 1250 : Rat)] [(46539 / 100 : Rat)] (104778 : Int), datedRead (221499 / 625 : Rat) #v[some (221499 / 625 : Rat), none] [(1776743 / 5000 : Rat)] (102887 : Int), datedRead (276499 / 625 : Rat) #v[some (276499 / 625 : Rat), none] [(2216743 / 5000 : Rat)] (102887 : Int), datedRead (248999 / 625 : Rat) #v[some (248999 / 625 : Rat), none] [(1996743 / 5000 : Rat)] (102887 : Int), datedRead (303999 / 625 : Rat) #v[some (303999 / 625 : Rat), some (608083 / 1250 : Rat)] [(1216671 / 2500 : Rat)] (207660 : Int)]
private def trace_F3_8304_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)]]

def trace_F3_8304_K0 : TraceTables cascade_F3_8304_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F3_8304_K0_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F3_8304_K0_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F3_8304_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F3_8304_K0_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8304_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8304_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F3_8304_K0 : checks cascade_F3_8304_K0 trace_F3_8304_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F3_8304_K0 : checkCascadeValid cascade_F3_8304_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F3_8304_K0 : checkTrainingSeparation cascade_F3_8304_K0 left right trace_F3_8304_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F3_8304_K0 : checkCascadeCalibrationOneSided cascade_F3_8304_K0 left right trace_F3_8304_K0.observations trace_F3_8304_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F3_8304_K0 : ∀ x i, (trace_F3_8304_K0.observations.secondTest x i).fired = output cascade_F3_8304_K0 i x := by
  have checked := checks_F3_8304_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_F3_8304_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F3_8304_K0.observations trace_F3_8304_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F3_8304_K3 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[86124, 0, 0], #v[0, 34699, 34699]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[1303, 2602] : Vector Nat 2).get a,
    testingError := fun a => (#v[1303, 2602] : Vector Nat 2).get a,
    dose := 7936, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[49057, 50948] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 4436, testingError := fun _ => 4436,
    dose := 26914, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F3_8304_K3_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none, none] [] (86124 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat), some (0 : Rat)] [] (69396 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none, none] [] (94061 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat), some (22 : Rat)] [] (85270 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none, none] [(56123 / 1250 : Rat)] (101997 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat), some (44 : Rat)] [(28104 / 625 : Rat)] (101144 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none, none] [(83623 / 1250 : Rat)] (101997 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat), some (66 : Rat)] [(41854 / 625 : Rat)] (101144 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none, none] [(111123 / 1250 : Rat)] (101997 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat), some (88 : Rat)] [(55604 / 625 : Rat)] (101144 : Int)]]
private def trace_F3_8304_K3_te : List (List (ReadObservation 3)) := [[datedRead (110 : Rat) #v[some (110 : Rat), none, none] [(138623 / 1250 : Rat)] (101997 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none, none] [] (0 : Int)], [datedRead (132 : Rat) #v[none, some (132 : Rat), some (132 : Rat)] [] (0 : Int), datedRead (132 : Rat) #v[none, some (132 : Rat), some (132 : Rat)] [(83104 / 625 : Rat)] (101144 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none, none] [(193623 / 1250 : Rat)] (101997 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none, none] [] (0 : Int)], [datedRead (176 : Rat) #v[none, some (176 : Rat), some (176 : Rat)] [] (0 : Int), datedRead (176 : Rat) #v[none, some (176 : Rat), some (176 : Rat)] [(110604 / 625 : Rat)] (101144 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none, none] [(248623 / 1250 : Rat)] (101997 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none, none] [] (0 : Int)], [datedRead (220 : Rat) #v[none, some (220 : Rat), some (220 : Rat)] [] (0 : Int), datedRead (220 : Rat) #v[none, some (220 : Rat), some (220 : Rat)] [(138104 / 625 : Rat)] (101144 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none, none] [(303623 / 1250 : Rat)] (101997 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none, none] [] (0 : Int)], [datedRead (264 : Rat) #v[none, some (264 : Rat), some (264 : Rat)] [] (0 : Int), datedRead (264 : Rat) #v[none, some (264 : Rat), some (264 : Rat)] [(165604 / 625 : Rat)] (101144 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none, none] [(358623 / 1250 : Rat)] (101997 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none, none] [] (0 : Int)], [datedRead (308 : Rat) #v[none, some (308 : Rat), some (308 : Rat)] [] (0 : Int), datedRead (308 : Rat) #v[none, some (308 : Rat), some (308 : Rat)] [(193104 / 625 : Rat)] (101144 : Int)]]
private def trace_F3_8304_K3_st : List (ReadObservation 2) := [datedRead (70249 / 625 : Rat) #v[some (70249 / 625 : Rat), none] [] (49054 : Int), datedRead (168083 / 1250 : Rat) #v[none, some (168083 / 1250 : Rat)] [] (50946 : Int), datedRead (97749 / 625 : Rat) #v[some (97749 / 625 : Rat), none] [] (75972 : Int), datedRead (223083 / 1250 : Rat) #v[none, some (223083 / 1250 : Rat)] [] (77863 : Int), datedRead (125249 / 625 : Rat) #v[some (125249 / 625 : Rat), none] [(1006743 / 5000 : Rat)] (102887 : Int), datedRead (278083 / 1250 : Rat) #v[none, some (278083 / 1250 : Rat)] [(22339 / 100 : Rat)] (104778 : Int), datedRead (152749 / 625 : Rat) #v[some (152749 / 625 : Rat), none] [(1226743 / 5000 : Rat)] (102887 : Int), datedRead (333083 / 1250 : Rat) #v[none, some (333083 / 1250 : Rat)] [(26739 / 100 : Rat)] (104778 : Int), datedRead (180249 / 625 : Rat) #v[some (180249 / 625 : Rat), none] [(1446743 / 5000 : Rat)] (102887 : Int), datedRead (388083 / 1250 : Rat) #v[none, some (388083 / 1250 : Rat)] [(31139 / 100 : Rat)] (104778 : Int)]
private def trace_F3_8304_K3_fx : List (List (ReadObservation 3)) := [[datedRead (330 : Rat) #v[none, none, none] [] (0 : Int), datedRead (330 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (0 : Int), datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (50572 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (0 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (50572 : Int)], [datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (0 : Int), datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [(289354 / 625 : Rat)] (101144 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none, none] [(441123 / 1250 : Rat)] (101997 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (0 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [(551123 / 1250 : Rat)] (101997 : Int), datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [] (50572 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [(496123 / 1250 : Rat)] (101997 : Int), datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [] (50572 : Int)], [datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(606123 / 1250 : Rat)] (101997 : Int), datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(303104 / 625 : Rat)] (101144 : Int)]]
private def trace_F3_8304_K3_sx : List (ReadObservation 2) := [datedRead (663 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (580583 / 1250 : Rat) #v[none, some (580583 / 1250 : Rat)] [(46539 / 100 : Rat)] (104778 : Int), datedRead (221499 / 625 : Rat) #v[some (221499 / 625 : Rat), none] [(1776743 / 5000 : Rat)] (102887 : Int), datedRead (276499 / 625 : Rat) #v[some (276499 / 625 : Rat), none] [(2216743 / 5000 : Rat)] (102887 : Int), datedRead (248999 / 625 : Rat) #v[some (248999 / 625 : Rat), none] [(1996743 / 5000 : Rat)] (102887 : Int), datedRead (303999 / 625 : Rat) #v[some (303999 / 625 : Rat), some (608083 / 1250 : Rat)] [(1216671 / 2500 : Rat)] (207660 : Int)]
private def trace_F3_8304_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)]]

def trace_F3_8304_K3 : TraceTables cascade_F3_8304_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F3_8304_K3_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F3_8304_K3_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F3_8304_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F3_8304_K3_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8304_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8304_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F3_8304_K3 : checks cascade_F3_8304_K3 trace_F3_8304_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F3_8304_K3 : checkCascadeValid cascade_F3_8304_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F3_8304_K3 : checkTrainingSeparation cascade_F3_8304_K3 left right trace_F3_8304_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F3_8304_K3 : checkCascadeCalibrationOneSided cascade_F3_8304_K3 left right trace_F3_8304_K3.observations trace_F3_8304_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
