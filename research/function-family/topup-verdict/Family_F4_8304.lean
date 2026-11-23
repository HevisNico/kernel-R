import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F4, instance 8304.
Shape `Cascade 2 1 2`. Each `checks_*`, `valid_*`, `separation_*` and `calibration_*` theorem asserts a verdict
by `decide +kernel`; the file compiles only if the kernel agrees with every asserted value. -/

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup

open TwoLayer (SlotTiming ReadObservation)

private def term (a : Fin 2) : Pattern 2 :=
  if a = 0 then pattern [0] else pattern [1]

private def empty2 : ReadObservation 2 := datedRead 0 #v[none, none] [] 0

def left : SlotTiming := ⟨(1 / 50 : Rat), (11 / 10 : Rat), (22 : Rat)⟩
def right : SlotTiming := ⟨(11 / 10 : Rat), (11 / 5 : Rat), (19 : Rat)⟩

def checks (p : Cascade 2 1 2) (t : TraceTables p) : Bool :=
  checkCascadeValid p &&
  checkTrainingSeparation p left right t.observations &&
  checkCascadeCalibrationOneSided p left right t.observations t.scoreAt

def cascade_F4_8304_K0 : Cascade 2 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[86126, 0], #v[0, 79768]] : Vector (Vector Nat 2) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[106, 106] : Vector Nat 2).get a,
    testingError := fun a => (#v[106, 106] : Vector Nat 2).get a,
    dose := 7935, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[49057, 50948] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 356, testingError := fun _ => 356,
    dose := 26914, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F4_8304_K0_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none] [] (86124 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat)] [] (79767 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none] [] (94061 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat)] [] (87704 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none] [(56123 / 1250 : Rat)] (101997 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat)] [] (95640 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none] [(83623 / 1250 : Rat)] (101997 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat)] [(668417 / 10000 : Rat)] (103575 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none] [(111123 / 1250 : Rat)] (101997 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat)] [(888417 / 10000 : Rat)] (103575 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), none] [(138623 / 1250 : Rat)] (101997 : Int), datedRead (110 : Rat) #v[none, some (110 : Rat)] [(1108417 / 10000 : Rat)] (103575 : Int)]]
private def trace_F4_8304_K0_te : List (List (ReadObservation 2)) := [[datedRead (132 : Rat) #v[some (132 : Rat), none] [(166123 / 1250 : Rat)] (101997 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none] [] (0 : Int)], [datedRead (154 : Rat) #v[none, some (154 : Rat)] [] (0 : Int), datedRead (154 : Rat) #v[none, some (154 : Rat)] [(1548417 / 10000 : Rat)] (103575 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none] [(221123 / 1250 : Rat)] (101997 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none] [] (0 : Int)], [datedRead (198 : Rat) #v[none, some (198 : Rat)] [] (0 : Int), datedRead (198 : Rat) #v[none, some (198 : Rat)] [(1988417 / 10000 : Rat)] (103575 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none] [(276123 / 1250 : Rat)] (101997 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none] [] (0 : Int)], [datedRead (242 : Rat) #v[none, some (242 : Rat)] [] (0 : Int), datedRead (242 : Rat) #v[none, some (242 : Rat)] [(2428417 / 10000 : Rat)] (103575 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none] [(331123 / 1250 : Rat)] (101997 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat)] [] (0 : Int), datedRead (286 : Rat) #v[none, some (286 : Rat)] [(2868417 / 10000 : Rat)] (103575 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none] [(386123 / 1250 : Rat)] (101997 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none] [] (0 : Int)], [datedRead (330 : Rat) #v[none, some (330 : Rat)] [] (0 : Int), datedRead (330 : Rat) #v[none, some (330 : Rat)] [(3308417 / 10000 : Rat)] (103575 : Int)]]
private def trace_F4_8304_K0_st : List (ReadObservation 2) := [datedRead (83999 / 625 : Rat) #v[some (83999 / 625 : Rat), none] [] (49054 : Int), datedRead (1563417 / 10000 : Rat) #v[none, some (1563417 / 10000 : Rat)] [] (50946 : Int), datedRead (111499 / 625 : Rat) #v[some (111499 / 625 : Rat), none] [] (75972 : Int), datedRead (2003417 / 10000 : Rat) #v[none, some (2003417 / 10000 : Rat)] [] (77863 : Int), datedRead (138999 / 625 : Rat) #v[some (138999 / 625 : Rat), none] [(1116743 / 5000 : Rat)] (102887 : Int), datedRead (2443417 / 10000 : Rat) #v[none, some (2443417 / 10000 : Rat)] [(2452653 / 10000 : Rat)] (104778 : Int), datedRead (166499 / 625 : Rat) #v[some (166499 / 625 : Rat), none] [(1336743 / 5000 : Rat)] (102887 : Int), datedRead (2883417 / 10000 : Rat) #v[none, some (2883417 / 10000 : Rat)] [(2892653 / 10000 : Rat)] (104778 : Int), datedRead (193999 / 625 : Rat) #v[some (193999 / 625 : Rat), none] [(1556743 / 5000 : Rat)] (102887 : Int), datedRead (3323417 / 10000 : Rat) #v[none, some (3323417 / 10000 : Rat)] [(3332653 / 10000 : Rat)] (104778 : Int)]
private def trace_F4_8304_K0_fx : List (List (ReadObservation 2)) := [[datedRead (352 : Rat) #v[none, none] [] (0 : Int), datedRead (352 : Rat) #v[none, none] [] (0 : Int)], [datedRead (396 : Rat) #v[none, some (396 : Rat)] [] (0 : Int), datedRead (396 : Rat) #v[none, some (396 : Rat)] [(3968417 / 10000 : Rat)] (103575 : Int)], [datedRead (374 : Rat) #v[some (374 : Rat), none] [(468623 / 1250 : Rat)] (101997 : Int), datedRead (374 : Rat) #v[some (374 : Rat), none] [] (0 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat)] [(523623 / 1250 : Rat)] (101997 : Int), datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat)] [(4188417 / 10000 : Rat)] (103575 : Int)]]
private def trace_F4_8304_K0_sx : List (ReadObservation 2) := [datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (3983417 / 10000 : Rat) #v[none, some (3983417 / 10000 : Rat)] [(3992653 / 10000 : Rat)] (104778 : Int), datedRead (235249 / 625 : Rat) #v[some (235249 / 625 : Rat), none] [(1886743 / 5000 : Rat)] (102887 : Int), datedRead (4203417 / 10000 : Rat) #v[some (262749 / 625 : Rat), some (4203417 / 10000 : Rat)] [(4206117 / 10000 : Rat)] (207660 : Int)]
private def trace_F4_8304_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)]]

def trace_F4_8304_K0 : TraceTables cascade_F4_8304_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F4_8304_K0_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F4_8304_K0_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_F4_8304_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F4_8304_K0_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8304_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8304_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F4_8304_K0 : checks cascade_F4_8304_K0 trace_F4_8304_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F4_8304_K0 : checkCascadeValid cascade_F4_8304_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F4_8304_K0 : checkTrainingSeparation cascade_F4_8304_K0 left right trace_F4_8304_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F4_8304_K0 : checkCascadeCalibrationOneSided cascade_F4_8304_K0 left right trace_F4_8304_K0.observations trace_F4_8304_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F4_8304_K0 : ∀ x i, (trace_F4_8304_K0.observations.secondTest x i).fired = output cascade_F4_8304_K0 i x := by
  have checked := checks_F4_8304_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 2 cascade_F4_8304_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F4_8304_K0.observations trace_F4_8304_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F4_8304_K3 : Cascade 2 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[86126, 0], #v[0, 79768]] : Vector (Vector Nat 2) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[1303, 1300] : Vector Nat 2).get a,
    testingError := fun a => (#v[1303, 1300] : Vector Nat 2).get a,
    dose := 7935, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[49057, 50948] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 4436, testingError := fun _ => 4436,
    dose := 26914, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F4_8304_K3_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none] [] (86124 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat)] [] (79767 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none] [] (94061 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat)] [] (87704 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none] [(56123 / 1250 : Rat)] (101997 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat)] [] (95640 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none] [(83623 / 1250 : Rat)] (101997 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat)] [(668417 / 10000 : Rat)] (103575 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none] [(111123 / 1250 : Rat)] (101997 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat)] [(888417 / 10000 : Rat)] (103575 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), none] [(138623 / 1250 : Rat)] (101997 : Int), datedRead (110 : Rat) #v[none, some (110 : Rat)] [(1108417 / 10000 : Rat)] (103575 : Int)]]
private def trace_F4_8304_K3_te : List (List (ReadObservation 2)) := [[datedRead (132 : Rat) #v[some (132 : Rat), none] [(166123 / 1250 : Rat)] (101997 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none] [] (0 : Int)], [datedRead (154 : Rat) #v[none, some (154 : Rat)] [] (0 : Int), datedRead (154 : Rat) #v[none, some (154 : Rat)] [(1548417 / 10000 : Rat)] (103575 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none] [(221123 / 1250 : Rat)] (101997 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none] [] (0 : Int)], [datedRead (198 : Rat) #v[none, some (198 : Rat)] [] (0 : Int), datedRead (198 : Rat) #v[none, some (198 : Rat)] [(1988417 / 10000 : Rat)] (103575 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none] [(276123 / 1250 : Rat)] (101997 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none] [] (0 : Int)], [datedRead (242 : Rat) #v[none, some (242 : Rat)] [] (0 : Int), datedRead (242 : Rat) #v[none, some (242 : Rat)] [(2428417 / 10000 : Rat)] (103575 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none] [(331123 / 1250 : Rat)] (101997 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat)] [] (0 : Int), datedRead (286 : Rat) #v[none, some (286 : Rat)] [(2868417 / 10000 : Rat)] (103575 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none] [(386123 / 1250 : Rat)] (101997 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none] [] (0 : Int)], [datedRead (330 : Rat) #v[none, some (330 : Rat)] [] (0 : Int), datedRead (330 : Rat) #v[none, some (330 : Rat)] [(3308417 / 10000 : Rat)] (103575 : Int)]]
private def trace_F4_8304_K3_st : List (ReadObservation 2) := [datedRead (83999 / 625 : Rat) #v[some (83999 / 625 : Rat), none] [] (49054 : Int), datedRead (1563417 / 10000 : Rat) #v[none, some (1563417 / 10000 : Rat)] [] (50946 : Int), datedRead (111499 / 625 : Rat) #v[some (111499 / 625 : Rat), none] [] (75972 : Int), datedRead (2003417 / 10000 : Rat) #v[none, some (2003417 / 10000 : Rat)] [] (77863 : Int), datedRead (138999 / 625 : Rat) #v[some (138999 / 625 : Rat), none] [(1116743 / 5000 : Rat)] (102887 : Int), datedRead (2443417 / 10000 : Rat) #v[none, some (2443417 / 10000 : Rat)] [(2452653 / 10000 : Rat)] (104778 : Int), datedRead (166499 / 625 : Rat) #v[some (166499 / 625 : Rat), none] [(1336743 / 5000 : Rat)] (102887 : Int), datedRead (2883417 / 10000 : Rat) #v[none, some (2883417 / 10000 : Rat)] [(2892653 / 10000 : Rat)] (104778 : Int), datedRead (193999 / 625 : Rat) #v[some (193999 / 625 : Rat), none] [(1556743 / 5000 : Rat)] (102887 : Int), datedRead (3323417 / 10000 : Rat) #v[none, some (3323417 / 10000 : Rat)] [(3332653 / 10000 : Rat)] (104778 : Int)]
private def trace_F4_8304_K3_fx : List (List (ReadObservation 2)) := [[datedRead (352 : Rat) #v[none, none] [] (0 : Int), datedRead (352 : Rat) #v[none, none] [] (0 : Int)], [datedRead (396 : Rat) #v[none, some (396 : Rat)] [] (0 : Int), datedRead (396 : Rat) #v[none, some (396 : Rat)] [(3968417 / 10000 : Rat)] (103575 : Int)], [datedRead (374 : Rat) #v[some (374 : Rat), none] [(468623 / 1250 : Rat)] (101997 : Int), datedRead (374 : Rat) #v[some (374 : Rat), none] [] (0 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat)] [(523623 / 1250 : Rat)] (101997 : Int), datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat)] [(4188417 / 10000 : Rat)] (103575 : Int)]]
private def trace_F4_8304_K3_sx : List (ReadObservation 2) := [datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (3983417 / 10000 : Rat) #v[none, some (3983417 / 10000 : Rat)] [(3992653 / 10000 : Rat)] (104778 : Int), datedRead (235249 / 625 : Rat) #v[some (235249 / 625 : Rat), none] [(1886743 / 5000 : Rat)] (102887 : Int), datedRead (4203417 / 10000 : Rat) #v[some (262749 / 625 : Rat), some (4203417 / 10000 : Rat)] [(4206117 / 10000 : Rat)] (207660 : Int)]
private def trace_F4_8304_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)], #v[(0 : Int), (104778 : Int), (102887 : Int), (207660 : Int)]]

def trace_F4_8304_K3 : TraceTables cascade_F4_8304_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F4_8304_K3_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F4_8304_K3_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_F4_8304_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F4_8304_K3_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8304_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8304_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F4_8304_K3 : checks cascade_F4_8304_K3 trace_F4_8304_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F4_8304_K3 : checkCascadeValid cascade_F4_8304_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F4_8304_K3 : checkTrainingSeparation cascade_F4_8304_K3 left right trace_F4_8304_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F4_8304_K3 : checkCascadeCalibrationOneSided cascade_F4_8304_K3 left right trace_F4_8304_K3.observations trace_F4_8304_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
