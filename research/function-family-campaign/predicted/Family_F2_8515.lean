import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F2, instance 8515.
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

def cascade_F2_8515_K0 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[36160, 36159, 0], #v[41736, 0, 41735]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[194, 194] : Vector Nat 2).get a,
    testingError := fun a => (#v[194, 194] : Vector Nat 2).get a,
    dose := 7281, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[49697, 50306] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 411, testingError := fun _ => 411,
    dose := 31214, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F2_8515_K0_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), some (0 : Rat), none] [] (72318 : Int), datedRead (0 : Rat) #v[some (0 : Rat), none, some (0 : Rat)] [] (83470 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), some (22 : Rat), none] [] (86883 : Int), datedRead (22 : Rat) #v[some (22 : Rat), none, some (22 : Rat)] [] (98035 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), some (44 : Rat), none] [(449551 / 10000 : Rat)] (101446 : Int), datedRead (44 : Rat) #v[some (44 : Rat), none, some (44 : Rat)] [(27971 / 625 : Rat)] (112598 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), some (66 : Rat), none] [(669551 / 10000 : Rat)] (101446 : Int), datedRead (66 : Rat) #v[some (66 : Rat), none, some (66 : Rat)] [(41721 / 625 : Rat)] (112598 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), some (88 : Rat), none] [(889551 / 10000 : Rat)] (101446 : Int), datedRead (88 : Rat) #v[some (88 : Rat), none, some (88 : Rat)] [(55471 / 625 : Rat)] (112598 : Int)]]
private def trace_F2_8515_K0_te : List (List (ReadObservation 3)) := [[datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [(1109551 / 10000 : Rat)] (101446 : Int), datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [] (56300 : Int)], [datedRead (132 : Rat) #v[some (132 : Rat), none, some (132 : Rat)] [] (50724 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none, some (132 : Rat)] [(82971 / 625 : Rat)] (112598 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat), none] [(1549551 / 10000 : Rat)] (101446 : Int), datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat), none] [] (56300 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none, some (176 : Rat)] [] (50724 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none, some (176 : Rat)] [(110471 / 625 : Rat)] (112598 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat), none] [(1989551 / 10000 : Rat)] (101446 : Int), datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat), none] [] (56300 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none, some (220 : Rat)] [] (50724 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none, some (220 : Rat)] [(137971 / 625 : Rat)] (112598 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), some (242 : Rat), none] [(2429551 / 10000 : Rat)] (101446 : Int), datedRead (242 : Rat) #v[some (242 : Rat), some (242 : Rat), none] [] (56300 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none, some (264 : Rat)] [] (50724 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none, some (264 : Rat)] [(165471 / 625 : Rat)] (112598 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), some (286 : Rat), none] [(2869551 / 10000 : Rat)] (101446 : Int), datedRead (286 : Rat) #v[some (286 : Rat), some (286 : Rat), none] [] (56300 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none, some (308 : Rat)] [] (50724 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none, some (308 : Rat)] [(192971 / 625 : Rat)] (112598 : Int)]]
private def trace_F2_8515_K0_st : List (ReadObservation 2) := [datedRead (1124551 / 10000 : Rat) #v[some (1124551 / 10000 : Rat), none] [] (49694 : Int), datedRead (167817 / 1250 : Rat) #v[none, some (167817 / 1250 : Rat)] [] (50304 : Int), datedRead (1564551 / 10000 : Rat) #v[some (1564551 / 10000 : Rat), none] [] (80912 : Int), datedRead (222817 / 1250 : Rat) #v[none, some (222817 / 1250 : Rat)] [] (81522 : Int), datedRead (2004551 / 10000 : Rat) #v[some (2004551 / 10000 : Rat), none] [(2013133 / 10000 : Rat)] (112128 : Int), datedRead (277817 / 1250 : Rat) #v[none, some (277817 / 1250 : Rat)] [(2231071 / 10000 : Rat)] (112737 : Int), datedRead (2444551 / 10000 : Rat) #v[some (2444551 / 10000 : Rat), none] [(2453133 / 10000 : Rat)] (112128 : Int), datedRead (332817 / 1250 : Rat) #v[none, some (332817 / 1250 : Rat)] [(2671071 / 10000 : Rat)] (112737 : Int), datedRead (2884551 / 10000 : Rat) #v[some (2884551 / 10000 : Rat), none] [(2893133 / 10000 : Rat)] (112128 : Int), datedRead (387817 / 1250 : Rat) #v[none, some (387817 / 1250 : Rat)] [(3111071 / 10000 : Rat)] (112737 : Int)]
private def trace_F2_8515_K0_fx : List (List (ReadObservation 3)) := [[datedRead (330 : Rat) #v[none, none, none] [] (0 : Int), datedRead (330 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (0 : Int), datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (56299 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (50723 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (0 : Int)], [datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (50723 : Int), datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (56299 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (50724 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (56300 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [] (50724 : Int), datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [(275471 / 625 : Rat)] (112598 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [(3969551 / 10000 : Rat)] (101446 : Int), datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [] (56300 : Int)], [datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(4849551 / 10000 : Rat)] (101446 : Int), datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(302971 / 625 : Rat)] (112598 : Int)]]
private def trace_F2_8515_K0_sx : List (ReadObservation 2) := [datedRead (663 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (927 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (552817 / 1250 : Rat) #v[none, some (552817 / 1250 : Rat)] [(4431071 / 10000 : Rat)] (112737 : Int), datedRead (3984551 / 10000 : Rat) #v[some (3984551 / 10000 : Rat), none] [(3993133 / 10000 : Rat)] (112128 : Int), datedRead (607817 / 1250 : Rat) #v[some (4864551 / 10000 : Rat), some (607817 / 1250 : Rat)] [(2433447 / 5000 : Rat)] (224859 : Int)]
private def trace_F2_8515_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)]]

def trace_F2_8515_K0 : TraceTables cascade_F2_8515_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F2_8515_K0_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F2_8515_K0_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F2_8515_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F2_8515_K0_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8515_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8515_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F2_8515_K0 : checks cascade_F2_8515_K0 trace_F2_8515_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F2_8515_K0 : checkCascadeValid cascade_F2_8515_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F2_8515_K0 : checkTrainingSeparation cascade_F2_8515_K0 left right trace_F2_8515_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F2_8515_K0 : checkCascadeCalibrationOneSided cascade_F2_8515_K0 left right trace_F2_8515_K0.observations trace_F2_8515_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F2_8515_K0 : ∀ x i, (trace_F2_8515_K0.observations.secondTest x i).fired = output cascade_F2_8515_K0 i x := by
  have checked := checks_F2_8515_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_F2_8515_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F2_8515_K0.observations trace_F2_8515_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F2_8515_K3 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[36160, 36159, 0], #v[41736, 0, 41735]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[2391, 2386] : Vector Nat 2).get a,
    testingError := fun a => (#v[2391, 2386] : Vector Nat 2).get a,
    dose := 7281, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[49697, 50306] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 5120, testingError := fun _ => 5120,
    dose := 31214, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F2_8515_K3_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), some (0 : Rat), none] [] (72318 : Int), datedRead (0 : Rat) #v[some (0 : Rat), none, some (0 : Rat)] [] (83470 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), some (22 : Rat), none] [] (86883 : Int), datedRead (22 : Rat) #v[some (22 : Rat), none, some (22 : Rat)] [] (98035 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), some (44 : Rat), none] [(449551 / 10000 : Rat)] (101446 : Int), datedRead (44 : Rat) #v[some (44 : Rat), none, some (44 : Rat)] [(27971 / 625 : Rat)] (112598 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), some (66 : Rat), none] [(669551 / 10000 : Rat)] (101446 : Int), datedRead (66 : Rat) #v[some (66 : Rat), none, some (66 : Rat)] [(41721 / 625 : Rat)] (112598 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), some (88 : Rat), none] [(889551 / 10000 : Rat)] (101446 : Int), datedRead (88 : Rat) #v[some (88 : Rat), none, some (88 : Rat)] [(55471 / 625 : Rat)] (112598 : Int)]]
private def trace_F2_8515_K3_te : List (List (ReadObservation 3)) := [[datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [(1109551 / 10000 : Rat)] (101446 : Int), datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [] (56300 : Int)], [datedRead (132 : Rat) #v[some (132 : Rat), none, some (132 : Rat)] [] (50724 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none, some (132 : Rat)] [(82971 / 625 : Rat)] (112598 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat), none] [(1549551 / 10000 : Rat)] (101446 : Int), datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat), none] [] (56300 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none, some (176 : Rat)] [] (50724 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none, some (176 : Rat)] [(110471 / 625 : Rat)] (112598 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat), none] [(1989551 / 10000 : Rat)] (101446 : Int), datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat), none] [] (56300 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none, some (220 : Rat)] [] (50724 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none, some (220 : Rat)] [(137971 / 625 : Rat)] (112598 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), some (242 : Rat), none] [(2429551 / 10000 : Rat)] (101446 : Int), datedRead (242 : Rat) #v[some (242 : Rat), some (242 : Rat), none] [] (56300 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none, some (264 : Rat)] [] (50724 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none, some (264 : Rat)] [(165471 / 625 : Rat)] (112598 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), some (286 : Rat), none] [(2869551 / 10000 : Rat)] (101446 : Int), datedRead (286 : Rat) #v[some (286 : Rat), some (286 : Rat), none] [] (56300 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none, some (308 : Rat)] [] (50724 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none, some (308 : Rat)] [(192971 / 625 : Rat)] (112598 : Int)]]
private def trace_F2_8515_K3_st : List (ReadObservation 2) := [datedRead (1124551 / 10000 : Rat) #v[some (1124551 / 10000 : Rat), none] [] (49694 : Int), datedRead (167817 / 1250 : Rat) #v[none, some (167817 / 1250 : Rat)] [] (50304 : Int), datedRead (1564551 / 10000 : Rat) #v[some (1564551 / 10000 : Rat), none] [] (80912 : Int), datedRead (222817 / 1250 : Rat) #v[none, some (222817 / 1250 : Rat)] [] (81522 : Int), datedRead (2004551 / 10000 : Rat) #v[some (2004551 / 10000 : Rat), none] [(2013133 / 10000 : Rat)] (112128 : Int), datedRead (277817 / 1250 : Rat) #v[none, some (277817 / 1250 : Rat)] [(2231071 / 10000 : Rat)] (112737 : Int), datedRead (2444551 / 10000 : Rat) #v[some (2444551 / 10000 : Rat), none] [(2453133 / 10000 : Rat)] (112128 : Int), datedRead (332817 / 1250 : Rat) #v[none, some (332817 / 1250 : Rat)] [(2671071 / 10000 : Rat)] (112737 : Int), datedRead (2884551 / 10000 : Rat) #v[some (2884551 / 10000 : Rat), none] [(2893133 / 10000 : Rat)] (112128 : Int), datedRead (387817 / 1250 : Rat) #v[none, some (387817 / 1250 : Rat)] [(3111071 / 10000 : Rat)] (112737 : Int)]
private def trace_F2_8515_K3_fx : List (List (ReadObservation 3)) := [[datedRead (330 : Rat) #v[none, none, none] [] (0 : Int), datedRead (330 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (0 : Int), datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (56299 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (50723 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (0 : Int)], [datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (50723 : Int), datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (56299 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (50724 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (56300 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [] (50724 : Int), datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [(275471 / 625 : Rat)] (112598 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [(3969551 / 10000 : Rat)] (101446 : Int), datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [] (56300 : Int)], [datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(4849551 / 10000 : Rat)] (101446 : Int), datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(302971 / 625 : Rat)] (112598 : Int)]]
private def trace_F2_8515_K3_sx : List (ReadObservation 2) := [datedRead (663 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (927 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (552817 / 1250 : Rat) #v[none, some (552817 / 1250 : Rat)] [(4431071 / 10000 : Rat)] (112737 : Int), datedRead (3984551 / 10000 : Rat) #v[some (3984551 / 10000 : Rat), none] [(3993133 / 10000 : Rat)] (112128 : Int), datedRead (607817 / 1250 : Rat) #v[some (4864551 / 10000 : Rat), some (607817 / 1250 : Rat)] [(2433447 / 5000 : Rat)] (224859 : Int)]
private def trace_F2_8515_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)], #v[(0 : Int), (112737 : Int), (112128 : Int), (224859 : Int)]]

def trace_F2_8515_K3 : TraceTables cascade_F2_8515_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F2_8515_K3_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F2_8515_K3_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F2_8515_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F2_8515_K3_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8515_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8515_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F2_8515_K3 : checks cascade_F2_8515_K3 trace_F2_8515_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F2_8515_K3 : checkCascadeValid cascade_F2_8515_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F2_8515_K3 : checkTrainingSeparation cascade_F2_8515_K3 left right trace_F2_8515_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F2_8515_K3 : checkCascadeCalibrationOneSided cascade_F2_8515_K3 left right trace_F2_8515_K3.observations trace_F2_8515_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
