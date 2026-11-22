import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F3, instance 8305.
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

def cascade_F3_8305_K0 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[86713, 0, 0], #v[0, 32214, 32213]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[108, 209] : Vector Nat 2).get a,
    testingError := fun a => (#v[108, 209] : Vector Nat 2).get a,
    dose := 7844, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[52177, 47832] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 328, testingError := fun _ => 328,
    dose := 24704, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F3_8305_K0_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none, none] [] (86714 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat), some (0 : Rat)] [] (64424 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none, none] [] (94559 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat), some (22 : Rat)] [] (80114 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none, none] [(448821 / 10000 : Rat)] (102403 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat), some (44 : Rat)] [] (95804 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none, none] [(668821 / 10000 : Rat)] (102403 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat), some (66 : Rat)] [(333901 / 5000 : Rat)] (111492 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none, none] [(888821 / 10000 : Rat)] (102403 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat), some (88 : Rat)] [(443901 / 5000 : Rat)] (111492 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), none, none] [(1108821 / 10000 : Rat)] (102403 : Int), datedRead (110 : Rat) #v[none, some (110 : Rat), some (110 : Rat)] [(553901 / 5000 : Rat)] (111492 : Int)]]
private def trace_F3_8305_K0_te : List (List (ReadObservation 3)) := [[datedRead (132 : Rat) #v[some (132 : Rat), none, none] [(1328821 / 10000 : Rat)] (102403 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none, none] [] (0 : Int)], [datedRead (154 : Rat) #v[none, some (154 : Rat), some (154 : Rat)] [] (0 : Int), datedRead (154 : Rat) #v[none, some (154 : Rat), some (154 : Rat)] [(773901 / 5000 : Rat)] (111492 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none, none] [(1768821 / 10000 : Rat)] (102403 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none, none] [] (0 : Int)], [datedRead (198 : Rat) #v[none, some (198 : Rat), some (198 : Rat)] [] (0 : Int), datedRead (198 : Rat) #v[none, some (198 : Rat), some (198 : Rat)] [(993901 / 5000 : Rat)] (111492 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none, none] [(2208821 / 10000 : Rat)] (102403 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none, none] [] (0 : Int)], [datedRead (242 : Rat) #v[none, some (242 : Rat), some (242 : Rat)] [] (0 : Int), datedRead (242 : Rat) #v[none, some (242 : Rat), some (242 : Rat)] [(1213901 / 5000 : Rat)] (111492 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none, none] [(2648821 / 10000 : Rat)] (102403 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none, none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat), some (286 : Rat)] [] (0 : Int), datedRead (286 : Rat) #v[none, some (286 : Rat), some (286 : Rat)] [(1433901 / 5000 : Rat)] (111492 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none, none] [(3088821 / 10000 : Rat)] (102403 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none, none] [] (0 : Int)], [datedRead (330 : Rat) #v[none, some (330 : Rat), some (330 : Rat)] [] (0 : Int), datedRead (330 : Rat) #v[none, some (330 : Rat), some (330 : Rat)] [(1653901 / 5000 : Rat)] (111492 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none, none] [(3528821 / 10000 : Rat)] (102403 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (0 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat), some (374 : Rat)] [] (0 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat), some (374 : Rat)] [(1873901 / 5000 : Rat)] (111492 : Int)]]
private def trace_F3_8305_K0_st : List (ReadObservation 2) := [datedRead (1343821 / 10000 : Rat) #v[some (1343821 / 10000 : Rat), none] [] (52173 : Int), datedRead (781401 / 5000 : Rat) #v[none, some (781401 / 5000 : Rat)] [] (47829 : Int), datedRead (1783821 / 10000 : Rat) #v[some (1783821 / 10000 : Rat), none] [] (76882 : Int), datedRead (1001401 / 5000 : Rat) #v[none, some (1001401 / 5000 : Rat)] [] (72537 : Int), datedRead (2223821 / 10000 : Rat) #v[some (2223821 / 10000 : Rat), none] [(2233507 / 10000 : Rat)] (101588 : Int), datedRead (1221401 / 5000 : Rat) #v[none, some (1221401 / 5000 : Rat)] [] (97243 : Int), datedRead (2663821 / 10000 : Rat) #v[some (2663821 / 10000 : Rat), none] [(2673507 / 10000 : Rat)] (101588 : Int), datedRead (1441401 / 5000 : Rat) #v[none, some (1441401 / 5000 : Rat)] [(722577 / 2500 : Rat)] (121947 : Int), datedRead (3103821 / 10000 : Rat) #v[some (3103821 / 10000 : Rat), none] [(3113507 / 10000 : Rat)] (101588 : Int), datedRead (1661401 / 5000 : Rat) #v[none, some (1661401 / 5000 : Rat)] [(832577 / 2500 : Rat)] (121947 : Int), datedRead (3543821 / 10000 : Rat) #v[some (3543821 / 10000 : Rat), none] [(3553507 / 10000 : Rat)] (101588 : Int), datedRead (1881401 / 5000 : Rat) #v[none, some (1881401 / 5000 : Rat)] [(942577 / 2500 : Rat)] (121947 : Int)]
private def trace_F3_8305_K0_fx : List (List (ReadObservation 3)) := [[datedRead (396 : Rat) #v[none, none, none] [] (0 : Int), datedRead (396 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (484 : Rat) #v[none, none, some (484 : Rat)] [] (0 : Int), datedRead (484 : Rat) #v[none, none, some (484 : Rat)] [] (55746 : Int)], [datedRead (440 : Rat) #v[none, some (440 : Rat), none] [] (0 : Int), datedRead (440 : Rat) #v[none, some (440 : Rat), none] [] (55747 : Int)], [datedRead (528 : Rat) #v[none, some (528 : Rat), some (528 : Rat)] [] (0 : Int), datedRead (528 : Rat) #v[none, some (528 : Rat), some (528 : Rat)] [(2643901 / 5000 : Rat)] (111492 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), none, none] [(4188821 / 10000 : Rat)] (102403 : Int), datedRead (418 : Rat) #v[some (418 : Rat), none, none] [] (0 : Int)], [datedRead (506 : Rat) #v[some (506 : Rat), none, some (506 : Rat)] [(5068821 / 10000 : Rat)] (102403 : Int), datedRead (506 : Rat) #v[some (506 : Rat), none, some (506 : Rat)] [] (55746 : Int)], [datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat), none] [(4628821 / 10000 : Rat)] (102403 : Int), datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat), none] [] (55747 : Int)], [datedRead (550 : Rat) #v[some (550 : Rat), some (550 : Rat), some (550 : Rat)] [(5508821 / 10000 : Rat)] (102403 : Int), datedRead (550 : Rat) #v[some (550 : Rat), some (550 : Rat), some (550 : Rat)] [(2753901 / 5000 : Rat)] (111492 : Int)]]
private def trace_F3_8305_K0_sx : List (ReadObservation 2) := [datedRead (795 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (971 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (883 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (2651401 / 5000 : Rat) #v[none, some (2651401 / 5000 : Rat)] [(1327577 / 2500 : Rat)] (121947 : Int), datedRead (4203821 / 10000 : Rat) #v[some (4203821 / 10000 : Rat), none] [(4213507 / 10000 : Rat)] (101588 : Int), datedRead (5083821 / 10000 : Rat) #v[some (5083821 / 10000 : Rat), none] [(5093507 / 10000 : Rat)] (101588 : Int), datedRead (4643821 / 10000 : Rat) #v[some (4643821 / 10000 : Rat), none] [(4653507 / 10000 : Rat)] (101588 : Int), datedRead (2761401 / 5000 : Rat) #v[some (5523821 / 10000 : Rat), some (2761401 / 5000 : Rat)] [(5525553 / 10000 : Rat)] (198827 : Int)]
private def trace_F3_8305_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)]]

def trace_F3_8305_K0 : TraceTables cascade_F3_8305_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F3_8305_K0_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F3_8305_K0_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F3_8305_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F3_8305_K0_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8305_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8305_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F3_8305_K0 : checks cascade_F3_8305_K0 trace_F3_8305_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F3_8305_K0 : checkCascadeValid cascade_F3_8305_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F3_8305_K0 : checkTrainingSeparation cascade_F3_8305_K0 left right trace_F3_8305_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F3_8305_K0 : checkCascadeCalibrationOneSided cascade_F3_8305_K0 left right trace_F3_8305_K0.observations trace_F3_8305_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F3_8305_K0 : ∀ x i, (trace_F3_8305_K0.observations.secondTest x i).fired = output cascade_F3_8305_K0 i x := by
  have checked := checks_F3_8305_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_F3_8305_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F3_8305_K0.observations trace_F3_8305_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F3_8305_K3 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[86713, 0, 0], #v[0, 32214, 32213]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[1294, 2584] : Vector Nat 2).get a,
    testingError := fun a => (#v[1294, 2584] : Vector Nat 2).get a,
    dose := 7844, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[52177, 47832] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 4057, testingError := fun _ => 4057,
    dose := 24704, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F3_8305_K3_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none, none] [] (86714 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat), some (0 : Rat)] [] (64424 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none, none] [] (94559 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat), some (22 : Rat)] [] (80114 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none, none] [(448821 / 10000 : Rat)] (102403 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat), some (44 : Rat)] [] (95804 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none, none] [(668821 / 10000 : Rat)] (102403 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat), some (66 : Rat)] [(333901 / 5000 : Rat)] (111492 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none, none] [(888821 / 10000 : Rat)] (102403 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat), some (88 : Rat)] [(443901 / 5000 : Rat)] (111492 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), none, none] [(1108821 / 10000 : Rat)] (102403 : Int), datedRead (110 : Rat) #v[none, some (110 : Rat), some (110 : Rat)] [(553901 / 5000 : Rat)] (111492 : Int)]]
private def trace_F3_8305_K3_te : List (List (ReadObservation 3)) := [[datedRead (132 : Rat) #v[some (132 : Rat), none, none] [(1328821 / 10000 : Rat)] (102403 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none, none] [] (0 : Int)], [datedRead (154 : Rat) #v[none, some (154 : Rat), some (154 : Rat)] [] (0 : Int), datedRead (154 : Rat) #v[none, some (154 : Rat), some (154 : Rat)] [(773901 / 5000 : Rat)] (111492 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none, none] [(1768821 / 10000 : Rat)] (102403 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none, none] [] (0 : Int)], [datedRead (198 : Rat) #v[none, some (198 : Rat), some (198 : Rat)] [] (0 : Int), datedRead (198 : Rat) #v[none, some (198 : Rat), some (198 : Rat)] [(993901 / 5000 : Rat)] (111492 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none, none] [(2208821 / 10000 : Rat)] (102403 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none, none] [] (0 : Int)], [datedRead (242 : Rat) #v[none, some (242 : Rat), some (242 : Rat)] [] (0 : Int), datedRead (242 : Rat) #v[none, some (242 : Rat), some (242 : Rat)] [(1213901 / 5000 : Rat)] (111492 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none, none] [(2648821 / 10000 : Rat)] (102403 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none, none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat), some (286 : Rat)] [] (0 : Int), datedRead (286 : Rat) #v[none, some (286 : Rat), some (286 : Rat)] [(1433901 / 5000 : Rat)] (111492 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none, none] [(3088821 / 10000 : Rat)] (102403 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none, none] [] (0 : Int)], [datedRead (330 : Rat) #v[none, some (330 : Rat), some (330 : Rat)] [] (0 : Int), datedRead (330 : Rat) #v[none, some (330 : Rat), some (330 : Rat)] [(1653901 / 5000 : Rat)] (111492 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none, none] [(3528821 / 10000 : Rat)] (102403 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (0 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat), some (374 : Rat)] [] (0 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat), some (374 : Rat)] [(1873901 / 5000 : Rat)] (111492 : Int)]]
private def trace_F3_8305_K3_st : List (ReadObservation 2) := [datedRead (1343821 / 10000 : Rat) #v[some (1343821 / 10000 : Rat), none] [] (52173 : Int), datedRead (781401 / 5000 : Rat) #v[none, some (781401 / 5000 : Rat)] [] (47829 : Int), datedRead (1783821 / 10000 : Rat) #v[some (1783821 / 10000 : Rat), none] [] (76882 : Int), datedRead (1001401 / 5000 : Rat) #v[none, some (1001401 / 5000 : Rat)] [] (72537 : Int), datedRead (2223821 / 10000 : Rat) #v[some (2223821 / 10000 : Rat), none] [(2233507 / 10000 : Rat)] (101588 : Int), datedRead (1221401 / 5000 : Rat) #v[none, some (1221401 / 5000 : Rat)] [] (97243 : Int), datedRead (2663821 / 10000 : Rat) #v[some (2663821 / 10000 : Rat), none] [(2673507 / 10000 : Rat)] (101588 : Int), datedRead (1441401 / 5000 : Rat) #v[none, some (1441401 / 5000 : Rat)] [(722577 / 2500 : Rat)] (121947 : Int), datedRead (3103821 / 10000 : Rat) #v[some (3103821 / 10000 : Rat), none] [(3113507 / 10000 : Rat)] (101588 : Int), datedRead (1661401 / 5000 : Rat) #v[none, some (1661401 / 5000 : Rat)] [(832577 / 2500 : Rat)] (121947 : Int), datedRead (3543821 / 10000 : Rat) #v[some (3543821 / 10000 : Rat), none] [(3553507 / 10000 : Rat)] (101588 : Int), datedRead (1881401 / 5000 : Rat) #v[none, some (1881401 / 5000 : Rat)] [(942577 / 2500 : Rat)] (121947 : Int)]
private def trace_F3_8305_K3_fx : List (List (ReadObservation 3)) := [[datedRead (396 : Rat) #v[none, none, none] [] (0 : Int), datedRead (396 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (484 : Rat) #v[none, none, some (484 : Rat)] [] (0 : Int), datedRead (484 : Rat) #v[none, none, some (484 : Rat)] [] (55746 : Int)], [datedRead (440 : Rat) #v[none, some (440 : Rat), none] [] (0 : Int), datedRead (440 : Rat) #v[none, some (440 : Rat), none] [] (55747 : Int)], [datedRead (528 : Rat) #v[none, some (528 : Rat), some (528 : Rat)] [] (0 : Int), datedRead (528 : Rat) #v[none, some (528 : Rat), some (528 : Rat)] [(2643901 / 5000 : Rat)] (111492 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), none, none] [(4188821 / 10000 : Rat)] (102403 : Int), datedRead (418 : Rat) #v[some (418 : Rat), none, none] [] (0 : Int)], [datedRead (506 : Rat) #v[some (506 : Rat), none, some (506 : Rat)] [(5068821 / 10000 : Rat)] (102403 : Int), datedRead (506 : Rat) #v[some (506 : Rat), none, some (506 : Rat)] [] (55746 : Int)], [datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat), none] [(4628821 / 10000 : Rat)] (102403 : Int), datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat), none] [] (55747 : Int)], [datedRead (550 : Rat) #v[some (550 : Rat), some (550 : Rat), some (550 : Rat)] [(5508821 / 10000 : Rat)] (102403 : Int), datedRead (550 : Rat) #v[some (550 : Rat), some (550 : Rat), some (550 : Rat)] [(2753901 / 5000 : Rat)] (111492 : Int)]]
private def trace_F3_8305_K3_sx : List (ReadObservation 2) := [datedRead (795 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (971 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (883 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (2651401 / 5000 : Rat) #v[none, some (2651401 / 5000 : Rat)] [(1327577 / 2500 : Rat)] (121947 : Int), datedRead (4203821 / 10000 : Rat) #v[some (4203821 / 10000 : Rat), none] [(4213507 / 10000 : Rat)] (101588 : Int), datedRead (5083821 / 10000 : Rat) #v[some (5083821 / 10000 : Rat), none] [(5093507 / 10000 : Rat)] (101588 : Int), datedRead (4643821 / 10000 : Rat) #v[some (4643821 / 10000 : Rat), none] [(4653507 / 10000 : Rat)] (101588 : Int), datedRead (2761401 / 5000 : Rat) #v[some (5523821 / 10000 : Rat), some (2761401 / 5000 : Rat)] [(5525553 / 10000 : Rat)] (198827 : Int)]
private def trace_F3_8305_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)], #v[(0 : Int), (121947 : Int), (101588 : Int), (198827 : Int)]]

def trace_F3_8305_K3 : TraceTables cascade_F3_8305_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F3_8305_K3_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F3_8305_K3_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F3_8305_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F3_8305_K3_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8305_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8305_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F3_8305_K3 : checks cascade_F3_8305_K3 trace_F3_8305_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F3_8305_K3 : checkCascadeValid cascade_F3_8305_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F3_8305_K3 : checkTrainingSeparation cascade_F3_8305_K3 left right trace_F3_8305_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F3_8305_K3 : checkCascadeCalibrationOneSided cascade_F3_8305_K3 left right trace_F3_8305_K3.observations trace_F3_8305_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
