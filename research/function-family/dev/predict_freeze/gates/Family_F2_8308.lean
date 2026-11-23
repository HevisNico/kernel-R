import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F2, instance 8308.
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

def cascade_F2_8308_K0 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[37620, 37619, 0], #v[34635, 0, 34634]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[207, 207] : Vector Nat 2).get a,
    testingError := fun a => (#v[207, 207] : Vector Nat 2).get a,
    dose := 7796, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[45070, 54937] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 489, testingError := fun _ => 489,
    dose := 37148, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F2_8308_K0_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), some (0 : Rat), none] [] (75238 : Int), datedRead (0 : Rat) #v[some (0 : Rat), none, some (0 : Rat)] [] (69268 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), some (22 : Rat), none] [] (90832 : Int), datedRead (22 : Rat) #v[some (22 : Rat), none, some (22 : Rat)] [] (84862 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), some (44 : Rat), none] [(448523 / 10000 : Rat)] (106426 : Int), datedRead (44 : Rat) #v[some (44 : Rat), none, some (44 : Rat)] [(449857 / 10000 : Rat)] (100456 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), some (66 : Rat), none] [(668523 / 10000 : Rat)] (106426 : Int), datedRead (66 : Rat) #v[some (66 : Rat), none, some (66 : Rat)] [(669857 / 10000 : Rat)] (100456 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), some (88 : Rat), none] [(888523 / 10000 : Rat)] (106426 : Int), datedRead (88 : Rat) #v[some (88 : Rat), none, some (88 : Rat)] [(889857 / 10000 : Rat)] (100456 : Int)]]
private def trace_F2_8308_K0_te : List (List (ReadObservation 3)) := [[datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [(1108523 / 10000 : Rat)] (106426 : Int), datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [] (50229 : Int)], [datedRead (132 : Rat) #v[some (132 : Rat), none, some (132 : Rat)] [] (53214 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none, some (132 : Rat)] [(1329857 / 10000 : Rat)] (100456 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat), none] [(1548523 / 10000 : Rat)] (106426 : Int), datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat), none] [] (50229 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none, some (176 : Rat)] [] (53214 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none, some (176 : Rat)] [(1769857 / 10000 : Rat)] (100456 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat), none] [(1988523 / 10000 : Rat)] (106426 : Int), datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat), none] [] (50229 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none, some (220 : Rat)] [] (53214 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none, some (220 : Rat)] [(2209857 / 10000 : Rat)] (100456 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), some (242 : Rat), none] [(2428523 / 10000 : Rat)] (106426 : Int), datedRead (242 : Rat) #v[some (242 : Rat), some (242 : Rat), none] [] (50229 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none, some (264 : Rat)] [] (53214 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none, some (264 : Rat)] [(2649857 / 10000 : Rat)] (100456 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), some (286 : Rat), none] [(2868523 / 10000 : Rat)] (106426 : Int), datedRead (286 : Rat) #v[some (286 : Rat), some (286 : Rat), none] [] (50229 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none, some (308 : Rat)] [] (53214 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none, some (308 : Rat)] [(3089857 / 10000 : Rat)] (100456 : Int)]]
private def trace_F2_8308_K0_st : List (ReadObservation 2) := [datedRead (1123523 / 10000 : Rat) #v[some (1123523 / 10000 : Rat), none] [] (45066 : Int), datedRead (1344857 / 10000 : Rat) #v[none, some (1344857 / 10000 : Rat)] [] (54934 : Int), datedRead (1563523 / 10000 : Rat) #v[some (1563523 / 10000 : Rat), none] [] (82219 : Int), datedRead (1784857 / 10000 : Rat) #v[none, some (1784857 / 10000 : Rat)] [] (92087 : Int), datedRead (2003523 / 10000 : Rat) #v[some (2003523 / 10000 : Rat), none] [(251471 / 1250 : Rat)] (119369 : Int), datedRead (2224857 / 10000 : Rat) #v[none, some (2224857 / 10000 : Rat)] [(2232553 / 10000 : Rat)] (129237 : Int), datedRead (2443523 / 10000 : Rat) #v[some (2443523 / 10000 : Rat), none] [(306471 / 1250 : Rat)] (119369 : Int), datedRead (2664857 / 10000 : Rat) #v[none, some (2664857 / 10000 : Rat)] [(2672553 / 10000 : Rat)] (129237 : Int), datedRead (2883523 / 10000 : Rat) #v[some (2883523 / 10000 : Rat), none] [(361471 / 1250 : Rat)] (119369 : Int), datedRead (3104857 / 10000 : Rat) #v[none, some (3104857 / 10000 : Rat)] [(3112553 / 10000 : Rat)] (129237 : Int)]
private def trace_F2_8308_K0_fx : List (List (ReadObservation 3)) := [[datedRead (330 : Rat) #v[none, none, none] [] (0 : Int), datedRead (330 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (0 : Int), datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (50228 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (53213 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (0 : Int)], [datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (53213 : Int), datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (50228 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (53214 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (50229 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [] (53214 : Int), datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [(4409857 / 10000 : Rat)] (100456 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [(3968523 / 10000 : Rat)] (106426 : Int), datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [] (50229 : Int)], [datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(4848523 / 10000 : Rat)] (106426 : Int), datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(4849857 / 10000 : Rat)] (100456 : Int)]]
private def trace_F2_8308_K0_sx : List (ReadObservation 2) := [datedRead (663 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (927 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (4424857 / 10000 : Rat) #v[none, some (4424857 / 10000 : Rat)] [(4432553 / 10000 : Rat)] (129237 : Int), datedRead (3983523 / 10000 : Rat) #v[some (3983523 / 10000 : Rat), none] [(498971 / 1250 : Rat)] (119369 : Int), datedRead (4863523 / 10000 : Rat) #v[some (4863523 / 10000 : Rat), some (4864857 / 10000 : Rat)] [(2433041 / 5000 : Rat)] (248599 : Int)]
private def trace_F2_8308_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)]]

def trace_F2_8308_K0 : TraceTables cascade_F2_8308_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F2_8308_K0_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F2_8308_K0_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F2_8308_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F2_8308_K0_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8308_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8308_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F2_8308_K0 : checks cascade_F2_8308_K0 trace_F2_8308_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F2_8308_K0 : checkCascadeValid cascade_F2_8308_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F2_8308_K0 : checkTrainingSeparation cascade_F2_8308_K0 left right trace_F2_8308_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F2_8308_K0 : checkCascadeCalibrationOneSided cascade_F2_8308_K0 left right trace_F2_8308_K0.observations trace_F2_8308_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F2_8308_K0 : ∀ x i, (trace_F2_8308_K0.observations.secondTest x i).fired = output cascade_F2_8308_K0 i x := by
  have checked := checks_F2_8308_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_F2_8308_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F2_8308_K0.observations trace_F2_8308_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F2_8308_K3 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[37620, 37619, 0], #v[34635, 0, 34634]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[2551, 2560] : Vector Nat 2).get a,
    testingError := fun a => (#v[2551, 2560] : Vector Nat 2).get a,
    dose := 7796, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[45070, 54937] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 6090, testingError := fun _ => 6090,
    dose := 37148, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F2_8308_K3_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), some (0 : Rat), none] [] (75238 : Int), datedRead (0 : Rat) #v[some (0 : Rat), none, some (0 : Rat)] [] (69268 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), some (22 : Rat), none] [] (90832 : Int), datedRead (22 : Rat) #v[some (22 : Rat), none, some (22 : Rat)] [] (84862 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), some (44 : Rat), none] [(448523 / 10000 : Rat)] (106426 : Int), datedRead (44 : Rat) #v[some (44 : Rat), none, some (44 : Rat)] [(449857 / 10000 : Rat)] (100456 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), some (66 : Rat), none] [(668523 / 10000 : Rat)] (106426 : Int), datedRead (66 : Rat) #v[some (66 : Rat), none, some (66 : Rat)] [(669857 / 10000 : Rat)] (100456 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), some (88 : Rat), none] [(888523 / 10000 : Rat)] (106426 : Int), datedRead (88 : Rat) #v[some (88 : Rat), none, some (88 : Rat)] [(889857 / 10000 : Rat)] (100456 : Int)]]
private def trace_F2_8308_K3_te : List (List (ReadObservation 3)) := [[datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [(1108523 / 10000 : Rat)] (106426 : Int), datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [] (50229 : Int)], [datedRead (132 : Rat) #v[some (132 : Rat), none, some (132 : Rat)] [] (53214 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none, some (132 : Rat)] [(1329857 / 10000 : Rat)] (100456 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat), none] [(1548523 / 10000 : Rat)] (106426 : Int), datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat), none] [] (50229 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none, some (176 : Rat)] [] (53214 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none, some (176 : Rat)] [(1769857 / 10000 : Rat)] (100456 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat), none] [(1988523 / 10000 : Rat)] (106426 : Int), datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat), none] [] (50229 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none, some (220 : Rat)] [] (53214 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none, some (220 : Rat)] [(2209857 / 10000 : Rat)] (100456 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), some (242 : Rat), none] [(2428523 / 10000 : Rat)] (106426 : Int), datedRead (242 : Rat) #v[some (242 : Rat), some (242 : Rat), none] [] (50229 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none, some (264 : Rat)] [] (53214 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none, some (264 : Rat)] [(2649857 / 10000 : Rat)] (100456 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), some (286 : Rat), none] [(2868523 / 10000 : Rat)] (106426 : Int), datedRead (286 : Rat) #v[some (286 : Rat), some (286 : Rat), none] [] (50229 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none, some (308 : Rat)] [] (53214 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none, some (308 : Rat)] [(3089857 / 10000 : Rat)] (100456 : Int)]]
private def trace_F2_8308_K3_st : List (ReadObservation 2) := [datedRead (1123523 / 10000 : Rat) #v[some (1123523 / 10000 : Rat), none] [] (45066 : Int), datedRead (1344857 / 10000 : Rat) #v[none, some (1344857 / 10000 : Rat)] [] (54934 : Int), datedRead (1563523 / 10000 : Rat) #v[some (1563523 / 10000 : Rat), none] [] (82219 : Int), datedRead (1784857 / 10000 : Rat) #v[none, some (1784857 / 10000 : Rat)] [] (92087 : Int), datedRead (2003523 / 10000 : Rat) #v[some (2003523 / 10000 : Rat), none] [(251471 / 1250 : Rat)] (119369 : Int), datedRead (2224857 / 10000 : Rat) #v[none, some (2224857 / 10000 : Rat)] [(2232553 / 10000 : Rat)] (129237 : Int), datedRead (2443523 / 10000 : Rat) #v[some (2443523 / 10000 : Rat), none] [(306471 / 1250 : Rat)] (119369 : Int), datedRead (2664857 / 10000 : Rat) #v[none, some (2664857 / 10000 : Rat)] [(2672553 / 10000 : Rat)] (129237 : Int), datedRead (2883523 / 10000 : Rat) #v[some (2883523 / 10000 : Rat), none] [(361471 / 1250 : Rat)] (119369 : Int), datedRead (3104857 / 10000 : Rat) #v[none, some (3104857 / 10000 : Rat)] [(3112553 / 10000 : Rat)] (129237 : Int)]
private def trace_F2_8308_K3_fx : List (List (ReadObservation 3)) := [[datedRead (330 : Rat) #v[none, none, none] [] (0 : Int), datedRead (330 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (0 : Int), datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (50228 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (53213 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (0 : Int)], [datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (53213 : Int), datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (50228 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (53214 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (50229 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [] (53214 : Int), datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [(4409857 / 10000 : Rat)] (100456 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [(3968523 / 10000 : Rat)] (106426 : Int), datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [] (50229 : Int)], [datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(4848523 / 10000 : Rat)] (106426 : Int), datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(4849857 / 10000 : Rat)] (100456 : Int)]]
private def trace_F2_8308_K3_sx : List (ReadObservation 2) := [datedRead (663 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (927 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (4424857 / 10000 : Rat) #v[none, some (4424857 / 10000 : Rat)] [(4432553 / 10000 : Rat)] (129237 : Int), datedRead (3983523 / 10000 : Rat) #v[some (3983523 / 10000 : Rat), none] [(498971 / 1250 : Rat)] (119369 : Int), datedRead (4863523 / 10000 : Rat) #v[some (4863523 / 10000 : Rat), some (4864857 / 10000 : Rat)] [(2433041 / 5000 : Rat)] (248599 : Int)]
private def trace_F2_8308_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)]]

def trace_F2_8308_K3 : TraceTables cascade_F2_8308_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F2_8308_K3_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F2_8308_K3_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F2_8308_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F2_8308_K3_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8308_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8308_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F2_8308_K3 : checks cascade_F2_8308_K3 trace_F2_8308_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F2_8308_K3 : checkCascadeValid cascade_F2_8308_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F2_8308_K3 : checkTrainingSeparation cascade_F2_8308_K3 left right trace_F2_8308_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F2_8308_K3 : checkCascadeCalibrationOneSided cascade_F2_8308_K3 left right trace_F2_8308_K3.observations trace_F2_8308_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
