import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F2, instance 8303.
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

def cascade_F2_8303_K0 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[37886, 37885, 0], #v[36794, 0, 36793]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[207, 207] : Vector Nat 2).get a,
    testingError := fun a => (#v[207, 207] : Vector Nat 2).get a,
    dose := 7763, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[52354, 47651] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 387, testingError := fun _ => 387,
    dose := 29352, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F2_8303_K0_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), some (0 : Rat), none] [] (75770 : Int), datedRead (0 : Rat) #v[some (0 : Rat), none, some (0 : Rat)] [] (73586 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), some (22 : Rat), none] [] (91298 : Int), datedRead (22 : Rat) #v[some (22 : Rat), none, some (22 : Rat)] [] (89114 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), some (44 : Rat), none] [(448457 / 10000 : Rat)] (106826 : Int), datedRead (44 : Rat) #v[some (44 : Rat), none, some (44 : Rat)] [(89769 / 2000 : Rat)] (104642 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), some (66 : Rat), none] [(668457 / 10000 : Rat)] (106826 : Int), datedRead (66 : Rat) #v[some (66 : Rat), none, some (66 : Rat)] [(133769 / 2000 : Rat)] (104642 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), some (88 : Rat), none] [(888457 / 10000 : Rat)] (106826 : Int), datedRead (88 : Rat) #v[some (88 : Rat), none, some (88 : Rat)] [(177769 / 2000 : Rat)] (104642 : Int)]]
private def trace_F2_8303_K0_te : List (List (ReadObservation 3)) := [[datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [(1108457 / 10000 : Rat)] (106826 : Int), datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [] (52322 : Int)], [datedRead (132 : Rat) #v[some (132 : Rat), none, some (132 : Rat)] [] (53414 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none, some (132 : Rat)] [(265769 / 2000 : Rat)] (104642 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat), none] [(1548457 / 10000 : Rat)] (106826 : Int), datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat), none] [] (52322 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none, some (176 : Rat)] [] (53414 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none, some (176 : Rat)] [(353769 / 2000 : Rat)] (104642 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat), none] [(1988457 / 10000 : Rat)] (106826 : Int), datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat), none] [] (52322 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none, some (220 : Rat)] [] (53414 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none, some (220 : Rat)] [(441769 / 2000 : Rat)] (104642 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), some (242 : Rat), none] [(2428457 / 10000 : Rat)] (106826 : Int), datedRead (242 : Rat) #v[some (242 : Rat), some (242 : Rat), none] [] (52322 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none, some (264 : Rat)] [] (53414 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none, some (264 : Rat)] [(529769 / 2000 : Rat)] (104642 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), some (286 : Rat), none] [(2868457 / 10000 : Rat)] (106826 : Int), datedRead (286 : Rat) #v[some (286 : Rat), some (286 : Rat), none] [] (52322 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none, some (308 : Rat)] [] (53414 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none, some (308 : Rat)] [(617769 / 2000 : Rat)] (104642 : Int)]]
private def trace_F2_8303_K0_st : List (ReadObservation 2) := [datedRead (1123457 / 10000 : Rat) #v[some (1123457 / 10000 : Rat), none] [] (52351 : Int), datedRead (268769 / 2000 : Rat) #v[none, some (268769 / 2000 : Rat)] [] (47649 : Int), datedRead (1563457 / 10000 : Rat) #v[some (1563457 / 10000 : Rat), none] [] (81707 : Int), datedRead (356769 / 2000 : Rat) #v[none, some (356769 / 2000 : Rat)] [] (77005 : Int), datedRead (2003457 / 10000 : Rat) #v[some (2003457 / 10000 : Rat), none] [(503019 / 2500 : Rat)] (111061 : Int), datedRead (444769 / 2000 : Rat) #v[none, some (444769 / 2000 : Rat)] [(2232943 / 10000 : Rat)] (106358 : Int), datedRead (2443457 / 10000 : Rat) #v[some (2443457 / 10000 : Rat), none] [(613019 / 2500 : Rat)] (111061 : Int), datedRead (532769 / 2000 : Rat) #v[none, some (532769 / 2000 : Rat)] [(2672943 / 10000 : Rat)] (106358 : Int), datedRead (2883457 / 10000 : Rat) #v[some (2883457 / 10000 : Rat), none] [(723019 / 2500 : Rat)] (111061 : Int), datedRead (620769 / 2000 : Rat) #v[none, some (620769 / 2000 : Rat)] [(3112943 / 10000 : Rat)] (106358 : Int)]
private def trace_F2_8303_K0_fx : List (List (ReadObservation 3)) := [[datedRead (330 : Rat) #v[none, none, none] [] (0 : Int), datedRead (330 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (0 : Int), datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (52321 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (53413 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (0 : Int)], [datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (53413 : Int), datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (52321 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (53414 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (52322 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [] (53414 : Int), datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [(881769 / 2000 : Rat)] (104642 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [(3968457 / 10000 : Rat)] (106826 : Int), datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [] (52322 : Int)], [datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(4848457 / 10000 : Rat)] (106826 : Int), datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(969769 / 2000 : Rat)] (104642 : Int)]]
private def trace_F2_8303_K0_sx : List (ReadObservation 2) := [datedRead (663 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (927 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (884769 / 2000 : Rat) #v[none, some (884769 / 2000 : Rat)] [(4432943 / 10000 : Rat)] (106358 : Int), datedRead (3983457 / 10000 : Rat) #v[some (3983457 / 10000 : Rat), none] [(998019 / 2500 : Rat)] (111061 : Int), datedRead (4863457 / 10000 : Rat) #v[some (4863457 / 10000 : Rat), some (972769 / 2000 : Rat)] [(1216529 / 2500 : Rat)] (217414 : Int)]
private def trace_F2_8303_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)]]

def trace_F2_8303_K0 : TraceTables cascade_F2_8303_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F2_8303_K0_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F2_8303_K0_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F2_8303_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F2_8303_K0_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8303_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8303_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F2_8303_K0 : checks cascade_F2_8303_K0 trace_F2_8303_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F2_8303_K0 : checkCascadeValid cascade_F2_8303_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F2_8303_K0 : checkTrainingSeparation cascade_F2_8303_K0 left right trace_F2_8303_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F2_8303_K0 : checkCascadeCalibrationOneSided cascade_F2_8303_K0 left right trace_F2_8303_K0.observations trace_F2_8303_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F2_8303_K0 : ∀ x i, (trace_F2_8303_K0.observations.secondTest x i).fired = output cascade_F2_8303_K0 i x := by
  have checked := checks_F2_8303_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_F2_8303_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F2_8303_K0.observations trace_F2_8303_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F2_8303_K3 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[37886, 37885, 0], #v[36794, 0, 36793]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[2549, 2550] : Vector Nat 2).get a,
    testingError := fun a => (#v[2549, 2550] : Vector Nat 2).get a,
    dose := 7763, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[52354, 47651] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 4811, testingError := fun _ => 4811,
    dose := 29352, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F2_8303_K3_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), some (0 : Rat), none] [] (75770 : Int), datedRead (0 : Rat) #v[some (0 : Rat), none, some (0 : Rat)] [] (73586 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), some (22 : Rat), none] [] (91298 : Int), datedRead (22 : Rat) #v[some (22 : Rat), none, some (22 : Rat)] [] (89114 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), some (44 : Rat), none] [(448457 / 10000 : Rat)] (106826 : Int), datedRead (44 : Rat) #v[some (44 : Rat), none, some (44 : Rat)] [(89769 / 2000 : Rat)] (104642 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), some (66 : Rat), none] [(668457 / 10000 : Rat)] (106826 : Int), datedRead (66 : Rat) #v[some (66 : Rat), none, some (66 : Rat)] [(133769 / 2000 : Rat)] (104642 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), some (88 : Rat), none] [(888457 / 10000 : Rat)] (106826 : Int), datedRead (88 : Rat) #v[some (88 : Rat), none, some (88 : Rat)] [(177769 / 2000 : Rat)] (104642 : Int)]]
private def trace_F2_8303_K3_te : List (List (ReadObservation 3)) := [[datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [(1108457 / 10000 : Rat)] (106826 : Int), datedRead (110 : Rat) #v[some (110 : Rat), some (110 : Rat), none] [] (52322 : Int)], [datedRead (132 : Rat) #v[some (132 : Rat), none, some (132 : Rat)] [] (53414 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none, some (132 : Rat)] [(265769 / 2000 : Rat)] (104642 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat), none] [(1548457 / 10000 : Rat)] (106826 : Int), datedRead (154 : Rat) #v[some (154 : Rat), some (154 : Rat), none] [] (52322 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none, some (176 : Rat)] [] (53414 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none, some (176 : Rat)] [(353769 / 2000 : Rat)] (104642 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat), none] [(1988457 / 10000 : Rat)] (106826 : Int), datedRead (198 : Rat) #v[some (198 : Rat), some (198 : Rat), none] [] (52322 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none, some (220 : Rat)] [] (53414 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none, some (220 : Rat)] [(441769 / 2000 : Rat)] (104642 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), some (242 : Rat), none] [(2428457 / 10000 : Rat)] (106826 : Int), datedRead (242 : Rat) #v[some (242 : Rat), some (242 : Rat), none] [] (52322 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none, some (264 : Rat)] [] (53414 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none, some (264 : Rat)] [(529769 / 2000 : Rat)] (104642 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), some (286 : Rat), none] [(2868457 / 10000 : Rat)] (106826 : Int), datedRead (286 : Rat) #v[some (286 : Rat), some (286 : Rat), none] [] (52322 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none, some (308 : Rat)] [] (53414 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none, some (308 : Rat)] [(617769 / 2000 : Rat)] (104642 : Int)]]
private def trace_F2_8303_K3_st : List (ReadObservation 2) := [datedRead (1123457 / 10000 : Rat) #v[some (1123457 / 10000 : Rat), none] [] (52351 : Int), datedRead (268769 / 2000 : Rat) #v[none, some (268769 / 2000 : Rat)] [] (47649 : Int), datedRead (1563457 / 10000 : Rat) #v[some (1563457 / 10000 : Rat), none] [] (81707 : Int), datedRead (356769 / 2000 : Rat) #v[none, some (356769 / 2000 : Rat)] [] (77005 : Int), datedRead (2003457 / 10000 : Rat) #v[some (2003457 / 10000 : Rat), none] [(503019 / 2500 : Rat)] (111061 : Int), datedRead (444769 / 2000 : Rat) #v[none, some (444769 / 2000 : Rat)] [(2232943 / 10000 : Rat)] (106358 : Int), datedRead (2443457 / 10000 : Rat) #v[some (2443457 / 10000 : Rat), none] [(613019 / 2500 : Rat)] (111061 : Int), datedRead (532769 / 2000 : Rat) #v[none, some (532769 / 2000 : Rat)] [(2672943 / 10000 : Rat)] (106358 : Int), datedRead (2883457 / 10000 : Rat) #v[some (2883457 / 10000 : Rat), none] [(723019 / 2500 : Rat)] (111061 : Int), datedRead (620769 / 2000 : Rat) #v[none, some (620769 / 2000 : Rat)] [(3112943 / 10000 : Rat)] (106358 : Int)]
private def trace_F2_8303_K3_fx : List (List (ReadObservation 3)) := [[datedRead (330 : Rat) #v[none, none, none] [] (0 : Int), datedRead (330 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (0 : Int), datedRead (418 : Rat) #v[none, none, some (418 : Rat)] [] (52321 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (53413 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat), none] [] (0 : Int)], [datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (53413 : Int), datedRead (462 : Rat) #v[none, some (462 : Rat), some (462 : Rat)] [] (52321 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (53414 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (52322 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [] (53414 : Int), datedRead (440 : Rat) #v[some (440 : Rat), none, some (440 : Rat)] [(881769 / 2000 : Rat)] (104642 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [(3968457 / 10000 : Rat)] (106826 : Int), datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat), none] [] (52322 : Int)], [datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(4848457 / 10000 : Rat)] (106826 : Int), datedRead (484 : Rat) #v[some (484 : Rat), some (484 : Rat), some (484 : Rat)] [(969769 / 2000 : Rat)] (104642 : Int)]]
private def trace_F2_8303_K3_sx : List (ReadObservation 2) := [datedRead (663 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (927 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (884769 / 2000 : Rat) #v[none, some (884769 / 2000 : Rat)] [(4432943 / 10000 : Rat)] (106358 : Int), datedRead (3983457 / 10000 : Rat) #v[some (3983457 / 10000 : Rat), none] [(998019 / 2500 : Rat)] (111061 : Int), datedRead (4863457 / 10000 : Rat) #v[some (4863457 / 10000 : Rat), some (972769 / 2000 : Rat)] [(1216529 / 2500 : Rat)] (217414 : Int)]
private def trace_F2_8303_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)]]

def trace_F2_8303_K3 : TraceTables cascade_F2_8303_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F2_8303_K3_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F2_8303_K3_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F2_8303_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F2_8303_K3_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8303_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F2_8303_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F2_8303_K3 : checks cascade_F2_8303_K3 trace_F2_8303_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F2_8303_K3 : checkCascadeValid cascade_F2_8303_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F2_8303_K3 : checkTrainingSeparation cascade_F2_8303_K3 left right trace_F2_8303_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F2_8303_K3 : checkCascadeCalibrationOneSided cascade_F2_8303_K3 left right trace_F2_8303_K3.observations trace_F2_8303_K3.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F2_8303_K3 : ∀ x i, (trace_F2_8303_K3.observations.secondTest x i).fired = output cascade_F2_8303_K3 i x := by
  have checked := checks_F2_8303_K3
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_F2_8303_K3
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F2_8303_K3.observations trace_F2_8303_K3.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
