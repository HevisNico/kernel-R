import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F4, instance 8303.
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

def cascade_F4_8303_K0 : Cascade 2 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[88156, 0], #v[0, 87307]] : Vector (Vector Nat 2) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[105, 105] : Vector Nat 2).get a,
    testingError := fun a => (#v[105, 105] : Vector Nat 2).get a,
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

private def trace_F4_8303_K0_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none] [] (88155 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat)] [] (87306 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none] [] (95919 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat)] [] (95070 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none] [(89673 / 2000 : Rat)] (103682 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat)] [(224323 / 5000 : Rat)] (102833 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none] [(133673 / 2000 : Rat)] (103682 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat)] [(334323 / 5000 : Rat)] (102833 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none] [(177673 / 2000 : Rat)] (103682 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat)] [(444323 / 5000 : Rat)] (102833 : Int)]]
private def trace_F4_8303_K0_te : List (List (ReadObservation 2)) := [[datedRead (110 : Rat) #v[some (110 : Rat), none] [(221673 / 2000 : Rat)] (103682 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none] [] (0 : Int)], [datedRead (132 : Rat) #v[none, some (132 : Rat)] [] (0 : Int), datedRead (132 : Rat) #v[none, some (132 : Rat)] [(664323 / 5000 : Rat)] (102833 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none] [(309673 / 2000 : Rat)] (103682 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none] [] (0 : Int)], [datedRead (176 : Rat) #v[none, some (176 : Rat)] [] (0 : Int), datedRead (176 : Rat) #v[none, some (176 : Rat)] [(884323 / 5000 : Rat)] (102833 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none] [(397673 / 2000 : Rat)] (103682 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none] [] (0 : Int)], [datedRead (220 : Rat) #v[none, some (220 : Rat)] [] (0 : Int), datedRead (220 : Rat) #v[none, some (220 : Rat)] [(1104323 / 5000 : Rat)] (102833 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none] [(485673 / 2000 : Rat)] (103682 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none] [] (0 : Int)], [datedRead (264 : Rat) #v[none, some (264 : Rat)] [] (0 : Int), datedRead (264 : Rat) #v[none, some (264 : Rat)] [(1324323 / 5000 : Rat)] (102833 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none] [(573673 / 2000 : Rat)] (103682 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none] [] (0 : Int)], [datedRead (308 : Rat) #v[none, some (308 : Rat)] [] (0 : Int), datedRead (308 : Rat) #v[none, some (308 : Rat)] [(1544323 / 5000 : Rat)] (102833 : Int)]]
private def trace_F4_8303_K0_st : List (ReadObservation 2) := [datedRead (224673 / 2000 : Rat) #v[some (224673 / 2000 : Rat), none] [] (52351 : Int), datedRead (671823 / 5000 : Rat) #v[none, some (671823 / 5000 : Rat)] [] (47649 : Int), datedRead (312673 / 2000 : Rat) #v[some (312673 / 2000 : Rat), none] [] (81707 : Int), datedRead (891823 / 5000 : Rat) #v[none, some (891823 / 5000 : Rat)] [] (77005 : Int), datedRead (400673 / 2000 : Rat) #v[some (400673 / 2000 : Rat), none] [(125749 / 625 : Rat)] (111061 : Int), datedRead (1111823 / 5000 : Rat) #v[none, some (1111823 / 5000 : Rat)] [(279093 / 1250 : Rat)] (106358 : Int), datedRead (488673 / 2000 : Rat) #v[some (488673 / 2000 : Rat), none] [(153249 / 625 : Rat)] (111061 : Int), datedRead (1331823 / 5000 : Rat) #v[none, some (1331823 / 5000 : Rat)] [(334093 / 1250 : Rat)] (106358 : Int), datedRead (576673 / 2000 : Rat) #v[some (576673 / 2000 : Rat), none] [(180749 / 625 : Rat)] (111061 : Int), datedRead (1551823 / 5000 : Rat) #v[none, some (1551823 / 5000 : Rat)] [(389093 / 1250 : Rat)] (106358 : Int)]
private def trace_F4_8303_K0_fx : List (List (ReadObservation 2)) := [[datedRead (330 : Rat) #v[none, none] [] (0 : Int), datedRead (330 : Rat) #v[none, none] [] (0 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat)] [] (0 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat)] [(1874323 / 5000 : Rat)] (102833 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none] [(705673 / 2000 : Rat)] (103682 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none] [] (0 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat)] [(793673 / 2000 : Rat)] (103682 : Int), datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat)] [(1984323 / 5000 : Rat)] (102833 : Int)]]
private def trace_F4_8303_K0_sx : List (ReadObservation 2) := [datedRead (663 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (1881823 / 5000 : Rat) #v[none, some (1881823 / 5000 : Rat)] [(471593 / 1250 : Rat)] (106358 : Int), datedRead (708673 / 2000 : Rat) #v[some (708673 / 2000 : Rat), none] [(221999 / 625 : Rat)] (111061 : Int), datedRead (796673 / 2000 : Rat) #v[some (796673 / 2000 : Rat), some (1991823 / 5000 : Rat)] [(498253 / 1250 : Rat)] (217414 : Int)]
private def trace_F4_8303_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)]]

def trace_F4_8303_K0 : TraceTables cascade_F4_8303_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F4_8303_K0_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F4_8303_K0_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_F4_8303_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F4_8303_K0_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8303_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8303_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F4_8303_K0 : checks cascade_F4_8303_K0 trace_F4_8303_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F4_8303_K0 : checkCascadeValid cascade_F4_8303_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F4_8303_K0 : checkTrainingSeparation cascade_F4_8303_K0 left right trace_F4_8303_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F4_8303_K0 : checkCascadeCalibrationOneSided cascade_F4_8303_K0 left right trace_F4_8303_K0.observations trace_F4_8303_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F4_8303_K0 : ∀ x i, (trace_F4_8303_K0.observations.secondTest x i).fired = output cascade_F4_8303_K0 i x := by
  have checked := checks_F4_8303_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 2 cascade_F4_8303_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F4_8303_K0.observations trace_F4_8303_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F4_8303_K3 : Cascade 2 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[88156, 0], #v[0, 87307]] : Vector (Vector Nat 2) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[1275, 1278] : Vector Nat 2).get a,
    testingError := fun a => (#v[1275, 1278] : Vector Nat 2).get a,
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

private def trace_F4_8303_K3_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none] [] (88155 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat)] [] (87306 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none] [] (95919 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat)] [] (95070 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none] [(89673 / 2000 : Rat)] (103682 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat)] [(224323 / 5000 : Rat)] (102833 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none] [(133673 / 2000 : Rat)] (103682 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat)] [(334323 / 5000 : Rat)] (102833 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none] [(177673 / 2000 : Rat)] (103682 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat)] [(444323 / 5000 : Rat)] (102833 : Int)]]
private def trace_F4_8303_K3_te : List (List (ReadObservation 2)) := [[datedRead (110 : Rat) #v[some (110 : Rat), none] [(221673 / 2000 : Rat)] (103682 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none] [] (0 : Int)], [datedRead (132 : Rat) #v[none, some (132 : Rat)] [] (0 : Int), datedRead (132 : Rat) #v[none, some (132 : Rat)] [(664323 / 5000 : Rat)] (102833 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none] [(309673 / 2000 : Rat)] (103682 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none] [] (0 : Int)], [datedRead (176 : Rat) #v[none, some (176 : Rat)] [] (0 : Int), datedRead (176 : Rat) #v[none, some (176 : Rat)] [(884323 / 5000 : Rat)] (102833 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none] [(397673 / 2000 : Rat)] (103682 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none] [] (0 : Int)], [datedRead (220 : Rat) #v[none, some (220 : Rat)] [] (0 : Int), datedRead (220 : Rat) #v[none, some (220 : Rat)] [(1104323 / 5000 : Rat)] (102833 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none] [(485673 / 2000 : Rat)] (103682 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none] [] (0 : Int)], [datedRead (264 : Rat) #v[none, some (264 : Rat)] [] (0 : Int), datedRead (264 : Rat) #v[none, some (264 : Rat)] [(1324323 / 5000 : Rat)] (102833 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none] [(573673 / 2000 : Rat)] (103682 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none] [] (0 : Int)], [datedRead (308 : Rat) #v[none, some (308 : Rat)] [] (0 : Int), datedRead (308 : Rat) #v[none, some (308 : Rat)] [(1544323 / 5000 : Rat)] (102833 : Int)]]
private def trace_F4_8303_K3_st : List (ReadObservation 2) := [datedRead (224673 / 2000 : Rat) #v[some (224673 / 2000 : Rat), none] [] (52351 : Int), datedRead (671823 / 5000 : Rat) #v[none, some (671823 / 5000 : Rat)] [] (47649 : Int), datedRead (312673 / 2000 : Rat) #v[some (312673 / 2000 : Rat), none] [] (81707 : Int), datedRead (891823 / 5000 : Rat) #v[none, some (891823 / 5000 : Rat)] [] (77005 : Int), datedRead (400673 / 2000 : Rat) #v[some (400673 / 2000 : Rat), none] [(125749 / 625 : Rat)] (111061 : Int), datedRead (1111823 / 5000 : Rat) #v[none, some (1111823 / 5000 : Rat)] [(279093 / 1250 : Rat)] (106358 : Int), datedRead (488673 / 2000 : Rat) #v[some (488673 / 2000 : Rat), none] [(153249 / 625 : Rat)] (111061 : Int), datedRead (1331823 / 5000 : Rat) #v[none, some (1331823 / 5000 : Rat)] [(334093 / 1250 : Rat)] (106358 : Int), datedRead (576673 / 2000 : Rat) #v[some (576673 / 2000 : Rat), none] [(180749 / 625 : Rat)] (111061 : Int), datedRead (1551823 / 5000 : Rat) #v[none, some (1551823 / 5000 : Rat)] [(389093 / 1250 : Rat)] (106358 : Int)]
private def trace_F4_8303_K3_fx : List (List (ReadObservation 2)) := [[datedRead (330 : Rat) #v[none, none] [] (0 : Int), datedRead (330 : Rat) #v[none, none] [] (0 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat)] [] (0 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat)] [(1874323 / 5000 : Rat)] (102833 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none] [(705673 / 2000 : Rat)] (103682 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none] [] (0 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat)] [(793673 / 2000 : Rat)] (103682 : Int), datedRead (396 : Rat) #v[some (396 : Rat), some (396 : Rat)] [(1984323 / 5000 : Rat)] (102833 : Int)]]
private def trace_F4_8303_K3_sx : List (ReadObservation 2) := [datedRead (663 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (1881823 / 5000 : Rat) #v[none, some (1881823 / 5000 : Rat)] [(471593 / 1250 : Rat)] (106358 : Int), datedRead (708673 / 2000 : Rat) #v[some (708673 / 2000 : Rat), none] [(221999 / 625 : Rat)] (111061 : Int), datedRead (796673 / 2000 : Rat) #v[some (796673 / 2000 : Rat), some (1991823 / 5000 : Rat)] [(498253 / 1250 : Rat)] (217414 : Int)]
private def trace_F4_8303_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)], #v[(0 : Int), (106358 : Int), (111061 : Int), (217414 : Int)]]

def trace_F4_8303_K3 : TraceTables cascade_F4_8303_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F4_8303_K3_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F4_8303_K3_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_F4_8303_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F4_8303_K3_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8303_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8303_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F4_8303_K3 : checks cascade_F4_8303_K3 trace_F4_8303_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F4_8303_K3 : checkCascadeValid cascade_F4_8303_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F4_8303_K3 : checkTrainingSeparation cascade_F4_8303_K3 left right trace_F4_8303_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F4_8303_K3 : checkCascadeCalibrationOneSided cascade_F4_8303_K3 left right trace_F4_8303_K3.observations trace_F4_8303_K3.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F4_8303_K3 : ∀ x i, (trace_F4_8303_K3.observations.secondTest x i).fired = output cascade_F4_8303_K3 i x := by
  have checked := checks_F4_8303_K3
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 2 cascade_F4_8303_K3
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F4_8303_K3.observations trace_F4_8303_K3.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
