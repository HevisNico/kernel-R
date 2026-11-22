import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F4, instance 8308.
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

def cascade_F4_8308_K0 : Cascade 2 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[89355, 0], #v[0, 83324]] : Vector (Vector Nat 2) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[105, 105] : Vector Nat 2).get a,
    testingError := fun a => (#v[105, 105] : Vector Nat 2).get a,
    dose := 7795, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[45070, 54937] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 489, testingError := fun _ => 489,
    dose := 37148, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F4_8308_K0_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none] [] (89354 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat)] [] (83323 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none] [] (97151 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat)] [] (91120 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none] [(55999 / 1250 : Rat)] (104947 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat)] [] (98916 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none] [(83499 / 1250 : Rat)] (104947 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat)] [(166889 / 2500 : Rat)] (106711 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none] [(110999 / 1250 : Rat)] (104947 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat)] [(221889 / 2500 : Rat)] (106711 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), none] [(138499 / 1250 : Rat)] (104947 : Int), datedRead (110 : Rat) #v[none, some (110 : Rat)] [(276889 / 2500 : Rat)] (106711 : Int)]]
private def trace_F4_8308_K0_te : List (List (ReadObservation 2)) := [[datedRead (132 : Rat) #v[some (132 : Rat), none] [(165999 / 1250 : Rat)] (104947 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none] [] (0 : Int)], [datedRead (154 : Rat) #v[none, some (154 : Rat)] [] (0 : Int), datedRead (154 : Rat) #v[none, some (154 : Rat)] [(386889 / 2500 : Rat)] (106711 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none] [(220999 / 1250 : Rat)] (104947 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none] [] (0 : Int)], [datedRead (198 : Rat) #v[none, some (198 : Rat)] [] (0 : Int), datedRead (198 : Rat) #v[none, some (198 : Rat)] [(496889 / 2500 : Rat)] (106711 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none] [(275999 / 1250 : Rat)] (104947 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none] [] (0 : Int)], [datedRead (242 : Rat) #v[none, some (242 : Rat)] [] (0 : Int), datedRead (242 : Rat) #v[none, some (242 : Rat)] [(606889 / 2500 : Rat)] (106711 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none] [(330999 / 1250 : Rat)] (104947 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat)] [] (0 : Int), datedRead (286 : Rat) #v[none, some (286 : Rat)] [(716889 / 2500 : Rat)] (106711 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none] [(385999 / 1250 : Rat)] (104947 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none] [] (0 : Int)], [datedRead (330 : Rat) #v[none, some (330 : Rat)] [] (0 : Int), datedRead (330 : Rat) #v[none, some (330 : Rat)] [(826889 / 2500 : Rat)] (106711 : Int)]]
private def trace_F4_8308_K0_st : List (ReadObservation 2) := [datedRead (83937 / 625 : Rat) #v[some (83937 / 625 : Rat), none] [] (45066 : Int), datedRead (390639 / 2500 : Rat) #v[none, some (390639 / 2500 : Rat)] [] (54934 : Int), datedRead (111437 / 625 : Rat) #v[some (111437 / 625 : Rat), none] [] (82219 : Int), datedRead (500639 / 2500 : Rat) #v[none, some (500639 / 2500 : Rat)] [] (92087 : Int), datedRead (138937 / 625 : Rat) #v[some (138937 / 625 : Rat), none] [(2231237 / 10000 : Rat)] (119369 : Int), datedRead (610639 / 2500 : Rat) #v[none, some (610639 / 2500 : Rat)] [(612563 / 2500 : Rat)] (129237 : Int), datedRead (166437 / 625 : Rat) #v[some (166437 / 625 : Rat), none] [(2671237 / 10000 : Rat)] (119369 : Int), datedRead (720639 / 2500 : Rat) #v[none, some (720639 / 2500 : Rat)] [(722563 / 2500 : Rat)] (129237 : Int), datedRead (193937 / 625 : Rat) #v[some (193937 / 625 : Rat), none] [(3111237 / 10000 : Rat)] (119369 : Int), datedRead (830639 / 2500 : Rat) #v[none, some (830639 / 2500 : Rat)] [(832563 / 2500 : Rat)] (129237 : Int)]
private def trace_F4_8308_K0_fx : List (List (ReadObservation 2)) := [[datedRead (352 : Rat) #v[none, none] [] (0 : Int), datedRead (352 : Rat) #v[none, none] [] (0 : Int)], [datedRead (396 : Rat) #v[none, some (396 : Rat)] [] (0 : Int), datedRead (396 : Rat) #v[none, some (396 : Rat)] [(991889 / 2500 : Rat)] (106711 : Int)], [datedRead (374 : Rat) #v[some (374 : Rat), none] [(468499 / 1250 : Rat)] (104947 : Int), datedRead (374 : Rat) #v[some (374 : Rat), none] [] (0 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat)] [(523499 / 1250 : Rat)] (104947 : Int), datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat)] [(1046889 / 2500 : Rat)] (106711 : Int)]]
private def trace_F4_8308_K0_sx : List (ReadObservation 2) := [datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (995639 / 2500 : Rat) #v[none, some (995639 / 2500 : Rat)] [(997563 / 2500 : Rat)] (129237 : Int), datedRead (235187 / 625 : Rat) #v[some (235187 / 625 : Rat), none] [(3771237 / 10000 : Rat)] (119369 : Int), datedRead (1050639 / 2500 : Rat) #v[some (262687 / 625 : Rat), some (1050639 / 2500 : Rat)] [(841023 / 2000 : Rat)] (248599 : Int)]
private def trace_F4_8308_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)]]

def trace_F4_8308_K0 : TraceTables cascade_F4_8308_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F4_8308_K0_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F4_8308_K0_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_F4_8308_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F4_8308_K0_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8308_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8308_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F4_8308_K0 : checks cascade_F4_8308_K0 trace_F4_8308_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F4_8308_K0 : checkCascadeValid cascade_F4_8308_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F4_8308_K0 : checkTrainingSeparation cascade_F4_8308_K0 left right trace_F4_8308_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F4_8308_K0 : checkCascadeCalibrationOneSided cascade_F4_8308_K0 left right trace_F4_8308_K0.observations trace_F4_8308_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F4_8308_K0 : ∀ x i, (trace_F4_8308_K0.observations.secondTest x i).fired = output cascade_F4_8308_K0 i x := by
  have checked := checks_F4_8308_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 2 cascade_F4_8308_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F4_8308_K0.observations trace_F4_8308_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F4_8308_K3 : Cascade 2 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[89355, 0], #v[0, 83324]] : Vector (Vector Nat 2) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[1277, 1284] : Vector Nat 2).get a,
    testingError := fun a => (#v[1277, 1284] : Vector Nat 2).get a,
    dose := 7795, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[45070, 54937] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 6090, testingError := fun _ => 6090,
    dose := 37148, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F4_8308_K3_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none] [] (89354 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat)] [] (83323 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none] [] (97151 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat)] [] (91120 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none] [(55999 / 1250 : Rat)] (104947 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat)] [] (98916 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none] [(83499 / 1250 : Rat)] (104947 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat)] [(166889 / 2500 : Rat)] (106711 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none] [(110999 / 1250 : Rat)] (104947 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat)] [(221889 / 2500 : Rat)] (106711 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), none] [(138499 / 1250 : Rat)] (104947 : Int), datedRead (110 : Rat) #v[none, some (110 : Rat)] [(276889 / 2500 : Rat)] (106711 : Int)]]
private def trace_F4_8308_K3_te : List (List (ReadObservation 2)) := [[datedRead (132 : Rat) #v[some (132 : Rat), none] [(165999 / 1250 : Rat)] (104947 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none] [] (0 : Int)], [datedRead (154 : Rat) #v[none, some (154 : Rat)] [] (0 : Int), datedRead (154 : Rat) #v[none, some (154 : Rat)] [(386889 / 2500 : Rat)] (106711 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none] [(220999 / 1250 : Rat)] (104947 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none] [] (0 : Int)], [datedRead (198 : Rat) #v[none, some (198 : Rat)] [] (0 : Int), datedRead (198 : Rat) #v[none, some (198 : Rat)] [(496889 / 2500 : Rat)] (106711 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none] [(275999 / 1250 : Rat)] (104947 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none] [] (0 : Int)], [datedRead (242 : Rat) #v[none, some (242 : Rat)] [] (0 : Int), datedRead (242 : Rat) #v[none, some (242 : Rat)] [(606889 / 2500 : Rat)] (106711 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none] [(330999 / 1250 : Rat)] (104947 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat)] [] (0 : Int), datedRead (286 : Rat) #v[none, some (286 : Rat)] [(716889 / 2500 : Rat)] (106711 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none] [(385999 / 1250 : Rat)] (104947 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none] [] (0 : Int)], [datedRead (330 : Rat) #v[none, some (330 : Rat)] [] (0 : Int), datedRead (330 : Rat) #v[none, some (330 : Rat)] [(826889 / 2500 : Rat)] (106711 : Int)]]
private def trace_F4_8308_K3_st : List (ReadObservation 2) := [datedRead (83937 / 625 : Rat) #v[some (83937 / 625 : Rat), none] [] (45066 : Int), datedRead (390639 / 2500 : Rat) #v[none, some (390639 / 2500 : Rat)] [] (54934 : Int), datedRead (111437 / 625 : Rat) #v[some (111437 / 625 : Rat), none] [] (82219 : Int), datedRead (500639 / 2500 : Rat) #v[none, some (500639 / 2500 : Rat)] [] (92087 : Int), datedRead (138937 / 625 : Rat) #v[some (138937 / 625 : Rat), none] [(2231237 / 10000 : Rat)] (119369 : Int), datedRead (610639 / 2500 : Rat) #v[none, some (610639 / 2500 : Rat)] [(612563 / 2500 : Rat)] (129237 : Int), datedRead (166437 / 625 : Rat) #v[some (166437 / 625 : Rat), none] [(2671237 / 10000 : Rat)] (119369 : Int), datedRead (720639 / 2500 : Rat) #v[none, some (720639 / 2500 : Rat)] [(722563 / 2500 : Rat)] (129237 : Int), datedRead (193937 / 625 : Rat) #v[some (193937 / 625 : Rat), none] [(3111237 / 10000 : Rat)] (119369 : Int), datedRead (830639 / 2500 : Rat) #v[none, some (830639 / 2500 : Rat)] [(832563 / 2500 : Rat)] (129237 : Int)]
private def trace_F4_8308_K3_fx : List (List (ReadObservation 2)) := [[datedRead (352 : Rat) #v[none, none] [] (0 : Int), datedRead (352 : Rat) #v[none, none] [] (0 : Int)], [datedRead (396 : Rat) #v[none, some (396 : Rat)] [] (0 : Int), datedRead (396 : Rat) #v[none, some (396 : Rat)] [(991889 / 2500 : Rat)] (106711 : Int)], [datedRead (374 : Rat) #v[some (374 : Rat), none] [(468499 / 1250 : Rat)] (104947 : Int), datedRead (374 : Rat) #v[some (374 : Rat), none] [] (0 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat)] [(523499 / 1250 : Rat)] (104947 : Int), datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat)] [(1046889 / 2500 : Rat)] (106711 : Int)]]
private def trace_F4_8308_K3_sx : List (ReadObservation 2) := [datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (995639 / 2500 : Rat) #v[none, some (995639 / 2500 : Rat)] [(997563 / 2500 : Rat)] (129237 : Int), datedRead (235187 / 625 : Rat) #v[some (235187 / 625 : Rat), none] [(3771237 / 10000 : Rat)] (119369 : Int), datedRead (1050639 / 2500 : Rat) #v[some (262687 / 625 : Rat), some (1050639 / 2500 : Rat)] [(841023 / 2000 : Rat)] (248599 : Int)]
private def trace_F4_8308_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)], #v[(0 : Int), (129237 : Int), (119369 : Int), (248599 : Int)]]

def trace_F4_8308_K3 : TraceTables cascade_F4_8308_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F4_8308_K3_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F4_8308_K3_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_F4_8308_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F4_8308_K3_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8308_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8308_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F4_8308_K3 : checks cascade_F4_8308_K3 trace_F4_8308_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F4_8308_K3 : checkCascadeValid cascade_F4_8308_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F4_8308_K3 : checkTrainingSeparation cascade_F4_8308_K3 left right trace_F4_8308_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F4_8308_K3 : checkCascadeCalibrationOneSided cascade_F4_8308_K3 left right trace_F4_8308_K3.observations trace_F4_8308_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
