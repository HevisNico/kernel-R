import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F4, instance 8505.
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

def cascade_F4_8505_K0 : Cascade 2 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[88997, 0], #v[0, 85938]] : Vector (Vector Nat 2) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[102, 102] : Vector Nat 2).get a,
    testingError := fun a => (#v[102, 102] : Vector Nat 2).get a,
    dose := 7601, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[59276, 40733] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 322, testingError := fun _ => 322,
    dose := 24213, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F4_8505_K0_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none] [] (88996 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat)] [] (85937 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none] [] (96598 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat)] [] (93539 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none] [(28011 / 625 : Rat)] (104199 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat)] [(22467 / 500 : Rat)] (101140 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none] [(41761 / 625 : Rat)] (104199 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat)] [(33467 / 500 : Rat)] (101140 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none] [(55511 / 625 : Rat)] (104199 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat)] [(44467 / 500 : Rat)] (101140 : Int)]]
private def trace_F4_8505_K0_te : List (List (ReadObservation 2)) := [[datedRead (110 : Rat) #v[some (110 : Rat), none] [(69261 / 625 : Rat)] (104199 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none] [] (0 : Int)], [datedRead (132 : Rat) #v[none, some (132 : Rat)] [] (0 : Int), datedRead (132 : Rat) #v[none, some (132 : Rat)] [(66467 / 500 : Rat)] (101140 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none] [(96761 / 625 : Rat)] (104199 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none] [] (0 : Int)], [datedRead (176 : Rat) #v[none, some (176 : Rat)] [] (0 : Int), datedRead (176 : Rat) #v[none, some (176 : Rat)] [(88467 / 500 : Rat)] (101140 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none] [(124261 / 625 : Rat)] (104199 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none] [] (0 : Int)], [datedRead (220 : Rat) #v[none, some (220 : Rat)] [] (0 : Int), datedRead (220 : Rat) #v[none, some (220 : Rat)] [(110467 / 500 : Rat)] (101140 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none] [(151761 / 625 : Rat)] (104199 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none] [] (0 : Int)], [datedRead (264 : Rat) #v[none, some (264 : Rat)] [] (0 : Int), datedRead (264 : Rat) #v[none, some (264 : Rat)] [(132467 / 500 : Rat)] (101140 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none] [(179261 / 625 : Rat)] (104199 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none] [] (0 : Int)], [datedRead (308 : Rat) #v[none, some (308 : Rat)] [] (0 : Int), datedRead (308 : Rat) #v[none, some (308 : Rat)] [(154467 / 500 : Rat)] (101140 : Int)], [datedRead (330 : Rat) #v[some (330 : Rat), none] [(206761 / 625 : Rat)] (104199 : Int), datedRead (330 : Rat) #v[some (330 : Rat), none] [] (0 : Int)], [datedRead (352 : Rat) #v[none, some (352 : Rat)] [] (0 : Int), datedRead (352 : Rat) #v[none, some (352 : Rat)] [(176467 / 500 : Rat)] (101140 : Int)]]
private def trace_F4_8505_K0_st : List (ReadObservation 2) := [datedRead (140397 / 1250 : Rat) #v[some (140397 / 1250 : Rat), none] [] (59272 : Int), datedRead (67217 / 500 : Rat) #v[none, some (67217 / 500 : Rat)] [] (40730 : Int), datedRead (195397 / 1250 : Rat) #v[some (195397 / 1250 : Rat), none] [] (83490 : Int), datedRead (89217 / 500 : Rat) #v[none, some (89217 / 500 : Rat)] [] (64947 : Int), datedRead (250397 / 1250 : Rat) #v[some (250397 / 1250 : Rat), none] [(502991 / 2500 : Rat)] (107705 : Int), datedRead (111217 / 500 : Rat) #v[none, some (111217 / 500 : Rat)] [] (89162 : Int), datedRead (305397 / 1250 : Rat) #v[some (305397 / 1250 : Rat), none] [(612991 / 2500 : Rat)] (107705 : Int), datedRead (133217 / 500 : Rat) #v[none, some (133217 / 500 : Rat)] [(668131 / 2500 : Rat)] (113376 : Int), datedRead (360397 / 1250 : Rat) #v[some (360397 / 1250 : Rat), none] [(722991 / 2500 : Rat)] (107705 : Int), datedRead (155217 / 500 : Rat) #v[none, some (155217 / 500 : Rat)] [(778131 / 2500 : Rat)] (113376 : Int), datedRead (415397 / 1250 : Rat) #v[some (415397 / 1250 : Rat), none] [(832991 / 2500 : Rat)] (107705 : Int), datedRead (177217 / 500 : Rat) #v[none, some (177217 / 500 : Rat)] [(888131 / 2500 : Rat)] (113376 : Int)]
private def trace_F4_8505_K0_fx : List (List (ReadObservation 2)) := [[datedRead (374 : Rat) #v[none, none] [] (0 : Int), datedRead (374 : Rat) #v[none, none] [] (0 : Int)], [datedRead (418 : Rat) #v[none, some (418 : Rat)] [] (0 : Int), datedRead (418 : Rat) #v[none, some (418 : Rat)] [(209467 / 500 : Rat)] (101140 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), none] [(248011 / 625 : Rat)] (104199 : Int), datedRead (396 : Rat) #v[some (396 : Rat), none] [] (0 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat)] [(275511 / 625 : Rat)] (104199 : Int), datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat)] [(220467 / 500 : Rat)] (101140 : Int)]]
private def trace_F4_8505_K0_sx : List (ReadObservation 2) := [datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (210217 / 500 : Rat) #v[none, some (210217 / 500 : Rat)] [(1053131 / 2500 : Rat)] (113376 : Int), datedRead (497897 / 1250 : Rat) #v[some (497897 / 1250 : Rat), none] [(997991 / 2500 : Rat)] (107705 : Int), datedRead (552897 / 1250 : Rat) #v[some (552897 / 1250 : Rat), some (221217 / 500 : Rat)] [(4425939 / 10000 : Rat)] (196863 : Int)]
private def trace_F4_8505_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (113376 : Int), (107705 : Int), (196863 : Int)], #v[(0 : Int), (113376 : Int), (107705 : Int), (196863 : Int)], #v[(0 : Int), (113376 : Int), (107705 : Int), (196863 : Int)], #v[(0 : Int), (113376 : Int), (107705 : Int), (196863 : Int)]]

def trace_F4_8505_K0 : TraceTables cascade_F4_8505_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F4_8505_K0_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F4_8505_K0_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_F4_8505_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F4_8505_K0_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8505_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8505_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F4_8505_K0 : checks cascade_F4_8505_K0 trace_F4_8505_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F4_8505_K0 : checkCascadeValid cascade_F4_8505_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F4_8505_K0 : checkTrainingSeparation cascade_F4_8505_K0 left right trace_F4_8505_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F4_8505_K0 : checkCascadeCalibrationOneSided cascade_F4_8505_K0 left right trace_F4_8505_K0.observations trace_F4_8505_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F4_8505_K0 : ∀ x i, (trace_F4_8505_K0.observations.secondTest x i).fired = output cascade_F4_8505_K0 i x := by
  have checked := checks_F4_8505_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 2 cascade_F4_8505_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F4_8505_K0.observations trace_F4_8505_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F4_8505_K3 : Cascade 2 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[88997, 0], #v[0, 85938]] : Vector (Vector Nat 2) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[1243, 1245] : Vector Nat 2).get a,
    testingError := fun a => (#v[1243, 1245] : Vector Nat 2).get a,
    dose := 7601, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[59276, 40733] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 3982, testingError := fun _ => 3982,
    dose := 24213, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F4_8505_K3_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none] [] (88996 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat)] [] (85937 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none] [] (96598 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat)] [] (93539 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none] [(28011 / 625 : Rat)] (104199 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat)] [(22467 / 500 : Rat)] (101140 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none] [(41761 / 625 : Rat)] (104199 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat)] [(33467 / 500 : Rat)] (101140 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none] [(55511 / 625 : Rat)] (104199 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat)] [(44467 / 500 : Rat)] (101140 : Int)]]
private def trace_F4_8505_K3_te : List (List (ReadObservation 2)) := [[datedRead (110 : Rat) #v[some (110 : Rat), none] [(69261 / 625 : Rat)] (104199 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none] [] (0 : Int)], [datedRead (132 : Rat) #v[none, some (132 : Rat)] [] (0 : Int), datedRead (132 : Rat) #v[none, some (132 : Rat)] [(66467 / 500 : Rat)] (101140 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none] [(96761 / 625 : Rat)] (104199 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none] [] (0 : Int)], [datedRead (176 : Rat) #v[none, some (176 : Rat)] [] (0 : Int), datedRead (176 : Rat) #v[none, some (176 : Rat)] [(88467 / 500 : Rat)] (101140 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none] [(124261 / 625 : Rat)] (104199 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none] [] (0 : Int)], [datedRead (220 : Rat) #v[none, some (220 : Rat)] [] (0 : Int), datedRead (220 : Rat) #v[none, some (220 : Rat)] [(110467 / 500 : Rat)] (101140 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none] [(151761 / 625 : Rat)] (104199 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none] [] (0 : Int)], [datedRead (264 : Rat) #v[none, some (264 : Rat)] [] (0 : Int), datedRead (264 : Rat) #v[none, some (264 : Rat)] [(132467 / 500 : Rat)] (101140 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none] [(179261 / 625 : Rat)] (104199 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none] [] (0 : Int)], [datedRead (308 : Rat) #v[none, some (308 : Rat)] [] (0 : Int), datedRead (308 : Rat) #v[none, some (308 : Rat)] [(154467 / 500 : Rat)] (101140 : Int)], [datedRead (330 : Rat) #v[some (330 : Rat), none] [(206761 / 625 : Rat)] (104199 : Int), datedRead (330 : Rat) #v[some (330 : Rat), none] [] (0 : Int)], [datedRead (352 : Rat) #v[none, some (352 : Rat)] [] (0 : Int), datedRead (352 : Rat) #v[none, some (352 : Rat)] [(176467 / 500 : Rat)] (101140 : Int)]]
private def trace_F4_8505_K3_st : List (ReadObservation 2) := [datedRead (140397 / 1250 : Rat) #v[some (140397 / 1250 : Rat), none] [] (59272 : Int), datedRead (67217 / 500 : Rat) #v[none, some (67217 / 500 : Rat)] [] (40730 : Int), datedRead (195397 / 1250 : Rat) #v[some (195397 / 1250 : Rat), none] [] (83490 : Int), datedRead (89217 / 500 : Rat) #v[none, some (89217 / 500 : Rat)] [] (64947 : Int), datedRead (250397 / 1250 : Rat) #v[some (250397 / 1250 : Rat), none] [(502991 / 2500 : Rat)] (107705 : Int), datedRead (111217 / 500 : Rat) #v[none, some (111217 / 500 : Rat)] [] (89162 : Int), datedRead (305397 / 1250 : Rat) #v[some (305397 / 1250 : Rat), none] [(612991 / 2500 : Rat)] (107705 : Int), datedRead (133217 / 500 : Rat) #v[none, some (133217 / 500 : Rat)] [(668131 / 2500 : Rat)] (113376 : Int), datedRead (360397 / 1250 : Rat) #v[some (360397 / 1250 : Rat), none] [(722991 / 2500 : Rat)] (107705 : Int), datedRead (155217 / 500 : Rat) #v[none, some (155217 / 500 : Rat)] [(778131 / 2500 : Rat)] (113376 : Int), datedRead (415397 / 1250 : Rat) #v[some (415397 / 1250 : Rat), none] [(832991 / 2500 : Rat)] (107705 : Int), datedRead (177217 / 500 : Rat) #v[none, some (177217 / 500 : Rat)] [(888131 / 2500 : Rat)] (113376 : Int)]
private def trace_F4_8505_K3_fx : List (List (ReadObservation 2)) := [[datedRead (374 : Rat) #v[none, none] [] (0 : Int), datedRead (374 : Rat) #v[none, none] [] (0 : Int)], [datedRead (418 : Rat) #v[none, some (418 : Rat)] [] (0 : Int), datedRead (418 : Rat) #v[none, some (418 : Rat)] [(209467 / 500 : Rat)] (101140 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), none] [(248011 / 625 : Rat)] (104199 : Int), datedRead (396 : Rat) #v[some (396 : Rat), none] [] (0 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat)] [(275511 / 625 : Rat)] (104199 : Int), datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat)] [(220467 / 500 : Rat)] (101140 : Int)]]
private def trace_F4_8505_K3_sx : List (ReadObservation 2) := [datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (210217 / 500 : Rat) #v[none, some (210217 / 500 : Rat)] [(1053131 / 2500 : Rat)] (113376 : Int), datedRead (497897 / 1250 : Rat) #v[some (497897 / 1250 : Rat), none] [(997991 / 2500 : Rat)] (107705 : Int), datedRead (552897 / 1250 : Rat) #v[some (552897 / 1250 : Rat), some (221217 / 500 : Rat)] [(4425939 / 10000 : Rat)] (196863 : Int)]
private def trace_F4_8505_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (113376 : Int), (107705 : Int), (196863 : Int)], #v[(0 : Int), (113376 : Int), (107705 : Int), (196863 : Int)], #v[(0 : Int), (113376 : Int), (107705 : Int), (196863 : Int)], #v[(0 : Int), (113376 : Int), (107705 : Int), (196863 : Int)]]

def trace_F4_8505_K3 : TraceTables cascade_F4_8505_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F4_8505_K3_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F4_8505_K3_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_F4_8505_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F4_8505_K3_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8505_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8505_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F4_8505_K3 : checks cascade_F4_8505_K3 trace_F4_8505_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F4_8505_K3 : checkCascadeValid cascade_F4_8505_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F4_8505_K3 : checkTrainingSeparation cascade_F4_8505_K3 left right trace_F4_8505_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F4_8505_K3 : checkCascadeCalibrationOneSided cascade_F4_8505_K3 left right trace_F4_8505_K3.observations trace_F4_8505_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
