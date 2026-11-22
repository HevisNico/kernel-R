import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F4, instance 8306.
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

def cascade_F4_8306_K0 : Cascade 2 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[82445, 0], #v[0, 82326]] : Vector (Vector Nat 2) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[103, 103] : Vector Nat 2).get a,
    testingError := fun a => (#v[103, 103] : Vector Nat 2).get a,
    dose := 7673, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[62638, 37370] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 363, testingError := fun _ => 363,
    dose := 27286, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F4_8306_K0_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none] [] (82444 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat)] [] (82324 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none] [] (90119 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat)] [] (89999 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none] [] (97793 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat)] [] (97673 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none] [(333923 / 5000 : Rat)] (105466 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat)] [(5343 / 80 : Rat)] (105346 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none] [(443923 / 5000 : Rat)] (105466 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat)] [(7103 / 80 : Rat)] (105346 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), none] [(553923 / 5000 : Rat)] (105466 : Int), datedRead (110 : Rat) #v[none, some (110 : Rat)] [(8863 / 80 : Rat)] (105346 : Int)]]
private def trace_F4_8306_K0_te : List (List (ReadObservation 2)) := [[datedRead (132 : Rat) #v[some (132 : Rat), none] [(663923 / 5000 : Rat)] (105466 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none] [] (0 : Int)], [datedRead (154 : Rat) #v[none, some (154 : Rat)] [] (0 : Int), datedRead (154 : Rat) #v[none, some (154 : Rat)] [(12383 / 80 : Rat)] (105346 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none] [(883923 / 5000 : Rat)] (105466 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none] [] (0 : Int)], [datedRead (198 : Rat) #v[none, some (198 : Rat)] [] (0 : Int), datedRead (198 : Rat) #v[none, some (198 : Rat)] [(15903 / 80 : Rat)] (105346 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none] [(1103923 / 5000 : Rat)] (105466 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none] [] (0 : Int)], [datedRead (242 : Rat) #v[none, some (242 : Rat)] [] (0 : Int), datedRead (242 : Rat) #v[none, some (242 : Rat)] [(19423 / 80 : Rat)] (105346 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none] [(1323923 / 5000 : Rat)] (105466 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat)] [] (0 : Int), datedRead (286 : Rat) #v[none, some (286 : Rat)] [(22943 / 80 : Rat)] (105346 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none] [(1543923 / 5000 : Rat)] (105466 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none] [] (0 : Int)], [datedRead (330 : Rat) #v[none, some (330 : Rat)] [] (0 : Int), datedRead (330 : Rat) #v[none, some (330 : Rat)] [(26463 / 80 : Rat)] (105346 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none] [(1763923 / 5000 : Rat)] (105466 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none] [] (0 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat)] [] (0 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat)] [(29983 / 80 : Rat)] (105346 : Int)]]
private def trace_F4_8306_K0_st : List (ReadObservation 2) := [datedRead (671423 / 5000 : Rat) #v[some (671423 / 5000 : Rat), none] [] (62633 : Int), datedRead (12503 / 80 : Rat) #v[none, some (12503 / 80 : Rat)] [] (37367 : Int), datedRead (891423 / 5000 : Rat) #v[some (891423 / 5000 : Rat), none] [] (89924 : Int), datedRead (16023 / 80 : Rat) #v[none, some (16023 / 80 : Rat)] [] (64657 : Int), datedRead (1111423 / 5000 : Rat) #v[some (1111423 / 5000 : Rat), none] [(44617 / 200 : Rat)] (117212 : Int), datedRead (19543 / 80 : Rat) #v[none, some (19543 / 80 : Rat)] [] (91945 : Int), datedRead (1331423 / 5000 : Rat) #v[some (1331423 / 5000 : Rat), none] [(53417 / 200 : Rat)] (117212 : Int), datedRead (23063 / 80 : Rat) #v[none, some (23063 / 80 : Rat)] [(2890723 / 10000 : Rat)] (119230 : Int), datedRead (1551423 / 5000 : Rat) #v[some (1551423 / 5000 : Rat), none] [(62217 / 200 : Rat)] (117212 : Int), datedRead (26583 / 80 : Rat) #v[none, some (26583 / 80 : Rat)] [(3330723 / 10000 : Rat)] (119230 : Int), datedRead (1771423 / 5000 : Rat) #v[some (1771423 / 5000 : Rat), none] [(71017 / 200 : Rat)] (117212 : Int), datedRead (30103 / 80 : Rat) #v[none, some (30103 / 80 : Rat)] [(3770723 / 10000 : Rat)] (119230 : Int)]
private def trace_F4_8306_K0_fx : List (List (ReadObservation 2)) := [[datedRead (396 : Rat) #v[none, none] [] (0 : Int), datedRead (396 : Rat) #v[none, none] [] (0 : Int)], [datedRead (440 : Rat) #v[none, some (440 : Rat)] [] (0 : Int), datedRead (440 : Rat) #v[none, some (440 : Rat)] [(35263 / 80 : Rat)] (105346 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), none] [(2093923 / 5000 : Rat)] (105466 : Int), datedRead (418 : Rat) #v[some (418 : Rat), none] [] (0 : Int)], [datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat)] [(2313923 / 5000 : Rat)] (105466 : Int), datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat)] [(37023 / 80 : Rat)] (105346 : Int)]]
private def trace_F4_8306_K0_sx : List (ReadObservation 2) := [datedRead (795 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (35383 / 80 : Rat) #v[none, some (35383 / 80 : Rat)] [(4430723 / 10000 : Rat)] (119230 : Int), datedRead (2101423 / 5000 : Rat) #v[some (2101423 / 5000 : Rat), none] [(84217 / 200 : Rat)] (117212 : Int), datedRead (2321423 / 5000 : Rat) #v[some (2321423 / 5000 : Rat), some (37143 / 80 : Rat)] [(929107 / 2000 : Rat)] (209152 : Int)]
private def trace_F4_8306_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (119230 : Int), (117212 : Int), (209152 : Int)], #v[(0 : Int), (119230 : Int), (117212 : Int), (209152 : Int)], #v[(0 : Int), (119230 : Int), (117212 : Int), (209152 : Int)], #v[(0 : Int), (119230 : Int), (117212 : Int), (209152 : Int)]]

def trace_F4_8306_K0 : TraceTables cascade_F4_8306_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F4_8306_K0_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F4_8306_K0_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_F4_8306_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F4_8306_K0_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8306_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8306_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F4_8306_K0 : checks cascade_F4_8306_K0 trace_F4_8306_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F4_8306_K0 : checkCascadeValid cascade_F4_8306_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F4_8306_K0 : checkTrainingSeparation cascade_F4_8306_K0 left right trace_F4_8306_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F4_8306_K0 : checkCascadeCalibrationOneSided cascade_F4_8306_K0 left right trace_F4_8306_K0.observations trace_F4_8306_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F4_8306_K0 : ∀ x i, (trace_F4_8306_K0.observations.secondTest x i).fired = output cascade_F4_8306_K0 i x := by
  have checked := checks_F4_8306_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 2 cascade_F4_8306_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F4_8306_K0.observations trace_F4_8306_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F4_8306_K3 : Cascade 2 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[82445, 0], #v[0, 82326]] : Vector (Vector Nat 2) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[1266, 1261] : Vector Nat 2).get a,
    testingError := fun a => (#v[1266, 1261] : Vector Nat 2).get a,
    dose := 7673, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[62638, 37370] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 4484, testingError := fun _ => 4484,
    dose := 27286, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F4_8306_K3_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none] [] (82444 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat)] [] (82324 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none] [] (90119 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat)] [] (89999 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none] [] (97793 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat)] [] (97673 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none] [(333923 / 5000 : Rat)] (105466 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat)] [(5343 / 80 : Rat)] (105346 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none] [(443923 / 5000 : Rat)] (105466 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat)] [(7103 / 80 : Rat)] (105346 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), none] [(553923 / 5000 : Rat)] (105466 : Int), datedRead (110 : Rat) #v[none, some (110 : Rat)] [(8863 / 80 : Rat)] (105346 : Int)]]
private def trace_F4_8306_K3_te : List (List (ReadObservation 2)) := [[datedRead (132 : Rat) #v[some (132 : Rat), none] [(663923 / 5000 : Rat)] (105466 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none] [] (0 : Int)], [datedRead (154 : Rat) #v[none, some (154 : Rat)] [] (0 : Int), datedRead (154 : Rat) #v[none, some (154 : Rat)] [(12383 / 80 : Rat)] (105346 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none] [(883923 / 5000 : Rat)] (105466 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none] [] (0 : Int)], [datedRead (198 : Rat) #v[none, some (198 : Rat)] [] (0 : Int), datedRead (198 : Rat) #v[none, some (198 : Rat)] [(15903 / 80 : Rat)] (105346 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none] [(1103923 / 5000 : Rat)] (105466 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none] [] (0 : Int)], [datedRead (242 : Rat) #v[none, some (242 : Rat)] [] (0 : Int), datedRead (242 : Rat) #v[none, some (242 : Rat)] [(19423 / 80 : Rat)] (105346 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none] [(1323923 / 5000 : Rat)] (105466 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat)] [] (0 : Int), datedRead (286 : Rat) #v[none, some (286 : Rat)] [(22943 / 80 : Rat)] (105346 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none] [(1543923 / 5000 : Rat)] (105466 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none] [] (0 : Int)], [datedRead (330 : Rat) #v[none, some (330 : Rat)] [] (0 : Int), datedRead (330 : Rat) #v[none, some (330 : Rat)] [(26463 / 80 : Rat)] (105346 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none] [(1763923 / 5000 : Rat)] (105466 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none] [] (0 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat)] [] (0 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat)] [(29983 / 80 : Rat)] (105346 : Int)]]
private def trace_F4_8306_K3_st : List (ReadObservation 2) := [datedRead (671423 / 5000 : Rat) #v[some (671423 / 5000 : Rat), none] [] (62633 : Int), datedRead (12503 / 80 : Rat) #v[none, some (12503 / 80 : Rat)] [] (37367 : Int), datedRead (891423 / 5000 : Rat) #v[some (891423 / 5000 : Rat), none] [] (89924 : Int), datedRead (16023 / 80 : Rat) #v[none, some (16023 / 80 : Rat)] [] (64657 : Int), datedRead (1111423 / 5000 : Rat) #v[some (1111423 / 5000 : Rat), none] [(44617 / 200 : Rat)] (117212 : Int), datedRead (19543 / 80 : Rat) #v[none, some (19543 / 80 : Rat)] [] (91945 : Int), datedRead (1331423 / 5000 : Rat) #v[some (1331423 / 5000 : Rat), none] [(53417 / 200 : Rat)] (117212 : Int), datedRead (23063 / 80 : Rat) #v[none, some (23063 / 80 : Rat)] [(2890723 / 10000 : Rat)] (119230 : Int), datedRead (1551423 / 5000 : Rat) #v[some (1551423 / 5000 : Rat), none] [(62217 / 200 : Rat)] (117212 : Int), datedRead (26583 / 80 : Rat) #v[none, some (26583 / 80 : Rat)] [(3330723 / 10000 : Rat)] (119230 : Int), datedRead (1771423 / 5000 : Rat) #v[some (1771423 / 5000 : Rat), none] [(71017 / 200 : Rat)] (117212 : Int), datedRead (30103 / 80 : Rat) #v[none, some (30103 / 80 : Rat)] [(3770723 / 10000 : Rat)] (119230 : Int)]
private def trace_F4_8306_K3_fx : List (List (ReadObservation 2)) := [[datedRead (396 : Rat) #v[none, none] [] (0 : Int), datedRead (396 : Rat) #v[none, none] [] (0 : Int)], [datedRead (440 : Rat) #v[none, some (440 : Rat)] [] (0 : Int), datedRead (440 : Rat) #v[none, some (440 : Rat)] [(35263 / 80 : Rat)] (105346 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), none] [(2093923 / 5000 : Rat)] (105466 : Int), datedRead (418 : Rat) #v[some (418 : Rat), none] [] (0 : Int)], [datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat)] [(2313923 / 5000 : Rat)] (105466 : Int), datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat)] [(37023 / 80 : Rat)] (105346 : Int)]]
private def trace_F4_8306_K3_sx : List (ReadObservation 2) := [datedRead (795 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (35383 / 80 : Rat) #v[none, some (35383 / 80 : Rat)] [(4430723 / 10000 : Rat)] (119230 : Int), datedRead (2101423 / 5000 : Rat) #v[some (2101423 / 5000 : Rat), none] [(84217 / 200 : Rat)] (117212 : Int), datedRead (2321423 / 5000 : Rat) #v[some (2321423 / 5000 : Rat), some (37143 / 80 : Rat)] [(929107 / 2000 : Rat)] (209152 : Int)]
private def trace_F4_8306_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (119230 : Int), (117212 : Int), (209152 : Int)], #v[(0 : Int), (119230 : Int), (117212 : Int), (209152 : Int)], #v[(0 : Int), (119230 : Int), (117212 : Int), (209152 : Int)], #v[(0 : Int), (119230 : Int), (117212 : Int), (209152 : Int)]]

def trace_F4_8306_K3 : TraceTables cascade_F4_8306_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F4_8306_K3_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F4_8306_K3_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_F4_8306_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F4_8306_K3_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8306_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8306_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F4_8306_K3 : checks cascade_F4_8306_K3 trace_F4_8306_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F4_8306_K3 : checkCascadeValid cascade_F4_8306_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F4_8306_K3 : checkTrainingSeparation cascade_F4_8306_K3 left right trace_F4_8306_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F4_8306_K3 : checkCascadeCalibrationOneSided cascade_F4_8306_K3 left right trace_F4_8306_K3.observations trace_F4_8306_K3.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F4_8306_K3 : ∀ x i, (trace_F4_8306_K3.observations.secondTest x i).fired = output cascade_F4_8306_K3 i x := by
  have checked := checks_F4_8306_K3
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 2 cascade_F4_8306_K3
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F4_8306_K3.observations trace_F4_8306_K3.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
