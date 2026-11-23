import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from synthetic.
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

def cascade_Syn_F3_K0 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[68750, 0, 0], #v[0, 18750, 18750]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[238, 425] : Vector Nat 2).get a,
    testingError := fun a => (#v[238, 425] : Vector Nat 2).get a,
    dose := 12500, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[50000, 50000] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 350, testingError := fun _ => 350,
    dose := 20000, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_Syn_F3_K0_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none, none] [] (68750 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat), some (0 : Rat)] [] (37500 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none, none] [] (81250 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat), some (22 : Rat)] [] (62500 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none, none] [] (93750 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat), some (44 : Rat)] [] (87500 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none, none] [(133 / 2 : Rat)] (106250 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat), some (66 : Rat)] [(133 / 2 : Rat)] (112500 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none, none] [(177 / 2 : Rat)] (106250 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat), some (88 : Rat)] [(177 / 2 : Rat)] (112500 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), none, none] [(221 / 2 : Rat)] (106250 : Int), datedRead (110 : Rat) #v[none, some (110 : Rat), some (110 : Rat)] [(221 / 2 : Rat)] (112500 : Int)]]
private def trace_Syn_F3_K0_te : List (List (ReadObservation 3)) := [[datedRead (132 : Rat) #v[some (132 : Rat), none, none] [(265 / 2 : Rat)] (106250 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none, none] [] (0 : Int)], [datedRead (154 : Rat) #v[none, some (154 : Rat), some (154 : Rat)] [] (0 : Int), datedRead (154 : Rat) #v[none, some (154 : Rat), some (154 : Rat)] [(309 / 2 : Rat)] (112500 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none, none] [(353 / 2 : Rat)] (106250 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none, none] [] (0 : Int)], [datedRead (198 : Rat) #v[none, some (198 : Rat), some (198 : Rat)] [] (0 : Int), datedRead (198 : Rat) #v[none, some (198 : Rat), some (198 : Rat)] [(397 / 2 : Rat)] (112500 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none, none] [(441 / 2 : Rat)] (106250 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none, none] [] (0 : Int)], [datedRead (242 : Rat) #v[none, some (242 : Rat), some (242 : Rat)] [] (0 : Int), datedRead (242 : Rat) #v[none, some (242 : Rat), some (242 : Rat)] [(485 / 2 : Rat)] (112500 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none, none] [(529 / 2 : Rat)] (106250 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none, none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat), some (286 : Rat)] [] (0 : Int), datedRead (286 : Rat) #v[none, some (286 : Rat), some (286 : Rat)] [(573 / 2 : Rat)] (112500 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none, none] [(617 / 2 : Rat)] (106250 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none, none] [] (0 : Int)], [datedRead (330 : Rat) #v[none, some (330 : Rat), some (330 : Rat)] [] (0 : Int), datedRead (330 : Rat) #v[none, some (330 : Rat), some (330 : Rat)] [(661 / 2 : Rat)] (112500 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none, none] [(705 / 2 : Rat)] (106250 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (0 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat), some (374 : Rat)] [] (0 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat), some (374 : Rat)] [(749 / 2 : Rat)] (112500 : Int)]]
private def trace_Syn_F3_K0_st : List (ReadObservation 2) := [datedRead (134 : Rat) #v[some (134 : Rat), none] [] (50000 : Int), datedRead (156 : Rat) #v[none, some (156 : Rat)] [] (50000 : Int), datedRead (178 : Rat) #v[some (178 : Rat), none] [] (70000 : Int), datedRead (200 : Rat) #v[none, some (200 : Rat)] [] (70000 : Int), datedRead (222 : Rat) #v[some (222 : Rat), none] [] (90000 : Int), datedRead (244 : Rat) #v[none, some (244 : Rat)] [] (90000 : Int), datedRead (266 : Rat) #v[some (266 : Rat), none] [(533 / 2 : Rat)] (110000 : Int), datedRead (288 : Rat) #v[none, some (288 : Rat)] [(577 / 2 : Rat)] (110000 : Int), datedRead (310 : Rat) #v[some (310 : Rat), none] [(621 / 2 : Rat)] (110000 : Int), datedRead (332 : Rat) #v[none, some (332 : Rat)] [(665 / 2 : Rat)] (110000 : Int), datedRead (354 : Rat) #v[some (354 : Rat), none] [(709 / 2 : Rat)] (110000 : Int), datedRead (376 : Rat) #v[none, some (376 : Rat)] [(753 / 2 : Rat)] (110000 : Int)]
private def trace_Syn_F3_K0_fx : List (List (ReadObservation 3)) := [[datedRead (396 : Rat) #v[none, none, none] [] (0 : Int), datedRead (396 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (484 : Rat) #v[none, none, some (484 : Rat)] [] (0 : Int), datedRead (484 : Rat) #v[none, none, some (484 : Rat)] [] (56250 : Int)], [datedRead (440 : Rat) #v[none, some (440 : Rat), none] [] (0 : Int), datedRead (440 : Rat) #v[none, some (440 : Rat), none] [] (56250 : Int)], [datedRead (528 : Rat) #v[none, some (528 : Rat), some (528 : Rat)] [] (0 : Int), datedRead (528 : Rat) #v[none, some (528 : Rat), some (528 : Rat)] [(1057 / 2 : Rat)] (112500 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), none, none] [(837 / 2 : Rat)] (106250 : Int), datedRead (418 : Rat) #v[some (418 : Rat), none, none] [] (0 : Int)], [datedRead (506 : Rat) #v[some (506 : Rat), none, some (506 : Rat)] [(1013 / 2 : Rat)] (106250 : Int), datedRead (506 : Rat) #v[some (506 : Rat), none, some (506 : Rat)] [] (56250 : Int)], [datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat), none] [(925 / 2 : Rat)] (106250 : Int), datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat), none] [] (56250 : Int)], [datedRead (550 : Rat) #v[some (550 : Rat), some (550 : Rat), some (550 : Rat)] [(1101 / 2 : Rat)] (106250 : Int), datedRead (550 : Rat) #v[some (550 : Rat), some (550 : Rat), some (550 : Rat)] [(1101 / 2 : Rat)] (112500 : Int)]]
private def trace_Syn_F3_K0_sx : List (ReadObservation 2) := [datedRead (795 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (971 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (883 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (530 : Rat) #v[none, some (530 : Rat)] [(1061 / 2 : Rat)] (110000 : Int), datedRead (420 : Rat) #v[some (420 : Rat), none] [(841 / 2 : Rat)] (110000 : Int), datedRead (508 : Rat) #v[some (508 : Rat), none] [(1017 / 2 : Rat)] (110000 : Int), datedRead (464 : Rat) #v[some (464 : Rat), none] [(929 / 2 : Rat)] (110000 : Int), datedRead (552 : Rat) #v[some (552 : Rat), some (552 : Rat)] [(1105 / 2 : Rat)] (220000 : Int)]
private def trace_Syn_F3_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)]]

def trace_Syn_F3_K0 : TraceTables cascade_Syn_F3_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_Syn_F3_K0_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_Syn_F3_K0_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_Syn_F3_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_Syn_F3_K0_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_Syn_F3_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_Syn_F3_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_Syn_F3_K0 : checks cascade_Syn_F3_K0 trace_Syn_F3_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Syn_F3_K0 : checkCascadeValid cascade_Syn_F3_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Syn_F3_K0 : checkTrainingSeparation cascade_Syn_F3_K0 left right trace_Syn_F3_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Syn_F3_K0 : checkCascadeCalibrationOneSided cascade_Syn_F3_K0 left right trace_Syn_F3_K0.observations trace_Syn_F3_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_Syn_F3_K0 : ∀ x i, (trace_Syn_F3_K0.observations.secondTest x i).fired = output cascade_Syn_F3_K0 i x := by
  have checked := checks_Syn_F3_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_Syn_F3_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_Syn_F3_K0.observations trace_Syn_F3_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_Syn_F3_K3 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[68750, 0, 0], #v[0, 18750, 18750]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[2793, 5536] : Vector Nat 2).get a,
    testingError := fun a => (#v[2793, 5536] : Vector Nat 2).get a,
    dose := 12500, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[50000, 50000] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 4439, testingError := fun _ => 4439,
    dose := 20000, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_Syn_F3_K3_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none, none] [] (68750 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat), some (0 : Rat)] [] (37500 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none, none] [] (81250 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat), some (22 : Rat)] [] (62500 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none, none] [] (93750 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat), some (44 : Rat)] [] (87500 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none, none] [(133 / 2 : Rat)] (106250 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat), some (66 : Rat)] [(133 / 2 : Rat)] (112500 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none, none] [(177 / 2 : Rat)] (106250 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat), some (88 : Rat)] [(177 / 2 : Rat)] (112500 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), none, none] [(221 / 2 : Rat)] (106250 : Int), datedRead (110 : Rat) #v[none, some (110 : Rat), some (110 : Rat)] [(221 / 2 : Rat)] (112500 : Int)]]
private def trace_Syn_F3_K3_te : List (List (ReadObservation 3)) := [[datedRead (132 : Rat) #v[some (132 : Rat), none, none] [(265 / 2 : Rat)] (106250 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none, none] [] (0 : Int)], [datedRead (154 : Rat) #v[none, some (154 : Rat), some (154 : Rat)] [] (0 : Int), datedRead (154 : Rat) #v[none, some (154 : Rat), some (154 : Rat)] [(309 / 2 : Rat)] (112500 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none, none] [(353 / 2 : Rat)] (106250 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none, none] [] (0 : Int)], [datedRead (198 : Rat) #v[none, some (198 : Rat), some (198 : Rat)] [] (0 : Int), datedRead (198 : Rat) #v[none, some (198 : Rat), some (198 : Rat)] [(397 / 2 : Rat)] (112500 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none, none] [(441 / 2 : Rat)] (106250 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none, none] [] (0 : Int)], [datedRead (242 : Rat) #v[none, some (242 : Rat), some (242 : Rat)] [] (0 : Int), datedRead (242 : Rat) #v[none, some (242 : Rat), some (242 : Rat)] [(485 / 2 : Rat)] (112500 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none, none] [(529 / 2 : Rat)] (106250 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none, none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat), some (286 : Rat)] [] (0 : Int), datedRead (286 : Rat) #v[none, some (286 : Rat), some (286 : Rat)] [(573 / 2 : Rat)] (112500 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none, none] [(617 / 2 : Rat)] (106250 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none, none] [] (0 : Int)], [datedRead (330 : Rat) #v[none, some (330 : Rat), some (330 : Rat)] [] (0 : Int), datedRead (330 : Rat) #v[none, some (330 : Rat), some (330 : Rat)] [(661 / 2 : Rat)] (112500 : Int)], [datedRead (352 : Rat) #v[some (352 : Rat), none, none] [(705 / 2 : Rat)] (106250 : Int), datedRead (352 : Rat) #v[some (352 : Rat), none, none] [] (0 : Int)], [datedRead (374 : Rat) #v[none, some (374 : Rat), some (374 : Rat)] [] (0 : Int), datedRead (374 : Rat) #v[none, some (374 : Rat), some (374 : Rat)] [(749 / 2 : Rat)] (112500 : Int)]]
private def trace_Syn_F3_K3_st : List (ReadObservation 2) := [datedRead (134 : Rat) #v[some (134 : Rat), none] [] (50000 : Int), datedRead (156 : Rat) #v[none, some (156 : Rat)] [] (50000 : Int), datedRead (178 : Rat) #v[some (178 : Rat), none] [] (70000 : Int), datedRead (200 : Rat) #v[none, some (200 : Rat)] [] (70000 : Int), datedRead (222 : Rat) #v[some (222 : Rat), none] [] (90000 : Int), datedRead (244 : Rat) #v[none, some (244 : Rat)] [] (90000 : Int), datedRead (266 : Rat) #v[some (266 : Rat), none] [(533 / 2 : Rat)] (110000 : Int), datedRead (288 : Rat) #v[none, some (288 : Rat)] [(577 / 2 : Rat)] (110000 : Int), datedRead (310 : Rat) #v[some (310 : Rat), none] [(621 / 2 : Rat)] (110000 : Int), datedRead (332 : Rat) #v[none, some (332 : Rat)] [(665 / 2 : Rat)] (110000 : Int), datedRead (354 : Rat) #v[some (354 : Rat), none] [(709 / 2 : Rat)] (110000 : Int), datedRead (376 : Rat) #v[none, some (376 : Rat)] [(753 / 2 : Rat)] (110000 : Int)]
private def trace_Syn_F3_K3_fx : List (List (ReadObservation 3)) := [[datedRead (396 : Rat) #v[none, none, none] [] (0 : Int), datedRead (396 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (484 : Rat) #v[none, none, some (484 : Rat)] [] (0 : Int), datedRead (484 : Rat) #v[none, none, some (484 : Rat)] [] (56250 : Int)], [datedRead (440 : Rat) #v[none, some (440 : Rat), none] [] (0 : Int), datedRead (440 : Rat) #v[none, some (440 : Rat), none] [] (56250 : Int)], [datedRead (528 : Rat) #v[none, some (528 : Rat), some (528 : Rat)] [] (0 : Int), datedRead (528 : Rat) #v[none, some (528 : Rat), some (528 : Rat)] [(1057 / 2 : Rat)] (112500 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), none, none] [(837 / 2 : Rat)] (106250 : Int), datedRead (418 : Rat) #v[some (418 : Rat), none, none] [] (0 : Int)], [datedRead (506 : Rat) #v[some (506 : Rat), none, some (506 : Rat)] [(1013 / 2 : Rat)] (106250 : Int), datedRead (506 : Rat) #v[some (506 : Rat), none, some (506 : Rat)] [] (56250 : Int)], [datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat), none] [(925 / 2 : Rat)] (106250 : Int), datedRead (462 : Rat) #v[some (462 : Rat), some (462 : Rat), none] [] (56250 : Int)], [datedRead (550 : Rat) #v[some (550 : Rat), some (550 : Rat), some (550 : Rat)] [(1101 / 2 : Rat)] (106250 : Int), datedRead (550 : Rat) #v[some (550 : Rat), some (550 : Rat), some (550 : Rat)] [(1101 / 2 : Rat)] (112500 : Int)]]
private def trace_Syn_F3_K3_sx : List (ReadObservation 2) := [datedRead (795 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (971 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (883 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (530 : Rat) #v[none, some (530 : Rat)] [(1061 / 2 : Rat)] (110000 : Int), datedRead (420 : Rat) #v[some (420 : Rat), none] [(841 / 2 : Rat)] (110000 : Int), datedRead (508 : Rat) #v[some (508 : Rat), none] [(1017 / 2 : Rat)] (110000 : Int), datedRead (464 : Rat) #v[some (464 : Rat), none] [(929 / 2 : Rat)] (110000 : Int), datedRead (552 : Rat) #v[some (552 : Rat), some (552 : Rat)] [(1105 / 2 : Rat)] (220000 : Int)]
private def trace_Syn_F3_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)], #v[(0 : Int), (110000 : Int), (110000 : Int), (220000 : Int)]]

def trace_Syn_F3_K3 : TraceTables cascade_Syn_F3_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_Syn_F3_K3_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_Syn_F3_K3_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_Syn_F3_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_Syn_F3_K3_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_Syn_F3_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_Syn_F3_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_Syn_F3_K3 : checks cascade_Syn_F3_K3 trace_Syn_F3_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Syn_F3_K3 : checkCascadeValid cascade_Syn_F3_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Syn_F3_K3 : checkTrainingSeparation cascade_Syn_F3_K3 left right trace_Syn_F3_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Syn_F3_K3 : checkCascadeCalibrationOneSided cascade_Syn_F3_K3 left right trace_Syn_F3_K3.observations trace_Syn_F3_K3.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_Syn_F3_K3 : ∀ x i, (trace_Syn_F3_K3.observations.secondTest x i).fired = output cascade_Syn_F3_K3 i x := by
  have checked := checks_Syn_F3_K3
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_Syn_F3_K3
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_Syn_F3_K3.observations trace_Syn_F3_K3.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
