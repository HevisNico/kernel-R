import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F3, instance 8511.
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

def cascade_F3_8511_K0 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[81543, 0, 0], #v[0, 38183, 38183]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[106, 205] : Vector Nat 2).get a,
    testingError := fun a => (#v[106, 205] : Vector Nat 2).get a,
    dose := 7725, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[41554, 58452] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 473, testingError := fun _ => 473,
    dose := 35747, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F3_8511_K0_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none, none] [] (81543 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat), some (0 : Rat)] [] (76364 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none, none] [] (89269 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat), some (22 : Rat)] [] (91816 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none, none] [] (96994 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat), some (44 : Rat)] [(44837 / 1000 : Rat)] (107268 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none, none] [(668051 / 10000 : Rat)] (104718 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat), some (66 : Rat)] [(66837 / 1000 : Rat)] (107268 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none, none] [(888051 / 10000 : Rat)] (104718 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat), some (88 : Rat)] [(88837 / 1000 : Rat)] (107268 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), none, none] [(1108051 / 10000 : Rat)] (104718 : Int), datedRead (110 : Rat) #v[none, some (110 : Rat), some (110 : Rat)] [(110837 / 1000 : Rat)] (107268 : Int)]]
private def trace_F3_8511_K0_te : List (List (ReadObservation 3)) := [[datedRead (132 : Rat) #v[some (132 : Rat), none, none] [(1328051 / 10000 : Rat)] (104718 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none, none] [] (0 : Int)], [datedRead (154 : Rat) #v[none, some (154 : Rat), some (154 : Rat)] [] (0 : Int), datedRead (154 : Rat) #v[none, some (154 : Rat), some (154 : Rat)] [(154837 / 1000 : Rat)] (107268 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none, none] [(1768051 / 10000 : Rat)] (104718 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none, none] [] (0 : Int)], [datedRead (198 : Rat) #v[none, some (198 : Rat), some (198 : Rat)] [] (0 : Int), datedRead (198 : Rat) #v[none, some (198 : Rat), some (198 : Rat)] [(198837 / 1000 : Rat)] (107268 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none, none] [(2208051 / 10000 : Rat)] (104718 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none, none] [] (0 : Int)], [datedRead (242 : Rat) #v[none, some (242 : Rat), some (242 : Rat)] [] (0 : Int), datedRead (242 : Rat) #v[none, some (242 : Rat), some (242 : Rat)] [(242837 / 1000 : Rat)] (107268 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none, none] [(2648051 / 10000 : Rat)] (104718 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none, none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat), some (286 : Rat)] [] (0 : Int), datedRead (286 : Rat) #v[none, some (286 : Rat), some (286 : Rat)] [(286837 / 1000 : Rat)] (107268 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none, none] [(3088051 / 10000 : Rat)] (104718 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none, none] [] (0 : Int)], [datedRead (330 : Rat) #v[none, some (330 : Rat), some (330 : Rat)] [] (0 : Int), datedRead (330 : Rat) #v[none, some (330 : Rat), some (330 : Rat)] [(330837 / 1000 : Rat)] (107268 : Int)]]
private def trace_F3_8511_K0_st : List (ReadObservation 2) := [datedRead (1343051 / 10000 : Rat) #v[some (1343051 / 10000 : Rat), none] [] (41551 : Int), datedRead (156337 / 1000 : Rat) #v[none, some (156337 / 1000 : Rat)] [] (58450 : Int), datedRead (1783051 / 10000 : Rat) #v[some (1783051 / 10000 : Rat), none] [] (77303 : Int), datedRead (200337 / 1000 : Rat) #v[none, some (200337 / 1000 : Rat)] [] (94201 : Int), datedRead (2223051 / 10000 : Rat) #v[some (2223051 / 10000 : Rat), none] [(22317 / 100 : Rat)] (113052 : Int), datedRead (244337 / 1000 : Rat) #v[none, some (244337 / 1000 : Rat)] [(1225491 / 5000 : Rat)] (129950 : Int), datedRead (2663051 / 10000 : Rat) #v[some (2663051 / 10000 : Rat), none] [(26717 / 100 : Rat)] (113052 : Int), datedRead (288337 / 1000 : Rat) #v[none, some (288337 / 1000 : Rat)] [(1445491 / 5000 : Rat)] (129950 : Int), datedRead (3103051 / 10000 : Rat) #v[some (3103051 / 10000 : Rat), none] [(31117 / 100 : Rat)] (113052 : Int), datedRead (332337 / 1000 : Rat) #v[none, some (332337 / 1000 : Rat)] [(1665491 / 5000 : Rat)] (129950 : Int)]
private def trace_F3_8511_K0_fx : List (List (ReadObservation 3)) := [[datedRead (352 : Rat) #v[none, none, none] [] (0 : Int), datedRead (352 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (440 : Rat) #v[none, none, some (440 : Rat)] [] (0 : Int), datedRead (440 : Rat) #v[none, none, some (440 : Rat)] [] (53634 : Int)], [datedRead (396 : Rat) #v[none, some (396 : Rat), none] [] (0 : Int), datedRead (396 : Rat) #v[none, some (396 : Rat), none] [] (53635 : Int)], [datedRead (484 : Rat) #v[none, some (484 : Rat), some (484 : Rat)] [] (0 : Int), datedRead (484 : Rat) #v[none, some (484 : Rat), some (484 : Rat)] [(484837 / 1000 : Rat)] (107268 : Int)], [datedRead (374 : Rat) #v[some (374 : Rat), none, none] [(3748051 / 10000 : Rat)] (104718 : Int), datedRead (374 : Rat) #v[some (374 : Rat), none, none] [] (0 : Int)], [datedRead (462 : Rat) #v[some (462 : Rat), none, some (462 : Rat)] [(4628051 / 10000 : Rat)] (104718 : Int), datedRead (462 : Rat) #v[some (462 : Rat), none, some (462 : Rat)] [] (53634 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat), none] [(4188051 / 10000 : Rat)] (104718 : Int), datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat), none] [] (53635 : Int)], [datedRead (506 : Rat) #v[some (506 : Rat), some (506 : Rat), some (506 : Rat)] [(5068051 / 10000 : Rat)] (104718 : Int), datedRead (506 : Rat) #v[some (506 : Rat), some (506 : Rat), some (506 : Rat)] [(506837 / 1000 : Rat)] (107268 : Int)]]
private def trace_F3_8511_K0_sx : List (ReadObservation 2) := [datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (883 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (795 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (486337 / 1000 : Rat) #v[none, some (486337 / 1000 : Rat)] [(2435491 / 5000 : Rat)] (129950 : Int), datedRead (3763051 / 10000 : Rat) #v[some (3763051 / 10000 : Rat), none] [(37717 / 100 : Rat)] (113052 : Int), datedRead (4643051 / 10000 : Rat) #v[some (4643051 / 10000 : Rat), none] [(46517 / 100 : Rat)] (113052 : Int), datedRead (4203051 / 10000 : Rat) #v[some (4203051 / 10000 : Rat), none] [(42117 / 100 : Rat)] (113052 : Int), datedRead (5083051 / 10000 : Rat) #v[some (5083051 / 10000 : Rat), some (508337 / 1000 : Rat)] [(635703 / 1250 : Rat)] (242996 : Int)]
private def trace_F3_8511_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)]]

def trace_F3_8511_K0 : TraceTables cascade_F3_8511_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F3_8511_K0_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F3_8511_K0_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F3_8511_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F3_8511_K0_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8511_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8511_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F3_8511_K0 : checks cascade_F3_8511_K0 trace_F3_8511_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F3_8511_K0 : checkCascadeValid cascade_F3_8511_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F3_8511_K0 : checkTrainingSeparation cascade_F3_8511_K0 left right trace_F3_8511_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F3_8511_K0 : checkCascadeCalibrationOneSided cascade_F3_8511_K0 left right trace_F3_8511_K0.observations trace_F3_8511_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F3_8511_K0 : ∀ x i, (trace_F3_8511_K0.observations.secondTest x i).fired = output cascade_F3_8511_K0 i x := by
  have checked := checks_F3_8511_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_F3_8511_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F3_8511_K0.observations trace_F3_8511_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F3_8511_K3 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[81543, 0, 0], #v[0, 38183, 38183]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[1274, 2533] : Vector Nat 2).get a,
    testingError := fun a => (#v[1274, 2533] : Vector Nat 2).get a,
    dose := 7725, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[41554, 58452] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 5889, testingError := fun _ => 5889,
    dose := 35747, maxWrites := 4, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F3_8511_K3_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none, none] [] (81543 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat), some (0 : Rat)] [] (76364 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none, none] [] (89269 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat), some (22 : Rat)] [] (91816 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none, none] [] (96994 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat), some (44 : Rat)] [(44837 / 1000 : Rat)] (107268 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none, none] [(668051 / 10000 : Rat)] (104718 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat), some (66 : Rat)] [(66837 / 1000 : Rat)] (107268 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none, none] [(888051 / 10000 : Rat)] (104718 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat), some (88 : Rat)] [(88837 / 1000 : Rat)] (107268 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat), none, none] [(1108051 / 10000 : Rat)] (104718 : Int), datedRead (110 : Rat) #v[none, some (110 : Rat), some (110 : Rat)] [(110837 / 1000 : Rat)] (107268 : Int)]]
private def trace_F3_8511_K3_te : List (List (ReadObservation 3)) := [[datedRead (132 : Rat) #v[some (132 : Rat), none, none] [(1328051 / 10000 : Rat)] (104718 : Int), datedRead (132 : Rat) #v[some (132 : Rat), none, none] [] (0 : Int)], [datedRead (154 : Rat) #v[none, some (154 : Rat), some (154 : Rat)] [] (0 : Int), datedRead (154 : Rat) #v[none, some (154 : Rat), some (154 : Rat)] [(154837 / 1000 : Rat)] (107268 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat), none, none] [(1768051 / 10000 : Rat)] (104718 : Int), datedRead (176 : Rat) #v[some (176 : Rat), none, none] [] (0 : Int)], [datedRead (198 : Rat) #v[none, some (198 : Rat), some (198 : Rat)] [] (0 : Int), datedRead (198 : Rat) #v[none, some (198 : Rat), some (198 : Rat)] [(198837 / 1000 : Rat)] (107268 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat), none, none] [(2208051 / 10000 : Rat)] (104718 : Int), datedRead (220 : Rat) #v[some (220 : Rat), none, none] [] (0 : Int)], [datedRead (242 : Rat) #v[none, some (242 : Rat), some (242 : Rat)] [] (0 : Int), datedRead (242 : Rat) #v[none, some (242 : Rat), some (242 : Rat)] [(242837 / 1000 : Rat)] (107268 : Int)], [datedRead (264 : Rat) #v[some (264 : Rat), none, none] [(2648051 / 10000 : Rat)] (104718 : Int), datedRead (264 : Rat) #v[some (264 : Rat), none, none] [] (0 : Int)], [datedRead (286 : Rat) #v[none, some (286 : Rat), some (286 : Rat)] [] (0 : Int), datedRead (286 : Rat) #v[none, some (286 : Rat), some (286 : Rat)] [(286837 / 1000 : Rat)] (107268 : Int)], [datedRead (308 : Rat) #v[some (308 : Rat), none, none] [(3088051 / 10000 : Rat)] (104718 : Int), datedRead (308 : Rat) #v[some (308 : Rat), none, none] [] (0 : Int)], [datedRead (330 : Rat) #v[none, some (330 : Rat), some (330 : Rat)] [] (0 : Int), datedRead (330 : Rat) #v[none, some (330 : Rat), some (330 : Rat)] [(330837 / 1000 : Rat)] (107268 : Int)]]
private def trace_F3_8511_K3_st : List (ReadObservation 2) := [datedRead (1343051 / 10000 : Rat) #v[some (1343051 / 10000 : Rat), none] [] (41551 : Int), datedRead (156337 / 1000 : Rat) #v[none, some (156337 / 1000 : Rat)] [] (58450 : Int), datedRead (1783051 / 10000 : Rat) #v[some (1783051 / 10000 : Rat), none] [] (77303 : Int), datedRead (200337 / 1000 : Rat) #v[none, some (200337 / 1000 : Rat)] [] (94201 : Int), datedRead (2223051 / 10000 : Rat) #v[some (2223051 / 10000 : Rat), none] [(22317 / 100 : Rat)] (113052 : Int), datedRead (244337 / 1000 : Rat) #v[none, some (244337 / 1000 : Rat)] [(1225491 / 5000 : Rat)] (129950 : Int), datedRead (2663051 / 10000 : Rat) #v[some (2663051 / 10000 : Rat), none] [(26717 / 100 : Rat)] (113052 : Int), datedRead (288337 / 1000 : Rat) #v[none, some (288337 / 1000 : Rat)] [(1445491 / 5000 : Rat)] (129950 : Int), datedRead (3103051 / 10000 : Rat) #v[some (3103051 / 10000 : Rat), none] [(31117 / 100 : Rat)] (113052 : Int), datedRead (332337 / 1000 : Rat) #v[none, some (332337 / 1000 : Rat)] [(1665491 / 5000 : Rat)] (129950 : Int)]
private def trace_F3_8511_K3_fx : List (List (ReadObservation 3)) := [[datedRead (352 : Rat) #v[none, none, none] [] (0 : Int), datedRead (352 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (440 : Rat) #v[none, none, some (440 : Rat)] [] (0 : Int), datedRead (440 : Rat) #v[none, none, some (440 : Rat)] [] (53634 : Int)], [datedRead (396 : Rat) #v[none, some (396 : Rat), none] [] (0 : Int), datedRead (396 : Rat) #v[none, some (396 : Rat), none] [] (53635 : Int)], [datedRead (484 : Rat) #v[none, some (484 : Rat), some (484 : Rat)] [] (0 : Int), datedRead (484 : Rat) #v[none, some (484 : Rat), some (484 : Rat)] [(484837 / 1000 : Rat)] (107268 : Int)], [datedRead (374 : Rat) #v[some (374 : Rat), none, none] [(3748051 / 10000 : Rat)] (104718 : Int), datedRead (374 : Rat) #v[some (374 : Rat), none, none] [] (0 : Int)], [datedRead (462 : Rat) #v[some (462 : Rat), none, some (462 : Rat)] [(4628051 / 10000 : Rat)] (104718 : Int), datedRead (462 : Rat) #v[some (462 : Rat), none, some (462 : Rat)] [] (53634 : Int)], [datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat), none] [(4188051 / 10000 : Rat)] (104718 : Int), datedRead (418 : Rat) #v[some (418 : Rat), some (418 : Rat), none] [] (53635 : Int)], [datedRead (506 : Rat) #v[some (506 : Rat), some (506 : Rat), some (506 : Rat)] [(5068051 / 10000 : Rat)] (104718 : Int), datedRead (506 : Rat) #v[some (506 : Rat), some (506 : Rat), some (506 : Rat)] [(506837 / 1000 : Rat)] (107268 : Int)]]
private def trace_F3_8511_K3_sx : List (ReadObservation 2) := [datedRead (707 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (883 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (795 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (486337 / 1000 : Rat) #v[none, some (486337 / 1000 : Rat)] [(2435491 / 5000 : Rat)] (129950 : Int), datedRead (3763051 / 10000 : Rat) #v[some (3763051 / 10000 : Rat), none] [(37717 / 100 : Rat)] (113052 : Int), datedRead (4643051 / 10000 : Rat) #v[some (4643051 / 10000 : Rat), none] [(46517 / 100 : Rat)] (113052 : Int), datedRead (4203051 / 10000 : Rat) #v[some (4203051 / 10000 : Rat), none] [(42117 / 100 : Rat)] (113052 : Int), datedRead (5083051 / 10000 : Rat) #v[some (5083051 / 10000 : Rat), some (508337 / 1000 : Rat)] [(635703 / 1250 : Rat)] (242996 : Int)]
private def trace_F3_8511_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)], #v[(0 : Int), (129950 : Int), (113052 : Int), (242996 : Int)]]

def trace_F3_8511_K3 : TraceTables cascade_F3_8511_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F3_8511_K3_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F3_8511_K3_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F3_8511_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F3_8511_K3_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8511_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8511_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F3_8511_K3 : checks cascade_F3_8511_K3 trace_F3_8511_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F3_8511_K3 : checkCascadeValid cascade_F3_8511_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F3_8511_K3 : checkTrainingSeparation cascade_F3_8511_K3 left right trace_F3_8511_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F3_8511_K3 : checkCascadeCalibrationOneSided cascade_F3_8511_K3 left right trace_F3_8511_K3.observations trace_F3_8511_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
