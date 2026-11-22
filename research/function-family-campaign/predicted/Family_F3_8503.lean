import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F3, instance 8503.
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

def cascade_F3_8503_K0 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[90779, 0, 0], #v[0, 41904, 41903]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[97, 193] : Vector Nat 2).get a,
    testingError := fun a => (#v[97, 193] : Vector Nat 2).get a,
    dose := 7183, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[41582, 58425] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 328, testingError := fun _ => 328,
    dose := 24776, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F3_8503_K0_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none, none] [] (90780 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat), some (0 : Rat)] [] (83806 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none, none] [] (97964 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat), some (22 : Rat)] [] (98175 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none, none] [(447833 / 10000 : Rat)] (105147 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat), some (44 : Rat)] [(89507 / 2000 : Rat)] (112542 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none, none] [(667833 / 10000 : Rat)] (105147 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat), some (66 : Rat)] [(133507 / 2000 : Rat)] (112542 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none, none] [(887833 / 10000 : Rat)] (105147 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat), some (88 : Rat)] [(177507 / 2000 : Rat)] (112542 : Int)]]
private def trace_F3_8503_K0_te : List (List (ReadObservation 3)) := [[datedRead (110 : Rat) #v[some (110 : Rat), none, none] [(1107833 / 10000 : Rat)] (105147 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none, none] [] (0 : Int)], [datedRead (132 : Rat) #v[none, some (132 : Rat), some (132 : Rat)] [] (0 : Int), datedRead (132 : Rat) #v[none, some (132 : Rat), some (132 : Rat)] [(265507 / 2000 : Rat)] (112542 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none, none] [(1547833 / 10000 : Rat)] (105147 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none, none] [] (0 : Int)], [datedRead (176 : Rat) #v[none, some (176 : Rat), some (176 : Rat)] [] (0 : Int), datedRead (176 : Rat) #v[none, some (176 : Rat), some (176 : Rat)] [(353507 / 2000 : Rat)] (112542 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none, none] [(1987833 / 10000 : Rat)] (105147 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none, none] [] (0 : Int)], [datedRead (220 : Rat) #v[none, some (220 : Rat), some (220 : Rat)] [] (0 : Int), datedRead (220 : Rat) #v[none, some (220 : Rat), some (220 : Rat)] [(441507 / 2000 : Rat)] (112542 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none, none] [(2427833 / 10000 : Rat)] (105147 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none, none] [] (0 : Int)], [datedRead (264 : Rat) #v[none, some (264 : Rat), some (264 : Rat)] [] (0 : Int), datedRead (264 : Rat) #v[none, some (264 : Rat), some (264 : Rat)] [(529507 / 2000 : Rat)] (112542 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none, none] [(2867833 / 10000 : Rat)] (105147 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none, none] [] (0 : Int)], [datedRead (308 : Rat) #v[none, some (308 : Rat), some (308 : Rat)] [] (0 : Int), datedRead (308 : Rat) #v[none, some (308 : Rat), some (308 : Rat)] [(617507 / 2000 : Rat)] (112542 : Int)], [datedRead (330 : Rat) #v[some (330 : Rat), none, none] [(3307833 / 10000 : Rat)] (105147 : Int), datedRead (330 : Rat) #v[some (330 : Rat), none, none] [] (0 : Int)], [datedRead (352 : Rat) #v[none, some (352 : Rat), some (352 : Rat)] [] (0 : Int), datedRead (352 : Rat) #v[none, some (352 : Rat), some (352 : Rat)] [(705507 / 2000 : Rat)] (112542 : Int)]]
private def trace_F3_8503_K0_st : List (ReadObservation 2) := [datedRead (1122833 / 10000 : Rat) #v[some (1122833 / 10000 : Rat), none] [] (41578 : Int), datedRead (268507 / 2000 : Rat) #v[none, some (268507 / 2000 : Rat)] [] (58422 : Int), datedRead (1562833 / 10000 : Rat) #v[some (1562833 / 10000 : Rat), none] [] (66359 : Int), datedRead (356507 / 2000 : Rat) #v[none, some (356507 / 2000 : Rat)] [] (83202 : Int), datedRead (2002833 / 10000 : Rat) #v[some (2002833 / 10000 : Rat), none] [] (91137 : Int), datedRead (444507 / 2000 : Rat) #v[none, some (444507 / 2000 : Rat)] [(2231303 / 10000 : Rat)] (107980 : Int), datedRead (2442833 / 10000 : Rat) #v[some (2442833 / 10000 : Rat), none] [(2450821 / 10000 : Rat)] (115914 : Int), datedRead (532507 / 2000 : Rat) #v[none, some (532507 / 2000 : Rat)] [(2671303 / 10000 : Rat)] (107980 : Int), datedRead (2882833 / 10000 : Rat) #v[some (2882833 / 10000 : Rat), none] [(2890821 / 10000 : Rat)] (115914 : Int), datedRead (620507 / 2000 : Rat) #v[none, some (620507 / 2000 : Rat)] [(3111303 / 10000 : Rat)] (107980 : Int), datedRead (3322833 / 10000 : Rat) #v[some (3322833 / 10000 : Rat), none] [(3330821 / 10000 : Rat)] (115914 : Int), datedRead (708507 / 2000 : Rat) #v[none, some (708507 / 2000 : Rat)] [(3551303 / 10000 : Rat)] (107980 : Int)]
private def trace_F3_8503_K0_fx : List (List (ReadObservation 3)) := [[datedRead (374 : Rat) #v[none, none, none] [] (0 : Int), datedRead (374 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (462 : Rat) #v[none, none, some (462 : Rat)] [] (0 : Int), datedRead (462 : Rat) #v[none, none, some (462 : Rat)] [] (56271 : Int)], [datedRead (418 : Rat) #v[none, some (418 : Rat), none] [] (0 : Int), datedRead (418 : Rat) #v[none, some (418 : Rat), none] [] (56272 : Int)], [datedRead (506 : Rat) #v[none, some (506 : Rat), some (506 : Rat)] [] (0 : Int), datedRead (506 : Rat) #v[none, some (506 : Rat), some (506 : Rat)] [(1013507 / 2000 : Rat)] (112542 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), none, none] [(3967833 / 10000 : Rat)] (105147 : Int), datedRead (396 : Rat) #v[some (396 : Rat), none, none] [] (0 : Int)], [datedRead (484 : Rat) #v[some (484 : Rat), none, some (484 : Rat)] [(4847833 / 10000 : Rat)] (105147 : Int), datedRead (484 : Rat) #v[some (484 : Rat), none, some (484 : Rat)] [] (56271 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat), none] [(4407833 / 10000 : Rat)] (105147 : Int), datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat), none] [] (56272 : Int)], [datedRead (528 : Rat) #v[some (528 : Rat), some (528 : Rat), some (528 : Rat)] [(5287833 / 10000 : Rat)] (105147 : Int), datedRead (528 : Rat) #v[some (528 : Rat), some (528 : Rat), some (528 : Rat)] [(1057507 / 2000 : Rat)] (112542 : Int)]]
private def trace_F3_8503_K0_sx : List (ReadObservation 2) := [datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (927 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (1016507 / 2000 : Rat) #v[none, some (1016507 / 2000 : Rat)] [(5091303 / 10000 : Rat)] (107980 : Int), datedRead (3982833 / 10000 : Rat) #v[some (3982833 / 10000 : Rat), none] [(3990821 / 10000 : Rat)] (115914 : Int), datedRead (4862833 / 10000 : Rat) #v[some (4862833 / 10000 : Rat), none] [(4870821 / 10000 : Rat)] (115914 : Int), datedRead (4422833 / 10000 : Rat) #v[some (4422833 / 10000 : Rat), none] [(4430821 / 10000 : Rat)] (115914 : Int), datedRead (1060507 / 2000 : Rat) #v[some (5302833 / 10000 : Rat), some (1060507 / 2000 : Rat)] [(2652641 / 5000 : Rat)] (199113 : Int)]
private def trace_F3_8503_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)]]

def trace_F3_8503_K0 : TraceTables cascade_F3_8503_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F3_8503_K0_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F3_8503_K0_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F3_8503_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F3_8503_K0_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8503_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8503_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F3_8503_K0 : checks cascade_F3_8503_K0 trace_F3_8503_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F3_8503_K0 : checkCascadeValid cascade_F3_8503_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F3_8503_K0 : checkTrainingSeparation cascade_F3_8503_K0 left right trace_F3_8503_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F3_8503_K0 : checkCascadeCalibrationOneSided cascade_F3_8503_K0 left right trace_F3_8503_K0.observations trace_F3_8503_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F3_8503_K0 : ∀ x i, (trace_F3_8503_K0.observations.secondTest x i).fired = output cascade_F3_8503_K0 i x := by
  have checked := checks_F3_8503_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 3 cascade_F3_8503_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F3_8503_K0.observations trace_F3_8503_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F3_8503_K3 : Cascade 2 1 3 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[90779, 0, 0], #v[0, 41904, 41903]] : Vector (Vector Nat 3) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[1180, 2366] : Vector Nat 2).get a,
    testingError := fun a => (#v[1180, 2366] : Vector Nat 2).get a,
    dose := 7183, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[41582, 58425] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 4076, testingError := fun _ => 4076,
    dose := 24776, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F3_8503_K3_ft : List (List (ReadObservation 3)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none, none] [] (90780 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat), some (0 : Rat)] [] (83806 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none, none] [] (97964 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat), some (22 : Rat)] [] (98175 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none, none] [(447833 / 10000 : Rat)] (105147 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat), some (44 : Rat)] [(89507 / 2000 : Rat)] (112542 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none, none] [(667833 / 10000 : Rat)] (105147 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat), some (66 : Rat)] [(133507 / 2000 : Rat)] (112542 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none, none] [(887833 / 10000 : Rat)] (105147 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat), some (88 : Rat)] [(177507 / 2000 : Rat)] (112542 : Int)]]
private def trace_F3_8503_K3_te : List (List (ReadObservation 3)) := [[datedRead (110 : Rat) #v[some (110 : Rat), none, none] [(1107833 / 10000 : Rat)] (105147 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none, none] [] (0 : Int)], [datedRead (132 : Rat) #v[none, some (132 : Rat), some (132 : Rat)] [] (0 : Int), datedRead (132 : Rat) #v[none, some (132 : Rat), some (132 : Rat)] [(265507 / 2000 : Rat)] (112542 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none, none] [(1547833 / 10000 : Rat)] (105147 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none, none] [] (0 : Int)], [datedRead (176 : Rat) #v[none, some (176 : Rat), some (176 : Rat)] [] (0 : Int), datedRead (176 : Rat) #v[none, some (176 : Rat), some (176 : Rat)] [(353507 / 2000 : Rat)] (112542 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none, none] [(1987833 / 10000 : Rat)] (105147 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none, none] [] (0 : Int)], [datedRead (220 : Rat) #v[none, some (220 : Rat), some (220 : Rat)] [] (0 : Int), datedRead (220 : Rat) #v[none, some (220 : Rat), some (220 : Rat)] [(441507 / 2000 : Rat)] (112542 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none, none] [(2427833 / 10000 : Rat)] (105147 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none, none] [] (0 : Int)], [datedRead (264 : Rat) #v[none, some (264 : Rat), some (264 : Rat)] [] (0 : Int), datedRead (264 : Rat) #v[none, some (264 : Rat), some (264 : Rat)] [(529507 / 2000 : Rat)] (112542 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none, none] [(2867833 / 10000 : Rat)] (105147 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none, none] [] (0 : Int)], [datedRead (308 : Rat) #v[none, some (308 : Rat), some (308 : Rat)] [] (0 : Int), datedRead (308 : Rat) #v[none, some (308 : Rat), some (308 : Rat)] [(617507 / 2000 : Rat)] (112542 : Int)], [datedRead (330 : Rat) #v[some (330 : Rat), none, none] [(3307833 / 10000 : Rat)] (105147 : Int), datedRead (330 : Rat) #v[some (330 : Rat), none, none] [] (0 : Int)], [datedRead (352 : Rat) #v[none, some (352 : Rat), some (352 : Rat)] [] (0 : Int), datedRead (352 : Rat) #v[none, some (352 : Rat), some (352 : Rat)] [(705507 / 2000 : Rat)] (112542 : Int)]]
private def trace_F3_8503_K3_st : List (ReadObservation 2) := [datedRead (1122833 / 10000 : Rat) #v[some (1122833 / 10000 : Rat), none] [] (41578 : Int), datedRead (268507 / 2000 : Rat) #v[none, some (268507 / 2000 : Rat)] [] (58422 : Int), datedRead (1562833 / 10000 : Rat) #v[some (1562833 / 10000 : Rat), none] [] (66359 : Int), datedRead (356507 / 2000 : Rat) #v[none, some (356507 / 2000 : Rat)] [] (83202 : Int), datedRead (2002833 / 10000 : Rat) #v[some (2002833 / 10000 : Rat), none] [] (91137 : Int), datedRead (444507 / 2000 : Rat) #v[none, some (444507 / 2000 : Rat)] [(2231303 / 10000 : Rat)] (107980 : Int), datedRead (2442833 / 10000 : Rat) #v[some (2442833 / 10000 : Rat), none] [(2450821 / 10000 : Rat)] (115914 : Int), datedRead (532507 / 2000 : Rat) #v[none, some (532507 / 2000 : Rat)] [(2671303 / 10000 : Rat)] (107980 : Int), datedRead (2882833 / 10000 : Rat) #v[some (2882833 / 10000 : Rat), none] [(2890821 / 10000 : Rat)] (115914 : Int), datedRead (620507 / 2000 : Rat) #v[none, some (620507 / 2000 : Rat)] [(3111303 / 10000 : Rat)] (107980 : Int), datedRead (3322833 / 10000 : Rat) #v[some (3322833 / 10000 : Rat), none] [(3330821 / 10000 : Rat)] (115914 : Int), datedRead (708507 / 2000 : Rat) #v[none, some (708507 / 2000 : Rat)] [(3551303 / 10000 : Rat)] (107980 : Int)]
private def trace_F3_8503_K3_fx : List (List (ReadObservation 3)) := [[datedRead (374 : Rat) #v[none, none, none] [] (0 : Int), datedRead (374 : Rat) #v[none, none, none] [] (0 : Int)], [datedRead (462 : Rat) #v[none, none, some (462 : Rat)] [] (0 : Int), datedRead (462 : Rat) #v[none, none, some (462 : Rat)] [] (56271 : Int)], [datedRead (418 : Rat) #v[none, some (418 : Rat), none] [] (0 : Int), datedRead (418 : Rat) #v[none, some (418 : Rat), none] [] (56272 : Int)], [datedRead (506 : Rat) #v[none, some (506 : Rat), some (506 : Rat)] [] (0 : Int), datedRead (506 : Rat) #v[none, some (506 : Rat), some (506 : Rat)] [(1013507 / 2000 : Rat)] (112542 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), none, none] [(3967833 / 10000 : Rat)] (105147 : Int), datedRead (396 : Rat) #v[some (396 : Rat), none, none] [] (0 : Int)], [datedRead (484 : Rat) #v[some (484 : Rat), none, some (484 : Rat)] [(4847833 / 10000 : Rat)] (105147 : Int), datedRead (484 : Rat) #v[some (484 : Rat), none, some (484 : Rat)] [] (56271 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat), none] [(4407833 / 10000 : Rat)] (105147 : Int), datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat), none] [] (56272 : Int)], [datedRead (528 : Rat) #v[some (528 : Rat), some (528 : Rat), some (528 : Rat)] [(5287833 / 10000 : Rat)] (105147 : Int), datedRead (528 : Rat) #v[some (528 : Rat), some (528 : Rat), some (528 : Rat)] [(1057507 / 2000 : Rat)] (112542 : Int)]]
private def trace_F3_8503_K3_sx : List (ReadObservation 2) := [datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (927 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (839 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (1016507 / 2000 : Rat) #v[none, some (1016507 / 2000 : Rat)] [(5091303 / 10000 : Rat)] (107980 : Int), datedRead (3982833 / 10000 : Rat) #v[some (3982833 / 10000 : Rat), none] [(3990821 / 10000 : Rat)] (115914 : Int), datedRead (4862833 / 10000 : Rat) #v[some (4862833 / 10000 : Rat), none] [(4870821 / 10000 : Rat)] (115914 : Int), datedRead (4422833 / 10000 : Rat) #v[some (4422833 / 10000 : Rat), none] [(4430821 / 10000 : Rat)] (115914 : Int), datedRead (1060507 / 2000 : Rat) #v[some (5302833 / 10000 : Rat), some (1060507 / 2000 : Rat)] [(2652641 / 5000 : Rat)] (199113 : Int)]
private def trace_F3_8503_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)], #v[(0 : Int), (107980 : Int), (115914 : Int), (199113 : Int)]]

def trace_F3_8503_K3 : TraceTables cascade_F3_8503_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F3_8503_K3_ft.getD r.val []).getD a.val empty3
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F3_8503_K3_te.getD n.val []).getD a.val empty3
  secondTrain := Vector.ofFn fun n => trace_F3_8503_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F3_8503_K3_fx.getD w.val []).getD a.val empty3
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8503_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F3_8503_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F3_8503_K3 : checks cascade_F3_8503_K3 trace_F3_8503_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F3_8503_K3 : checkCascadeValid cascade_F3_8503_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F3_8503_K3 : checkTrainingSeparation cascade_F3_8503_K3 left right trace_F3_8503_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F3_8503_K3 : checkCascadeCalibrationOneSided cascade_F3_8503_K3 left right trace_F3_8503_K3.observations trace_F3_8503_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
