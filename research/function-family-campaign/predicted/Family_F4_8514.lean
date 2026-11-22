import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from family_predict.py, member F4, instance 8514.
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

def cascade_F4_8514_K0 : Cascade 2 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[87004, 0], #v[0, 87312]] : Vector (Vector Nat 2) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[107, 107] : Vector Nat 2).get a,
    testingError := fun a => (#v[107, 107] : Vector Nat 2).get a,
    dose := 7892, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[49539, 50470] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 316, testingError := fun _ => 316,
    dose := 23852, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F4_8514_K0_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none] [] (87003 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat)] [] (87311 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none] [] (94896 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat)] [] (95204 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none] [(112171 / 2500 : Rat)] (102788 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat)] [(448569 / 10000 : Rat)] (103096 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none] [(167171 / 2500 : Rat)] (102788 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat)] [(668569 / 10000 : Rat)] (103096 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none] [(222171 / 2500 : Rat)] (102788 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat)] [(888569 / 10000 : Rat)] (103096 : Int)]]
private def trace_F4_8514_K0_te : List (List (ReadObservation 2)) := [[datedRead (110 : Rat) #v[some (110 : Rat), none] [(277171 / 2500 : Rat)] (102788 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none] [] (0 : Int)], [datedRead (132 : Rat) #v[none, some (132 : Rat)] [] (0 : Int), datedRead (132 : Rat) #v[none, some (132 : Rat)] [(1328569 / 10000 : Rat)] (103096 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none] [(387171 / 2500 : Rat)] (102788 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none] [] (0 : Int)], [datedRead (176 : Rat) #v[none, some (176 : Rat)] [] (0 : Int), datedRead (176 : Rat) #v[none, some (176 : Rat)] [(1768569 / 10000 : Rat)] (103096 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none] [(497171 / 2500 : Rat)] (102788 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none] [] (0 : Int)], [datedRead (220 : Rat) #v[none, some (220 : Rat)] [] (0 : Int), datedRead (220 : Rat) #v[none, some (220 : Rat)] [(2208569 / 10000 : Rat)] (103096 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none] [(607171 / 2500 : Rat)] (102788 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none] [] (0 : Int)], [datedRead (264 : Rat) #v[none, some (264 : Rat)] [] (0 : Int), datedRead (264 : Rat) #v[none, some (264 : Rat)] [(2648569 / 10000 : Rat)] (103096 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none] [(717171 / 2500 : Rat)] (102788 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none] [] (0 : Int)], [datedRead (308 : Rat) #v[none, some (308 : Rat)] [] (0 : Int), datedRead (308 : Rat) #v[none, some (308 : Rat)] [(3088569 / 10000 : Rat)] (103096 : Int)], [datedRead (330 : Rat) #v[some (330 : Rat), none] [(827171 / 2500 : Rat)] (102788 : Int), datedRead (330 : Rat) #v[some (330 : Rat), none] [] (0 : Int)], [datedRead (352 : Rat) #v[none, some (352 : Rat)] [] (0 : Int), datedRead (352 : Rat) #v[none, some (352 : Rat)] [(3528569 / 10000 : Rat)] (103096 : Int)]]
private def trace_F4_8514_K0_st : List (ReadObservation 2) := [datedRead (280921 / 2500 : Rat) #v[some (280921 / 2500 : Rat), none] [] (49535 : Int), datedRead (1343569 / 10000 : Rat) #v[none, some (1343569 / 10000 : Rat)] [] (50467 : Int), datedRead (390921 / 2500 : Rat) #v[some (390921 / 2500 : Rat), none] [] (73392 : Int), datedRead (1783569 / 10000 : Rat) #v[none, some (1783569 / 10000 : Rat)] [] (74323 : Int), datedRead (500921 / 2500 : Rat) #v[some (500921 / 2500 : Rat), none] [] (97246 : Int), datedRead (2223569 / 10000 : Rat) #v[none, some (2223569 / 10000 : Rat)] [] (98178 : Int), datedRead (610921 / 2500 : Rat) #v[some (610921 / 2500 : Rat), none] [(6128 / 25 : Rat)] (121099 : Int), datedRead (2663569 / 10000 : Rat) #v[none, some (2663569 / 10000 : Rat)] [(2671021 / 10000 : Rat)] (122030 : Int), datedRead (720921 / 2500 : Rat) #v[some (720921 / 2500 : Rat), none] [(7228 / 25 : Rat)] (121099 : Int), datedRead (3103569 / 10000 : Rat) #v[none, some (3103569 / 10000 : Rat)] [(3111021 / 10000 : Rat)] (122030 : Int), datedRead (830921 / 2500 : Rat) #v[some (830921 / 2500 : Rat), none] [(8328 / 25 : Rat)] (121099 : Int), datedRead (3543569 / 10000 : Rat) #v[none, some (3543569 / 10000 : Rat)] [(3551021 / 10000 : Rat)] (122030 : Int)]
private def trace_F4_8514_K0_fx : List (List (ReadObservation 2)) := [[datedRead (374 : Rat) #v[none, none] [] (0 : Int), datedRead (374 : Rat) #v[none, none] [] (0 : Int)], [datedRead (418 : Rat) #v[none, some (418 : Rat)] [] (0 : Int), datedRead (418 : Rat) #v[none, some (418 : Rat)] [(4188569 / 10000 : Rat)] (103096 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), none] [(992171 / 2500 : Rat)] (102788 : Int), datedRead (396 : Rat) #v[some (396 : Rat), none] [] (0 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat)] [(1102171 / 2500 : Rat)] (102788 : Int), datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat)] [(4408569 / 10000 : Rat)] (103096 : Int)]]
private def trace_F4_8514_K0_sx : List (ReadObservation 2) := [datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (4203569 / 10000 : Rat) #v[none, some (4203569 / 10000 : Rat)] [(4211021 / 10000 : Rat)] (122030 : Int), datedRead (995921 / 2500 : Rat) #v[some (995921 / 2500 : Rat), none] [(9978 / 25 : Rat)] (121099 : Int), datedRead (4423569 / 10000 : Rat) #v[some (1105921 / 2500 : Rat), some (4423569 / 10000 : Rat)] [(276629 / 625 : Rat)] (243123 : Int)]
private def trace_F4_8514_K0_sc : List (Vector Int 4) := [#v[(0 : Int), (122030 : Int), (121099 : Int), (243123 : Int)], #v[(0 : Int), (122030 : Int), (121099 : Int), (243123 : Int)], #v[(0 : Int), (122030 : Int), (121099 : Int), (243123 : Int)], #v[(0 : Int), (122030 : Int), (121099 : Int), (243123 : Int)]]

def trace_F4_8514_K0 : TraceTables cascade_F4_8514_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F4_8514_K0_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F4_8514_K0_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_F4_8514_K0_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F4_8514_K0_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8514_K0_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8514_K0_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F4_8514_K0 : checks cascade_F4_8514_K0 trace_F4_8514_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F4_8514_K0 : checkCascadeValid cascade_F4_8514_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F4_8514_K0 : checkTrainingSeparation cascade_F4_8514_K0 left right trace_F4_8514_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F4_8514_K0 : checkCascadeCalibrationOneSided cascade_F4_8514_K0 left right trace_F4_8514_K0.observations trace_F4_8514_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_F4_8514_K0 : ∀ x i, (trace_F4_8514_K0.observations.secondTest x i).fired = output cascade_F4_8514_K0 i x := by
  have checked := checks_F4_8514_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 2 1 2 cascade_F4_8514_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_F4_8514_K0.observations trace_F4_8514_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_F4_8514_K3 : Cascade 2 1 2 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[87004, 0], #v[0, 87312]] : Vector (Vector Nat 2) 2).get a).get j,
    help := fun a => (#v[0, 0] : Vector Nat 2).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[1301, 1294] : Vector Nat 2).get a,
    testingError := fun a => (#v[1301, 1294] : Vector Nat 2).get a,
    dose := 7892, maxWrites := 4, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[49539, 50470] : Vector Nat 2).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 3923, testingError := fun _ => 3923,
    dose := 23852, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_F4_8514_K3_ft : List (List (ReadObservation 2)) := [[datedRead (0 : Rat) #v[some (0 : Rat), none] [] (87003 : Int), datedRead (0 : Rat) #v[none, some (0 : Rat)] [] (87311 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat), none] [] (94896 : Int), datedRead (22 : Rat) #v[none, some (22 : Rat)] [] (95204 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat), none] [(112171 / 2500 : Rat)] (102788 : Int), datedRead (44 : Rat) #v[none, some (44 : Rat)] [(448569 / 10000 : Rat)] (103096 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat), none] [(167171 / 2500 : Rat)] (102788 : Int), datedRead (66 : Rat) #v[none, some (66 : Rat)] [(668569 / 10000 : Rat)] (103096 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat), none] [(222171 / 2500 : Rat)] (102788 : Int), datedRead (88 : Rat) #v[none, some (88 : Rat)] [(888569 / 10000 : Rat)] (103096 : Int)]]
private def trace_F4_8514_K3_te : List (List (ReadObservation 2)) := [[datedRead (110 : Rat) #v[some (110 : Rat), none] [(277171 / 2500 : Rat)] (102788 : Int), datedRead (110 : Rat) #v[some (110 : Rat), none] [] (0 : Int)], [datedRead (132 : Rat) #v[none, some (132 : Rat)] [] (0 : Int), datedRead (132 : Rat) #v[none, some (132 : Rat)] [(1328569 / 10000 : Rat)] (103096 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat), none] [(387171 / 2500 : Rat)] (102788 : Int), datedRead (154 : Rat) #v[some (154 : Rat), none] [] (0 : Int)], [datedRead (176 : Rat) #v[none, some (176 : Rat)] [] (0 : Int), datedRead (176 : Rat) #v[none, some (176 : Rat)] [(1768569 / 10000 : Rat)] (103096 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat), none] [(497171 / 2500 : Rat)] (102788 : Int), datedRead (198 : Rat) #v[some (198 : Rat), none] [] (0 : Int)], [datedRead (220 : Rat) #v[none, some (220 : Rat)] [] (0 : Int), datedRead (220 : Rat) #v[none, some (220 : Rat)] [(2208569 / 10000 : Rat)] (103096 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat), none] [(607171 / 2500 : Rat)] (102788 : Int), datedRead (242 : Rat) #v[some (242 : Rat), none] [] (0 : Int)], [datedRead (264 : Rat) #v[none, some (264 : Rat)] [] (0 : Int), datedRead (264 : Rat) #v[none, some (264 : Rat)] [(2648569 / 10000 : Rat)] (103096 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat), none] [(717171 / 2500 : Rat)] (102788 : Int), datedRead (286 : Rat) #v[some (286 : Rat), none] [] (0 : Int)], [datedRead (308 : Rat) #v[none, some (308 : Rat)] [] (0 : Int), datedRead (308 : Rat) #v[none, some (308 : Rat)] [(3088569 / 10000 : Rat)] (103096 : Int)], [datedRead (330 : Rat) #v[some (330 : Rat), none] [(827171 / 2500 : Rat)] (102788 : Int), datedRead (330 : Rat) #v[some (330 : Rat), none] [] (0 : Int)], [datedRead (352 : Rat) #v[none, some (352 : Rat)] [] (0 : Int), datedRead (352 : Rat) #v[none, some (352 : Rat)] [(3528569 / 10000 : Rat)] (103096 : Int)]]
private def trace_F4_8514_K3_st : List (ReadObservation 2) := [datedRead (280921 / 2500 : Rat) #v[some (280921 / 2500 : Rat), none] [] (49535 : Int), datedRead (1343569 / 10000 : Rat) #v[none, some (1343569 / 10000 : Rat)] [] (50467 : Int), datedRead (390921 / 2500 : Rat) #v[some (390921 / 2500 : Rat), none] [] (73392 : Int), datedRead (1783569 / 10000 : Rat) #v[none, some (1783569 / 10000 : Rat)] [] (74323 : Int), datedRead (500921 / 2500 : Rat) #v[some (500921 / 2500 : Rat), none] [] (97246 : Int), datedRead (2223569 / 10000 : Rat) #v[none, some (2223569 / 10000 : Rat)] [] (98178 : Int), datedRead (610921 / 2500 : Rat) #v[some (610921 / 2500 : Rat), none] [(6128 / 25 : Rat)] (121099 : Int), datedRead (2663569 / 10000 : Rat) #v[none, some (2663569 / 10000 : Rat)] [(2671021 / 10000 : Rat)] (122030 : Int), datedRead (720921 / 2500 : Rat) #v[some (720921 / 2500 : Rat), none] [(7228 / 25 : Rat)] (121099 : Int), datedRead (3103569 / 10000 : Rat) #v[none, some (3103569 / 10000 : Rat)] [(3111021 / 10000 : Rat)] (122030 : Int), datedRead (830921 / 2500 : Rat) #v[some (830921 / 2500 : Rat), none] [(8328 / 25 : Rat)] (121099 : Int), datedRead (3543569 / 10000 : Rat) #v[none, some (3543569 / 10000 : Rat)] [(3551021 / 10000 : Rat)] (122030 : Int)]
private def trace_F4_8514_K3_fx : List (List (ReadObservation 2)) := [[datedRead (374 : Rat) #v[none, none] [] (0 : Int), datedRead (374 : Rat) #v[none, none] [] (0 : Int)], [datedRead (418 : Rat) #v[none, some (418 : Rat)] [] (0 : Int), datedRead (418 : Rat) #v[none, some (418 : Rat)] [(4188569 / 10000 : Rat)] (103096 : Int)], [datedRead (396 : Rat) #v[some (396 : Rat), none] [(992171 / 2500 : Rat)] (102788 : Int), datedRead (396 : Rat) #v[some (396 : Rat), none] [] (0 : Int)], [datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat)] [(1102171 / 2500 : Rat)] (102788 : Int), datedRead (440 : Rat) #v[some (440 : Rat), some (440 : Rat)] [(4408569 / 10000 : Rat)] (103096 : Int)]]
private def trace_F4_8514_K3_sx : List (ReadObservation 2) := [datedRead (751 / 2 : Rat) #v[none, none] [] (0 : Int), datedRead (4203569 / 10000 : Rat) #v[none, some (4203569 / 10000 : Rat)] [(4211021 / 10000 : Rat)] (122030 : Int), datedRead (995921 / 2500 : Rat) #v[some (995921 / 2500 : Rat), none] [(9978 / 25 : Rat)] (121099 : Int), datedRead (4423569 / 10000 : Rat) #v[some (1105921 / 2500 : Rat), some (4423569 / 10000 : Rat)] [(276629 / 625 : Rat)] (243123 : Int)]
private def trace_F4_8514_K3_sc : List (Vector Int 4) := [#v[(0 : Int), (122030 : Int), (121099 : Int), (243123 : Int)], #v[(0 : Int), (122030 : Int), (121099 : Int), (243123 : Int)], #v[(0 : Int), (122030 : Int), (121099 : Int), (243123 : Int)], #v[(0 : Int), (122030 : Int), (121099 : Int), (243123 : Int)]]

def trace_F4_8514_K3 : TraceTables cascade_F4_8514_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_F4_8514_K3_ft.getD r.val []).getD a.val empty2
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_F4_8514_K3_te.getD n.val []).getD a.val empty2
  secondTrain := Vector.ofFn fun n => trace_F4_8514_K3_st.getD n.val empty2
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_F4_8514_K3_fx.getD w.val []).getD a.val empty2
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8514_K3_sx.getD w.val empty2
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_F4_8514_K3_sc.getD w.val #v[0, 0, 0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_F4_8514_K3 : checks cascade_F4_8514_K3 trace_F4_8514_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_F4_8514_K3 : checkCascadeValid cascade_F4_8514_K3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_F4_8514_K3 : checkTrainingSeparation cascade_F4_8514_K3 left right trace_F4_8514_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_F4_8514_K3 : checkCascadeCalibrationOneSided cascade_F4_8514_K3 left right trace_F4_8514_K3.observations trace_F4_8514_K3.scoreAt = true := by decide +kernel

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
