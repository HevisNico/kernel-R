import MonotonePremiseSoundness
import MonotoneOneSidedRecognition

/-! A kernel gate written by the parameterized generator (research/learned-dnf-generator/emit.py) from synthetic.
Shape `Cascade 1 1 1`. Each `checks_*`, `valid_*`, `separation_*` and `calibration_*` theorem asserts a verdict
by `decide +kernel`; the file compiles only if the kernel agrees with every asserted value. -/

namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup

open TwoLayer (SlotTiming ReadObservation)

private def term : Fin 1 → Pattern 1 := fun _ => pattern [0]

private def empty1 : ReadObservation 1 := datedRead 0 #v[none] [] 0

def left : SlotTiming := ⟨(1 / 50 : Rat), (11 / 10 : Rat), (22 : Rat)⟩
def right : SlotTiming := ⟨(11 / 10 : Rat), (11 / 5 : Rat), (19 : Rat)⟩

def checks (p : Cascade 1 1 1) (t : TraceTables p) : Bool :=
  checkCascadeValid p &&
  checkTrainingSeparation p left right t.observations &&
  checkCascadeCalibrationOneSided p left right t.observations t.scoreAt

def cascade_Syn_X1_K0 : Cascade 1 1 1 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[68750]] : Vector (Vector Nat 1) 1).get a).get j,
    help := fun a => (#v[0] : Vector Nat 1).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[238] : Vector Nat 1).get a,
    testingError := fun a => (#v[238] : Vector Nat 1).get a,
    dose := 12500, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[50000] : Vector Nat 1).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 350, testingError := fun _ => 350,
    dose := 20000, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_Syn_X1_K0_ft : List (List (ReadObservation 1)) := [[datedRead (0 : Rat) #v[some (0 : Rat)] [] (68750 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat)] [] (81250 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat)] [] (93750 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat)] [(133 / 2 : Rat)] (106250 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat)] [(177 / 2 : Rat)] (106250 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat)] [(221 / 2 : Rat)] (106250 : Int)]]
private def trace_Syn_X1_K0_te : List (List (ReadObservation 1)) := [[datedRead (132 : Rat) #v[some (132 : Rat)] [(265 / 2 : Rat)] (106250 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat)] [(309 / 2 : Rat)] (106250 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat)] [(353 / 2 : Rat)] (106250 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat)] [(397 / 2 : Rat)] (106250 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat)] [(441 / 2 : Rat)] (106250 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat)] [(485 / 2 : Rat)] (106250 : Int)]]
private def trace_Syn_X1_K0_st : List (ReadObservation 1) := [datedRead (134 : Rat) #v[some (134 : Rat)] [] (50000 : Int), datedRead (156 : Rat) #v[some (156 : Rat)] [] (70000 : Int), datedRead (178 : Rat) #v[some (178 : Rat)] [] (90000 : Int), datedRead (200 : Rat) #v[some (200 : Rat)] [(401 / 2 : Rat)] (110000 : Int), datedRead (222 : Rat) #v[some (222 : Rat)] [(445 / 2 : Rat)] (110000 : Int), datedRead (244 : Rat) #v[some (244 : Rat)] [(489 / 2 : Rat)] (110000 : Int)]
private def trace_Syn_X1_K0_fx : List (List (ReadObservation 1)) := [[datedRead (264 : Rat) #v[none] [] (0 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat)] [(573 / 2 : Rat)] (106250 : Int)]]
private def trace_Syn_X1_K0_sx : List (ReadObservation 1) := [datedRead (531 / 2 : Rat) #v[none] [] (0 : Int), datedRead (288 : Rat) #v[some (288 : Rat)] [(577 / 2 : Rat)] (110000 : Int)]
private def trace_Syn_X1_K0_sc : List (Vector Int 2) := [#v[(0 : Int), (110000 : Int)], #v[(0 : Int), (110000 : Int)]]

def trace_Syn_X1_K0 : TraceTables cascade_Syn_X1_K0 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_Syn_X1_K0_ft.getD r.val []).getD a.val empty1
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_Syn_X1_K0_te.getD n.val []).getD a.val empty1
  secondTrain := Vector.ofFn fun n => trace_Syn_X1_K0_st.getD n.val empty1
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_Syn_X1_K0_fx.getD w.val []).getD a.val empty1
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_Syn_X1_K0_sx.getD w.val empty1
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_Syn_X1_K0_sc.getD w.val #v[0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_Syn_X1_K0 : checks cascade_Syn_X1_K0 trace_Syn_X1_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Syn_X1_K0 : checkCascadeValid cascade_Syn_X1_K0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Syn_X1_K0 : checkTrainingSeparation cascade_Syn_X1_K0 left right trace_Syn_X1_K0.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Syn_X1_K0 : checkCascadeCalibrationOneSided cascade_Syn_X1_K0 left right trace_Syn_X1_K0.observations trace_Syn_X1_K0.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_Syn_X1_K0 : ∀ x i, (trace_Syn_X1_K0.observations.secondTest x i).fired = output cascade_Syn_X1_K0 i x := by
  have checked := checks_Syn_X1_K0
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 1 1 1 cascade_Syn_X1_K0
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_Syn_X1_K0.observations trace_Syn_X1_K0.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

def cascade_Syn_X1_K3 : Cascade 1 1 1 where
  first := {
    target := term, tests := [],
    initialGain := fun a j => ((#v[#v[68750]] : Vector (Vector Nat 1) 1).get a).get j,
    help := fun a => (#v[0] : Vector Nat 1).get a, threshold := fun _ => 100000,
    trainingError := fun a => (#v[2793] : Vector Nat 1).get a,
    testingError := fun a => (#v[2793] : Vector Nat 1).get a,
    dose := 12500, maxWrites := 5, rail := 1000000
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ j => (#v[50000] : Vector Nat 1).get j, help := fun _ => 0, threshold := fun _ => 100000,
    trainingError := fun _ => 4439, testingError := fun _ => 4439,
    dose := 20000, maxWrites := 5, rail := 1000000
  }
  delay := fun _ _ => 3 / 2
  heldOut := []

private def trace_Syn_X1_K3_ft : List (List (ReadObservation 1)) := [[datedRead (0 : Rat) #v[some (0 : Rat)] [] (68750 : Int)], [datedRead (22 : Rat) #v[some (22 : Rat)] [] (81250 : Int)], [datedRead (44 : Rat) #v[some (44 : Rat)] [] (93750 : Int)], [datedRead (66 : Rat) #v[some (66 : Rat)] [(133 / 2 : Rat)] (106250 : Int)], [datedRead (88 : Rat) #v[some (88 : Rat)] [(177 / 2 : Rat)] (106250 : Int)], [datedRead (110 : Rat) #v[some (110 : Rat)] [(221 / 2 : Rat)] (106250 : Int)]]
private def trace_Syn_X1_K3_te : List (List (ReadObservation 1)) := [[datedRead (132 : Rat) #v[some (132 : Rat)] [(265 / 2 : Rat)] (106250 : Int)], [datedRead (154 : Rat) #v[some (154 : Rat)] [(309 / 2 : Rat)] (106250 : Int)], [datedRead (176 : Rat) #v[some (176 : Rat)] [(353 / 2 : Rat)] (106250 : Int)], [datedRead (198 : Rat) #v[some (198 : Rat)] [(397 / 2 : Rat)] (106250 : Int)], [datedRead (220 : Rat) #v[some (220 : Rat)] [(441 / 2 : Rat)] (106250 : Int)], [datedRead (242 : Rat) #v[some (242 : Rat)] [(485 / 2 : Rat)] (106250 : Int)]]
private def trace_Syn_X1_K3_st : List (ReadObservation 1) := [datedRead (134 : Rat) #v[some (134 : Rat)] [] (50000 : Int), datedRead (156 : Rat) #v[some (156 : Rat)] [] (70000 : Int), datedRead (178 : Rat) #v[some (178 : Rat)] [] (90000 : Int), datedRead (200 : Rat) #v[some (200 : Rat)] [(401 / 2 : Rat)] (110000 : Int), datedRead (222 : Rat) #v[some (222 : Rat)] [(445 / 2 : Rat)] (110000 : Int), datedRead (244 : Rat) #v[some (244 : Rat)] [(489 / 2 : Rat)] (110000 : Int)]
private def trace_Syn_X1_K3_fx : List (List (ReadObservation 1)) := [[datedRead (264 : Rat) #v[none] [] (0 : Int)], [datedRead (286 : Rat) #v[some (286 : Rat)] [(573 / 2 : Rat)] (106250 : Int)]]
private def trace_Syn_X1_K3_sx : List (ReadObservation 1) := [datedRead (531 / 2 : Rat) #v[none] [] (0 : Int), datedRead (288 : Rat) #v[some (288 : Rat)] [(577 / 2 : Rat)] (110000 : Int)]
private def trace_Syn_X1_K3_sc : List (Vector Int 2) := [#v[(0 : Int), (110000 : Int)], #v[(0 : Int), (110000 : Int)]]

def trace_Syn_X1_K3 : TraceTables cascade_Syn_X1_K3 where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun a => (trace_Syn_X1_K3_ft.getD r.val []).getD a.val empty1
  teach := Vector.ofFn fun n => Vector.ofFn fun a => (trace_Syn_X1_K3_te.getD n.val []).getD a.val empty1
  secondTrain := Vector.ofFn fun n => trace_Syn_X1_K3_st.getD n.val empty1
  firstTest := Vector.ofFn fun w => Vector.ofFn fun a => (trace_Syn_X1_K3_fx.getD w.val []).getD a.val empty1
  secondTest := Vector.ofFn fun w => Vector.ofFn fun _ => trace_Syn_X1_K3_sx.getD w.val empty1
  scores := Vector.ofFn fun w => Vector.ofFn fun _ => trace_Syn_X1_K3_sc.getD w.val #v[0, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks_Syn_X1_K3 : checks cascade_Syn_X1_K3 trace_Syn_X1_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_Syn_X1_K3 : checkCascadeValid cascade_Syn_X1_K3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separation_Syn_X1_K3 : checkTrainingSeparation cascade_Syn_X1_K3 left right trace_Syn_X1_K3.observations = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem calibration_Syn_X1_K3 : checkCascadeCalibrationOneSided cascade_Syn_X1_K3 left right trace_Syn_X1_K3.observations trace_Syn_X1_K3.scoreAt = true := by decide +kernel

/-- The predicted outputs of the second layer follow from the measures by kernel check. -/
theorem outputs_Syn_X1_K3 : ∀ x i, (trace_Syn_X1_K3.observations.secondTest x i).fired = output cascade_Syn_X1_K3 i x := by
  have checked := checks_Syn_X1_K3
  unfold checks at checked
  obtain ⟨parameterAndCalendar, calibration⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨params, calendar⟩ := Bool.and_eq_true_iff.mp parameterAndCalendar
  exact (two_layer_monotone_recognition_one_sided 1 1 1 cascade_Syn_X1_K3
    (cascade_valid_checker_sound _ _ _ _ params) left right
    trace_Syn_X1_K3.observations trace_Syn_X1_K3.scoreAt
    (training_separation_checker_sound _ _ _ _ _ _ _ calendar)
    (cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ calibration)).2

end LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup
