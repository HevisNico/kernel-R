import LayeredWitnessSupport
import LayeredMonotoneCheckerProofs
import LayeredReadCheckAt

/-! Calibrated instance NOT1 (not x), seed 9801, at K3: research/layered-networks/leancal.py. -/

namespace LearnedCoincidence.Layered.CalNOT1K3

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF.PremiseCheck (patterns)
open MonotoneDNF (InverterTiming rails)

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

def timing1 : SlotTiming := ⟨(1 / 5 : Rat), (7 / 5 : Rat), (12 / 5 : Rat)⟩
def cell1_0 : Cell := { gate := .copy, initialGain := fun a => if a.val = 0 then 85458 else 0, help := 0, threshold := 100000, trainError := 1324, testError := 1324, dose := 8068, maxWrites := 3, rail := 1000000 }
def node1_0 : Node 2 2 := ⟨cell1_0, fun a => if a.val = 0 then some 1 else none, fun _ => (3 / 25 : Rat), fun g => if g.val = 0 then pattern [1] else pattern []⟩
def layer1 : Cascade 2 1 1 := .layer (Cascade.input : Cascade 2 0 2) timing1 fun i => node1_0

def circuit := layer1

def blankRead : ReadObservation 2 := ⟨0, fun _ => none, [], 0⟩
def blankInv : ReadObservation 1 := ⟨0, fun _ => none, [], 0⟩
def arr2 (a b : Option Rat) : Fin 2 → Option Rat := fun j => if j.val = 0 then a else b
def maskIdx (y : Pattern 2) : Nat := (if y 0 then 1 else 0) + (if y 1 then 2 else 0)

/-- A trace constructor from data rows (top layer first; each read with its four reference scores) and the
line arrivals. No proof obligation. -/
def build : (c : Cascade M L N) → List (List (ReadObservation 2 × List Int)) → List (Option Rat) → ReadTrace c
  | .input, _, ext => fun j => ext.getD j.val none
  | .layer lower _ _, rows, ext => ⟨build lower rows.tail ext,
      fun i => ((rows.headD []).getD i.val (blankRead, [])).1,
      fun i y => (((rows.headD []).getD i.val (blankRead, [])).2).getD (maskIdx y) 0⟩

def testData : Nat → List (List (ReadObservation 2 × List Int)) × List (Option Rat)
  | 0 => ([[(⟨(19313 / 200 : Rat), arr2 (some (19329 / 200 : Rat)) (none), [(19513 / 200 : Rat)], 101593⟩, [0, 101593, 0, 0])]], [none, some (3861 / 40 : Rat)])
  | 1 => ([[(⟨(23713 / 200 : Rat), arr2 (none) (none), [], 0⟩, [0, 101593, 0, 0])]], [some (23689 / 200 : Rat), none])
  | _ => ([], [])
def test (k : Nat) : ReadTrace circuit := build circuit (testData k).1 (testData k).2
def code (y : Pattern 1) : Nat := (List.finRange 1).foldl (fun acc j => acc + if y j then 2 ^ j.val else 0) 0
def expect : Nat → Bool
  | 0 => true
  | 1 => false
  | _ => false
def lines (y : Pattern 1) : Pattern 2 := rails y

def lessonRow : Nat → Nat → Nat → Nat → List (List (ReadObservation 2 × List Int)) × List (Option Rat) × ReadObservation 2
  | 1, 0, 0, 0 => ([], [none, some (341 / 40 : Rat)], ⟨(1713 / 200 : Rat), arr2 (some (1729 / 200 : Rat)) (none), [], 85458⟩)
  | 1, 0, 0, 1 => ([], [none, some (1221 / 40 : Rat)], ⟨(6113 / 200 : Rat), arr2 (some (6129 / 200 : Rat)) (none), [], 93526⟩)
  | 1, 0, 0, 2 => ([], [none, some (2101 / 40 : Rat)], ⟨(10513 / 200 : Rat), arr2 (some (10529 / 200 : Rat)) (none), [(10713 / 200 : Rat)], 101594⟩)
  | 1, 0, 0, 3 => ([], [none, some (2981 / 40 : Rat)], ⟨(14913 / 200 : Rat), arr2 (some (14929 / 200 : Rat)) (none), [(15113 / 200 : Rat)], 101594⟩)
  | _, _, _, _ => ([], [], blankRead)
def buildTrain : (c : Cascade M L N) → TrainingTrace c
  | .input => ()
  | .layer (L := L) lower _ _ => ⟨buildTrain lower,
      fun i g r => build lower (lessonRow (L + 1) i.val g.val r).1 (lessonRow (L + 1) i.val g.val r).2.1,
      fun i g r => (lessonRow (L + 1) i.val g.val r).2.2⟩
def train : TrainingTrace circuit := buildTrain circuit

theorem valid_check : checkLayeredValid circuit = true := by decide +kernel
theorem training_check : checkLayeredTrainingCalibration circuit train = true := by decide +kernel
theorem reads_check : ((patterns 1).all fun y => Checker.oneRead circuit train (lines y) (test (code y))) = true := by decide +kernel
theorem predicted_check : ((patterns 1).all fun y => circuit.predict (lines y) 0 == expect (code y)) = true := by decide +kernel

private theorem every_pattern {P : Pattern 1 → Bool} (h : (patterns 1).all P = true) (y : Pattern 1) :
    P y = true := List.all_eq_true.mp h y (MonotoneDNF.patterns_complete y)

/-- The recognition theorem on the measured instance: the cascade is trained, and at every input pattern
the observed output is the expected function. Applied, not compared. -/
theorem computes (y : Pattern 1) :
    circuit.Trained train ∧ observed circuit (test (code y)) 0 = expect (code y) := by
  have valid := layered_valid_checker_sound _ _ _ _ valid_check
  have training := layered_training_calibration_checker_sound _ _ _ _ _ training_check
  have reads := one_read_checker_sound (every_pattern reads_check y)
  obtain ⟨trained, decided⟩ := layered_recognition_at _ _ _ circuit valid train training (lines y) _ reads
  refine ⟨trained, ?_⟩
  rw [decided]
  exact beq_iff_eq.mp (every_pattern predicted_check y)

end LearnedCoincidence.Layered.CalNOT1K3
