import LayeredWitnessSupport
import LayeredTrainingChain
import LayeredMonotoneCheckerProofs
import MonotonePremiseSoundness

/-! Witness without inverters: `(x0 ∧ x1) ∨ x2` over three layers on three inputs.

- Layer 1 has `both(x0, x1)` and `copy(x2)`.
- Layer 2 has `either`.
- Layer 3 has `copy`.

Every premise of the latency chain, both for the training lessons and for every test
read, holds on the traces. The kernel checks them all. The frozen theorem
`layered_monotone_recognition_one_sided`, with its separation premise, is also applied as
a cross-check. -/

namespace LearnedCoincidence.Layered.WitnessAndOr

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF.PremiseCheck (patterns)
open MonotoneDNF (singleton)

def clock : SlotTiming := ⟨0, 1, 2⟩

def andNode : Node 3 3 := ⟨canonical .both, fun a => some (if a = 0 then 0 else 1), fun _ => 0,
  fun _ => pattern [0, 1]⟩
def copyInput : Node 3 3 := ⟨canonical .copy, fun a => if a = 0 then some 2 else none, fun _ => 0,
  fun _ => pattern [2]⟩
def orNode : Node 3 2 := ⟨canonical .either, some, fun _ => 0,
  fun g => if g = 0 then pattern [0, 1] else pattern [2]⟩
def outNode : Node 3 1 := ⟨canonical .copy, fun a => if a = 0 then some 0 else none, fun _ => 0,
  fun _ => pattern [2]⟩

def layer1 : Cascade 3 1 2 := .layer .input clock fun i => if i = 0 then andNode else copyInput
def layer2 : Cascade 3 2 1 := .layer layer1 clock fun _ => orNode
def circuit : Cascade 3 3 1 := .layer layer2 clock fun _ => outNode

def train : TrainingTrace circuit := simTrain circuit
def test (x : Pattern 3) : ReadTrace circuit := simulate (stepSchedule T0) circuit (externalAt T0 x)

def lmin : Nat → Rat := fun _ => 1
def lmax : Nat → Rat := fun _ => 1
def e : Nat → Rat := latencyLow lmin
def f : Nat → Rat := latencyHigh 0 lmax

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem valid_check : checkLayeredValid circuit = true := by decide +kernel
theorem training_check : checkLayeredTrainingCalibration circuit train = true := by decide +kernel
theorem reads_check : checkLayeredReadCalibration circuit train test = true := by decide +kernel
theorem separation_check : checkLayeredSeparation circuit train test = true := by decide +kernel
theorem dates_check : checkChainDates (stepSchedule T0) e f circuit = true := by decide +kernel
theorem lesson_dates_check : checkTrainingChainDates witnessClock e f circuit = true := by decide +kernel
theorem lesson_scheduled_check : checkTrainingScheduled witnessClock circuit train = true := by decide +kernel
theorem lesson_pulses_check : checkTrainingPulses witnessClock e f circuit train = true := by decide +kernel
theorem test_chain_check : ((patterns 3).all fun x =>
    checkScheduled (stepSchedule T0) circuit (test x) &&
    checkLatencies lmin lmax circuit (test x) &&
    checkExternalWindow (stepSchedule T0 0) 0 circuit (test x)) = true := by decide +kernel
theorem predicted_check : ((patterns 3).all fun x =>
    circuit.predict x 0 == ((x 0 && x 1) || x 2)) = true := by decide +kernel

private theorem every_pattern {P : Pattern 3 → Bool} (h : (patterns 3).all P = true) (x : Pattern 3) :
    P x = true :=
  List.all_eq_true.mp h x (MonotoneDNF.patterns_complete x)

theorem valid : circuit.Valid := layered_valid_checker_sound 3 3 1 _ valid_check

/-- The fully chained theorem on the witness: no arrival window assumed anywhere. -/
theorem computes (x : Pattern 3) :
    circuit.Trained train ∧ ArrivalWindows circuit (test x) ∧
    observed circuit (test x) 0 = ((x 0 && x 1) || x 2) := by
  have reads := (read_calibration_iff circuit train x (test x)).mp
    (layered_read_calibration_checker_sound 3 3 1 _ _ _ reads_check x)
  have chain := every_pattern test_chain_check x
  simp only [Bool.and_eq_true] at chain
  obtain ⟨⟨scheduled, latency⟩, external⟩ := chain
  obtain ⟨trained, windows, decisions⟩ := layered_recognition_fully_chained valid
    (training_chain_dates_checker_sound lesson_dates_check)
    (training_reads_of_calibration (layered_training_calibration_checker_sound 3 3 1 _ _ training_check))
    (training_scheduled_checker_sound lesson_scheduled_check)
    (training_pulses_checker_sound lesson_pulses_check)
    (chain_dates_checker_sound 3 3 1 _ _ _ _ dates_check) reads.1 reads.2.1
    (scheduled_checker_sound scheduled) (external_window_checker_sound external)
    (latencies_checker_sound latency)
  refine ⟨trained, windows, ?_⟩
  rw [decisions]
  exact beq_iff_eq.mp (every_pattern predicted_check x)

/-- Cross-check with the frozen layered theorem, whose premises include separation. -/
example : circuit.Trained train ∧ ∀ x, observed circuit (test x) = circuit.predict x :=
  layered_monotone_recognition_one_sided 3 3 1 circuit valid train test
    (layered_separation_checker_sound 3 3 1 _ _ _ separation_check)
    (layered_training_calibration_checker_sound 3 3 1 _ _ training_check)
    (layered_read_calibration_checker_sound 3 3 1 _ _ _ reads_check)

end LearnedCoincidence.Layered.WitnessAndOr
