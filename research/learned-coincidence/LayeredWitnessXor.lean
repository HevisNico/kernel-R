import LayeredWitnessSupport
import LayeredMonotoneCheckerProofs
import MonotonePremiseSoundness

/-! Witness with inverters: XOR on two inputs, over three layers, with two inverters.

The cascade is admissible and trained. At every input pattern `y`, the front end, the
layer reads and the latency chain hold, and `layered_inverters_chained` gives the answer.
The kernel checks every premise. -/

namespace LearnedCoincidence.Layered.WitnessXor

open TwoLayer (ReadObservation SlotTiming)
open MonotoneDNF.PremiseCheck (patterns)
open MonotoneDNF (rails)

/-- Layer 1 reads the front end, whose pulses spread over 1/4. -/
def front : SlotTiming := ⟨1 / 4, 1, 2⟩
def clock : SlotTiming := ⟨0, 1, 2⟩

/-- Lines 0, 1 are the inputs, lines 2, 3 their complements.
Layer 1: `x0 ∧ ¬x1` and `¬x0 ∧ x1`. Layer 2: OR. Layer 3: copy. -/
def andLeft : Node 4 4 := ⟨canonical .both, fun a => some (if a = 0 then 0 else 3), fun _ => 0,
  fun _ => pattern [0, 3]⟩
def andRight : Node 4 4 := ⟨canonical .both, fun a => some (if a = 0 then 2 else 1), fun _ => 0,
  fun _ => pattern [1, 2]⟩
def orNode : Node 4 2 := ⟨canonical .either, some, fun _ => 0,
  fun g => if g = 0 then pattern [0, 3] else pattern [1, 2]⟩
def outNode : Node 4 1 := ⟨canonical .copy, fun a => if a = 0 then some 0 else none, fun _ => 0,
  fun _ => pattern [0, 3]⟩

def layer1 : Cascade 4 1 2 := .layer .input front fun i => if i = 0 then andLeft else andRight
def layer2 : Cascade 4 2 1 := .layer layer1 clock fun _ => orNode
def circuit : Cascade 4 3 1 := .layer layer2 clock fun _ => outNode

def train : TrainingTrace circuit := simTrain circuit
def test (x : Pattern 4) : ReadTrace circuit := simulate (stepSchedule (T0 + 1 / 2)) circuit (lineArrivals (M := 2) x)

def lmin : Nat → Rat := fun _ => 1
def lmax : Nat → Rat := fun _ => 1
def w : Rat := 1 / 4

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem valid_check : checkLayeredValid circuit = true := by decide +kernel
theorem training_check : checkLayeredTrainingCalibration circuit train = true := by decide +kernel
theorem reads_check : checkLayeredReadCalibration circuit train test = true := by decide +kernel
theorem dates_check :
    checkChainDates (stepSchedule (T0 + 1 / 2)) (latencyLow lmin) (latencyHigh w lmax) circuit = true := by
  decide +kernel
theorem front_check : ((patterns 2).all fun y =>
    checkLayeredFront witnessInverter T0 (frontExternal y) (frontInverters y) circuit (test (rails y)) &&
    checkScheduled (stepSchedule (T0 + 1 / 2)) circuit (test (rails y)) &&
    checkLatencies lmin lmax circuit (test (rails y))) = true := by decide +kernel
theorem realised_check : ((patterns 2).all fun y => (List.finRange 2).all fun j =>
    (frontExternal y j).isSome == y j) = true := by decide +kernel
theorem predicted_check : ((patterns 2).all fun y =>
    circuit.predict (rails y) 0 == (y 0 != y 1)) = true := by decide +kernel
theorem dates_fit : stepSchedule (T0 + 1 / 2) 0 = T0 + witnessInverter.emitEarly ∧
    witnessInverter.window ≤ w ∧ witnessInverter.emitLate - witnessInverter.emitEarly ≤ w := by
  decide +kernel

private theorem every_pattern {P : Pattern 2 → Bool} (h : (patterns 2).all P = true) (y : Pattern 2) :
    P y = true :=
  List.all_eq_true.mp h y (MonotoneDNF.patterns_complete y)

theorem valid : circuit.Valid := layered_valid_checker_sound _ _ _ _ valid_check

/-- The network, read through the inverters, answers XOR at every input pattern. -/
theorem computes (y : Pattern 2) :
    ArrivalWindows circuit (test (rails y)) ∧ observed circuit (test (rails y)) 0 = (y 0 != y 1) := by
  have reads := (read_calibration_iff circuit train (rails y) (test (rails y))).mp
    (layered_read_calibration_checker_sound _ _ _ _ _ _ reads_check (rails y))
  have premises := every_pattern front_check y
  simp only [Bool.and_eq_true] at premises
  obtain ⟨⟨frontOk, scheduled⟩, latency⟩ := premises
  have realised : ∀ j, (frontExternal y j).isSome = y j := fun j =>
    beq_iff_eq.mp (List.all_eq_true.mp (every_pattern realised_check y) j (List.mem_finRange j))
  obtain ⟨first, windowFits, spreadFits⟩ := dates_fit
  obtain ⟨windows, decisions⟩ := layered_inverters_chained _ _ _ circuit valid train
    (layered_training_calibration_checker_sound _ _ _ _ _ training_check)
    witnessInverter T0 (frontExternal y) (frontInverters y) y (test (rails y))
    (stepSchedule (T0 + 1 / 2)) lmin lmax w first windowFits spreadFits
    (chain_dates_checker_sound _ _ _ _ _ _ _ dates_check) realised
    (layered_front_checker_sound frontOk) reads.2.1
    (scheduled_checker_sound scheduled) (latencies_checker_sound latency)
  refine ⟨windows, ?_⟩
  rw [decisions]
  exact beq_iff_eq.mp (every_pattern predicted_check y)

end LearnedCoincidence.Layered.WitnessXor
