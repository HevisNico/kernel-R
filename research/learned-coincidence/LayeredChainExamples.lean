import LayeredChainChecks
import LayeredMonotoneExample
import LayeredMonotoneCheckerProofs
import MonotonePremiseSoundness

/-! The chain on the repository's three-layer example (`LayeredMonotoneExample`), which tests
at date 120. The external pulses arrive at 120. Layer `ℓ` reads at `119 + ℓ`, has skew 0
and deadline 1, and emits exactly one unit after its read start.

- The deadline-only chain (`e = 0`, `f = deadline`) rejects this calendar. It fails at the
  lower inequality of layer 2: `s 2 ≤ s 1 + 0 + δ` reads `121 ≤ 120`.
- The latency chain with `λmin = λmax = 1` accepts it. Its trace premises hold at every
  external mask, so `layered_recognition_from_latency` gives the arrival windows, the
  formula and the output date. -/

namespace LearnedCoincidence.Layered.ChainExample

open MonotoneDNF.PremiseCheck (patterns)

def start : Nat → Rat := fun ℓ => if ℓ = 0 then 120 else 119 + ℓ

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem deadline_only_rejected :
    checkChainDates start (latencyLow fun _ => 0) (latencyHigh 0 (layerDeadline Example.circuit))
      Example.circuit = false := by decide +kernel

/-- The single failing inequality of the deadline-only chain, at layer 2. -/
example : ¬ (start 2 ≤ start 1 + latencyLow (fun _ => 0) 1 + 0) := by decide +kernel

theorem latency_accepted :
    checkChainDates start (latencyLow fun _ => 1) (latencyHigh 0 fun _ => 1) Example.circuit = true := by
  decide +kernel

private theorem scheduled : ((patterns 4).all fun x => checkScheduled start Example.circuit (Example.test x)) = true := by
  decide +kernel

private theorem latencies :
    ((patterns 4).all fun x => checkLatencies (fun _ => 1) (fun _ => 1) Example.circuit (Example.test x)) = true := by
  decide +kernel

private theorem external :
    ((patterns 4).all fun x => checkExternalWindow (start 0) 0 Example.circuit (Example.test x)) = true := by
  decide +kernel

private theorem accepted_valid : checkLayeredValid Example.circuit = true := by decide +kernel
private theorem accepted_training :
    checkLayeredTrainingCalibration Example.circuit Example.train = true := by decide +kernel
private theorem accepted_tests :
    checkLayeredReadCalibration Example.circuit Example.train Example.test = true := by decide +kernel

private theorem every_pattern {P : Pattern 4 → Bool} (h : (patterns 4).all P = true) (x : Pattern 4) :
    P x = true :=
  List.all_eq_true.mp h x (MonotoneDNF.patterns_complete x)

/-- The latency form on the example: arrival windows, decisions and output date at 123 or later. -/
theorem example_from_latency (x : Pattern 4) :
    ArrivalWindows Example.circuit (Example.test x) ∧
    observed Example.circuit (Example.test x) = Example.circuit.predict x ∧
    ∀ i t, pulseDates Example.circuit (Example.test x) i = some t → start 3 + 1 ≤ t ∧ t ≤ start 3 + 1 := by
  have reads := (read_calibration_iff Example.circuit Example.train x (Example.test x)).mp
    (layered_read_calibration_checker_sound 4 3 1 _ _ _ accepted_tests x)
  exact layered_recognition_from_latency 4 3 1 Example.circuit
    (layered_valid_checker_sound 4 3 1 _ accepted_valid) Example.train
    (layered_training_calibration_checker_sound 4 3 1 _ _ accepted_training)
    start (fun _ => 1) (fun _ => 1) 0 (chain_dates_checker_sound 4 3 1 _ _ _ _ latency_accepted)
    x (Example.test x) reads.1 reads.2.1
    (scheduled_checker_sound (every_pattern scheduled x))
    (external_window_checker_sound (every_pattern external x))
    (latencies_checker_sound (every_pattern latencies x))

end LearnedCoincidence.Layered.ChainExample
