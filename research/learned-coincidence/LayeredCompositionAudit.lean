import LayeredInverters
import LayeredTrainingChain
import LayeredChainExamples
import LayeredWitnessAndOr
import LayeredWitnessNot
import LayeredWitnessXor
import Lean.Util.CollectAxioms

/-! Audit of the layered-composition modules.

- No project axiom. The allowed axioms are only `propext`, `Classical.choice` and
  `Quot.sound`, so a `sorry` (`sorryAx`) fails the audit.
- Every main theorem has the exact type of its frozen target.
- The witnesses' conclusions are restated below with their meaning, so a weakened witness
  does not compile.

What is NOT proved, and the premises that stay assumed, are listed in
`LAYERED_COMPOSITION.md`. In particular, `TrainingSeparation` is a premise of the frozen
layered target and is used by none of these proofs. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`LayeredCompositionTarget, `LayeredRecognitionAt, `LayeredChain,
    `LayeredTrainingChainTarget, `LayeredTrainingChain, `LayeredChainChecks, `LayeredChainExamples,
    `LayeredInverterTarget, `LayeredInverters, `LayeredWitnessSupport, `LayeredWitnessAndOr,
    `LayeredWitnessNot, `LayeredWitnessXor]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains env.header.moduleNames[idx.toNat]! do continue
      if info.isAxiom then throwError "Unexpected layered-composition axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  let required := #[
    (``LearnedCoincidence.Layered.layered_recognition_at, ``LearnedCoincidence.Layered.LayeredRecognitionAt),
    (``LearnedCoincidence.Layered.layered_recognition_chained,
      ``LearnedCoincidence.Layered.LayeredRecognitionChained),
    (``LearnedCoincidence.Layered.layered_recognition_from_latency,
      ``LearnedCoincidence.Layered.LayeredRecognitionFromLatency),
    (``LearnedCoincidence.Layered.layered_recognition_from_deadlines,
      ``LearnedCoincidence.Layered.LayeredRecognitionFromDeadlines),
    (``LearnedCoincidence.Layered.chain_dates_checker_sound,
      ``LearnedCoincidence.Layered.ChainDatesCheckerSound),
    (``LearnedCoincidence.Layered.chain_dates_checker_complete,
      ``LearnedCoincidence.Layered.ChainDatesCheckerComplete),
    (``LearnedCoincidence.Layered.training_calibration_chained,
      ``LearnedCoincidence.Layered.TrainingCalibrationChained),
    (``LearnedCoincidence.Layered.layered_inverters_compute,
      ``LearnedCoincidence.Layered.LayeredInvertersCompute),
    (``LearnedCoincidence.Layered.layered_inverters_chained,
      ``LearnedCoincidence.Layered.LayeredInvertersChained),
    (``LearnedCoincidence.Layered.every_function_layered_with_inverters,
      ``LearnedCoincidence.Layered.EveryFunctionLayeredWithInverters)]
  for (theoremName, target) in required do
    let some info := env.find? theoremName | throwError "Missing theorem {theoremName}"
    unless info.isTheorem && info.type.isConstOf target do
      throwError "Expected theorem {theoremName} with type {target}"
  logInfo m!"Layered composition audit passed: {checked} declarations."

namespace LearnedCoincidence.Layered

open MonotoneDNF (rails)

/-! The witnesses' conclusions, restated. -/

example (x : Pattern 3) : observed WitnessAndOr.circuit (WitnessAndOr.test x) 0 = ((x 0 && x 1) || x 2) :=
  (WitnessAndOr.computes x).2.2

example (y : Pattern 1) : observed WitnessNot.circuit (WitnessNot.test (rails y)) 0 = !y 0 :=
  (WitnessNot.computes y).2

example (y : Pattern 2) : observed WitnessXor.circuit (WitnessXor.test (rails y)) 0 = (y 0 != y 1) :=
  (WitnessXor.computes y).2

/-! The deadline-only chain rejects main's example; the latency chain accepts it. -/

example : checkChainDates ChainExample.start (latencyLow fun _ => 0)
    (latencyHigh 0 (layerDeadline Example.circuit)) Example.circuit = false :=
  ChainExample.deadline_only_rejected

example : checkChainDates ChainExample.start (latencyLow fun _ => 1) (latencyHigh 0 fun _ => 1)
    Example.circuit = true :=
  ChainExample.latency_accepted

end LearnedCoincidence.Layered

#print axioms LearnedCoincidence.Layered.layered_recognition_at
#print axioms LearnedCoincidence.Layered.layered_recognition_from_latency
#print axioms LearnedCoincidence.Layered.training_calibration_chained
#print axioms LearnedCoincidence.Layered.layered_inverters_chained
#print axioms LearnedCoincidence.Layered.every_function_layered_with_inverters
#print axioms LearnedCoincidence.Layered.WitnessAndOr.computes
#print axioms LearnedCoincidence.Layered.WitnessNot.computes
#print axioms LearnedCoincidence.Layered.WitnessXor.computes
