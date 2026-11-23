import InverterTrainingWitness
import Lean.Util.CollectAxioms

/-! Audit of training through the inverters: no project axiom, only `propext`,
`Classical.choice` and `Quot.sound`, and the two frozen targets have their exact types. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`TwoRailsExplicit, `InverterTraining, `InverterTrainingWitness]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains env.header.moduleNames[idx.toNat]! do continue
      if info.isAxiom then throwError "Unexpected inverter-training axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  let required := #[
    (``LearnedCoincidence.MonotoneDNF.RailsExplicit.every_function_on_two_rails_explicit,
      ``LearnedCoincidence.MonotoneDNF.RailsExplicit.EveryFunctionOnTwoRailsExplicit),
    (``LearnedCoincidence.MonotoneDNF.every_function_trained_through_inverters,
      ``LearnedCoincidence.MonotoneDNF.EveryFunctionTrainedThroughInverters)]
  for (thm, target) in required do
    let some info := env.find? thm | throwError "{thm} is missing"
    unless info.type == mkConst target do throwError "{thm} does not have the type {target}"
  logInfo m!"Inverter training audit passed: {checked} declarations."

#print axioms LearnedCoincidence.MonotoneDNF.RailsExplicit.every_function_on_two_rails_explicit
#print axioms LearnedCoincidence.MonotoneDNF.training_through_front_end
#print axioms LearnedCoincidence.MonotoneDNF.front_end_slots_disjoint
#print axioms LearnedCoincidence.MonotoneDNF.training_inverter_slots_disjoint
#print axioms LearnedCoincidence.MonotoneDNF.trained_inverters_compute
#print axioms LearnedCoincidence.MonotoneDNF.every_function_trained_through_inverters
#print axioms LearnedCoincidence.MonotoneDNF.InverterTrainingWitness.premises_hold
#print axioms LearnedCoincidence.MonotoneDNF.InverterTrainingWitness.answers_not
