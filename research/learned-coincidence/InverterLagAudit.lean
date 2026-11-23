import InverterLagWitness
import Lean.Util.CollectAxioms

/-! Audit of the direct-rail delay tolerance: no project axiom, only `propext`,
`Classical.choice` and `Quot.sound`, and the frozen target has its exact type. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`InverterLag, `InverterLagWitness]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains env.header.moduleNames[idx.toNat]! do continue
      if info.isAxiom then throwError "Unexpected inverter-lag axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  let some info := env.find? ``LearnedCoincidence.MonotoneDNF.every_function_with_delay_tolerance
    | throwError "every_function_with_delay_tolerance is missing"
  unless info.type == mkConst ``LearnedCoincidence.MonotoneDNF.EveryFunctionWithDelayTolerance do
    throwError "every_function_with_delay_tolerance does not have the type EveryFunctionWithDelayTolerance"
  logInfo m!"Inverter lag audit passed: {checked} declarations."

#print axioms LearnedCoincidence.MonotoneDNF.front_end_is_lag
#print axioms LearnedCoincidence.MonotoneDNF.front_end_lag_input
#print axioms LearnedCoincidence.MonotoneDNF.front_end_lag_window
#print axioms LearnedCoincidence.MonotoneDNF.front_end_lag_calibrated
#print axioms LearnedCoincidence.MonotoneDNF.scheduled_training_lag_calibration
#print axioms LearnedCoincidence.MonotoneDNF.inverters_compute_lag
#print axioms LearnedCoincidence.MonotoneDNF.scheduled_inverters_compute_lag
#print axioms LearnedCoincidence.MonotoneDNF.every_function_with_delay_tolerance
#print axioms LearnedCoincidence.MonotoneDNF.InverterLagWitness.premises_hold
#print axioms LearnedCoincidence.MonotoneDNF.InverterLagWitness.answers_not
