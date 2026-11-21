import Inverters
import Lean.Util.CollectAxioms

/-! Audit of the inverter modules: no project axiom, only `propext`,
`Classical.choice` and `Quot.sound`, and the composition theorem has its exact type. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`InverterTarget, `Inverters]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains env.header.moduleNames[idx.toNat]! do continue
      if info.isAxiom then throwError "Unexpected inverter axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  let some info := env.find? ``LearnedCoincidence.MonotoneDNF.every_function_with_inverters
    | throwError "every_function_with_inverters is missing"
  unless info.type == mkConst ``LearnedCoincidence.MonotoneDNF.EveryFunctionWithInverters do
    throwError "every_function_with_inverters does not have the type EveryFunctionWithInverters"
  logInfo m!"Inverter audit passed: {checked} declarations."

#print axioms LearnedCoincidence.MonotoneDNF.front_end_input
#print axioms LearnedCoincidence.MonotoneDNF.front_end_window
#print axioms LearnedCoincidence.MonotoneDNF.front_end_calibrated
#print axioms LearnedCoincidence.MonotoneDNF.one_sided_recognition_at
#print axioms LearnedCoincidence.MonotoneDNF.every_function_with_inverters
