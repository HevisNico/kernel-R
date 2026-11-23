import CircuitInverterLeakExamples
import Lean.Util.CollectAxioms

/-! Audit of the leak-asymmetry modules: no project axiom, and only `propext`,
`Classical.choice` and `Quot.sound`. This package has no frozen `Prop` targets; the
statements are the theorems' own types, held by `check_inverter_leak.py`. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`CircuitInverterLeak, `CircuitInverterLeakExamples]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains env.header.moduleNames[idx.toNat]! do continue
      if info.isAxiom then throwError "Unexpected leak axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  logInfo m!"Leak audit passed: {checked} declarations."

#print axioms KernelR.Circuit.decay_factor_gap
#print axioms KernelR.Circuit.leaky_response_leak_error
#print axioms KernelR.Circuit.reference_leak_gap
#print axioms KernelR.Circuit.inhibited_silence_leaks
#print axioms KernelR.Circuit.uninhibited_first_crossing_leaks
#print axioms KernelR.Circuit.inhibited_silence_leaks_witness
#print axioms KernelR.Circuit.help_alone_exceeds_level_leaks
