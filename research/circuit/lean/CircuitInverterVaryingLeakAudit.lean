import CircuitInverterVaryingLeakExamples
import Lean.Util.CollectAxioms

/-! Audit of the varying-leak modules: no project axiom, and only `propext`,
`Classical.choice` and `Quot.sound`. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`CircuitInverterVaryingLeak, `CircuitInverterVaryingLeakExamples]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains env.header.moduleNames[idx.toNat]! do continue
      if info.isAxiom then throwError "Unexpected varying-leak axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  logInfo m!"Varying-leak audit passed: {checked} declarations."

#print axioms KernelR.Circuit.varying_leak_integral_form
#print axioms KernelR.Circuit.varying_leak_drift
#print axioms KernelR.Circuit.inhibited_silence_varying
#print axioms KernelR.Circuit.uninhibited_first_crossing_varying
#print axioms KernelR.Circuit.inhibited_silence_varying_witness
