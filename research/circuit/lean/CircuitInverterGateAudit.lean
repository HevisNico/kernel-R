import CircuitInverterGate9901
import Lean.Util.CollectAxioms

/-! Audit of the gate bridge: no project axiom, and only `propext`,
`Classical.choice` and `Quot.sound`. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`CircuitInverterTaylor, `CircuitInverterGateBridge, `CircuitInverterGate9901]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains env.header.moduleNames[idx.toNat]! do continue
      if info.isAxiom then throwError "Unexpected gate axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  logInfo m!"Gate bridge audit passed: {checked} declarations."

#print axioms KernelR.Circuit.hasDerivAt_expNegSum
#print axioms KernelR.Circuit.expNeg_signed_remainder_nonneg
#print axioms KernelR.Circuit.expNegSum_six_le
#print axioms KernelR.Circuit.exp_le_expNegSum_seven
#print axioms KernelR.Circuit.InverterGate.gate_silence
#print axioms KernelR.Circuit.InverterGate.gate_firing
#print axioms KernelR.Circuit.InverterGate.Instance9901.silenceAfterK3
#print axioms KernelR.Circuit.InverterGate.Instance9901.firingAfterK3
