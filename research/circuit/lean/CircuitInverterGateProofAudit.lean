import CircuitInverterGateInstance9901
import Lean.Util.CollectAxioms

/-! Audit of the single-source gate (`CircuitInverterGate`, core only), its bridge
(`CircuitInverterGateProof`) and seed 9901 on it (`CircuitInverterGateInstance9901`):
no project axiom, and only `propext`, `Classical.choice` and `Quot.sound`. The
earlier restatement (`CircuitInverterGateBridge`, `CircuitInverterGate9901`) is
superseded as an interface; it stays audited by `CircuitInverterGateAudit`. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`CircuitInverterGate, `CircuitInverterGateProof, `CircuitInverterGateInstance9901]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains env.header.moduleNames[idx.toNat]! do continue
      if info.isAxiom then throwError "Unexpected gate axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  logInfo m!"Single-source gate audit passed: {checked} declarations."

#print axioms KernelR.Circuit.Gate.gate_silence
#print axioms KernelR.Circuit.Gate.gate_firing
#print axioms KernelR.Circuit.Gate.Instance9901.stateBound
#print axioms KernelR.Circuit.Gate.Instance9901.silenceAfterK3
#print axioms KernelR.Circuit.Gate.Instance9901.firingAfterK3
