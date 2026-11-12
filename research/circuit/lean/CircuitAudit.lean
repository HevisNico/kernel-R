import CircuitBridge
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    if mod == `CircuitBridge then
      for name in data.constNames do
        let some info := env.constants.find? name
          | throwError "Missing declaration {name}"
        if info.isAxiom then throwError "Unexpected project axiom {name}"
        for ax in ← collectAxioms name do
          unless allowed.contains ax do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
        if info.isTheorem then theorems := theorems + 1
  if theorems < 13 then throwError "Only {theorems} bridge theorems found"
  logInfo m!"Circuit bridge audit passed: {checked} declarations, {theorems} theorems."

#print axioms KernelR.Circuit.ChargeWindow.balance
#print axioms KernelR.Circuit.ChargeWindow.calibrated_gain
#print axioms KernelR.Circuit.ChargeWindow.exposed_dose
#print axioms KernelR.Circuit.ChargeWindow.protected_step
#print axioms KernelR.Circuit.ChargeWindow.dose_error
#print axioms KernelR.Circuit.ChargeWindow.protected_drift
#print axioms KernelR.Circuit.ChargeWindow.capacitor_dose
#print axioms KernelR.Circuit.ChargeWindow.kernel_dose_projection
#print axioms KernelR.Circuit.ChargeWindow.nominal_kernel_dose
#print axioms KernelR.Circuit.design_dose
#print axioms KernelR.Circuit.design_dose_below_read_budget
#print axioms KernelR.Circuit.common_offset_cancels
#print axioms KernelR.Circuit.accumulated_error
