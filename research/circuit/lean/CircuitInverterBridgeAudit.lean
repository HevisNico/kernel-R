import CircuitInverterBoxReference
import CircuitInverterExpBounds
import Lean.Util.CollectAxioms

/-! Audit of the bridge's analytic pieces (box reference in closed form, its peak,
rational bounds of `exp`): no project axiom, and only `propext`,
`Classical.choice` and `Quot.sound`. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`CircuitInverterBoxReference, `CircuitInverterExpBounds]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains env.header.moduleNames[idx.toNat]! do continue
      if info.isAxiom then throwError "Unexpected bridge axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  logInfo m!"Bridge pieces audit passed: {checked} declarations."

#print axioms KernelR.Circuit.box_reference_eq
#print axioms KernelR.Circuit.box_closed_le_peak
#print axioms KernelR.Circuit.box_closed_before
#print axioms KernelR.Circuit.box_help_abs_integral_le
#print axioms KernelR.Circuit.expNegTaylor_eq
#print axioms KernelR.Circuit.exp_neg_rat_bounds
