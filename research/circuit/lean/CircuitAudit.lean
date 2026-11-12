import CircuitTiming
import CircuitNeed
import Training.WideDoseRead
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let roots := #[`CircuitBridge, `CircuitRobustness, `CircuitTiming, `CircuitNeed,
    `Search.VariableNeedTolerance, `Training.WideDoseRead]
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  let mut modules : Nat := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    if roots.contains mod then
      modules := modules + 1
      for name in data.constNames do
        let some info := env.constants.find? name
          | throwError "Missing declaration {name}"
        if info.isAxiom then throwError "Unexpected project axiom {name}"
        for ax in ← collectAxioms name do
          unless allowed.contains ax do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
        if info.isTheorem then theorems := theorems + 1
  if modules != roots.size then throwError "Only {modules} bridge modules found"
  if theorems < 26 then throwError "Only {theorems} bridge theorems found"
  logInfo m!"Circuit bridge audit passed: {checked} declarations in {modules} modules (coverage, including generated auxiliaries)."

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
#print axioms KernelR.Circuit.ChargeWindow.actual_dose_error
#print axioms KernelR.Circuit.ChargeWindow.actual_protected_drift
#print axioms KernelR.Circuit.leaky_response_error
#print axioms KernelR.Circuit.robust_first_crossing
#print axioms KernelR.Circuit.contact_time_error
#print axioms KernelR.Circuit.robust_first_crossing_with_latency
#print axioms KernelR.Circuit.current_error_first_crossing
#print axioms KernelR.Circuit.grazing_contact_counterexample
#print axioms RecursiveLearning.Native.needAlong_of_variable_doses
#print axioms KernelR.Circuit.needAlong_of_circuit_residual
#print axioms KernelR.Circuit.needAlong_of_circuit_residual_and_handoff
#print axioms RecursiveLearning.Native.stopped_pair_read_latency_wide
#print axioms RecursiveLearning.Native.stopped_pair_read_skew_wide
#print axioms RecursiveLearning.Native.wide_pair_dates_decide_lag

#print axioms RecursiveLearning.Native.stopped_read_latency_two_thirds_wide
#print axioms RecursiveLearning.Native.stopped_read_skew_two_thirds_wide

#print axioms KernelR.Circuit.needAlong_of_circuit_tolerances
