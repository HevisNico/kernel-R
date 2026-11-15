import CircuitNetwork
import DatedOrder
import Instances
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`CircuitNetwork, `DatedOrder, `Instances]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains (env.header.moduleNames[idx.toNat]!) do continue
      if info.isAxiom then throwError "Unexpected axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      if info.isTheorem then count := count + 1
  for name in #[``NetworkStability.CircuitNetwork.certificate,
      ``NetworkStability.CircuitNetwork.circuit_certified,
      ``NetworkStability.CircuitNetwork.nominal_of_port,
      ``NetworkStability.CircuitNetwork.circuit_predicted,
      ``NetworkStability.PortOrder.terminal_unique,
      ``NetworkStability.PortOrder.noisy_exact,
      ``NetworkStability.PortOrder.dated_run_eq_queue_run,
      ``NetworkStability.PortOrder.dated_run_exists,
      ``NetworkStability.CircuitNetwork.circuit_dated_predicted,
      ``NetworkStability.CircuitNetwork.circuit_dated_eq_queue,
      ``NetworkStability.CircuitNetwork.circuit_dated_run_exists] do
    unless env.contains name do throwError "Missing {name}"
  logInfo m!"network circuit: {count} theorems, axioms within propext, Classical.choice, Quot.sound"
