import RingNetwork
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`RingNetwork]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains (env.header.moduleNames[idx.toNat]!) do continue
      if info.isAxiom then throwError "Unexpected axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      if info.isTheorem then count := count + 1
  for name in #[``NetworkStability.RingNetwork.certificate,
      ``NetworkStability.RingNetwork.ring_certified,
      ``NetworkStability.RingNetwork.ring_predicted,
      ``NetworkStability.RingNetwork.ring_port_shaped,
      ``NetworkStability.RingNetwork.ring_words,
      ``NetworkStability.RingNetwork.ring_dated_words,
      ``NetworkStability.RingNetwork.queue_any,
      ``NetworkStability.RingNetwork.ring_queue_words,
      ``NetworkStability.RingNetwork.nominal_own,
      ``NetworkStability.RingNetwork.nominal_ring] do
    unless env.contains name do throwError "Missing {name}"
  logInfo m!"ring network: {count} theorems, axioms within propext, Classical.choice, Quot.sound"
