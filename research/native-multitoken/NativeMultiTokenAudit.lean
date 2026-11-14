import NativeMultiTokenTarget
import NativeMultiTokenMilestone
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut modules : Nat := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    if mod == `NativeMultiTokenTarget || mod == `NativeMultiTokenMilestone then
      modules := modules + 1
      for name in data.constNames do
        let some info := env.constants.find? name
          | throwError "Missing declaration {name}"
        if info.isAxiom then
          throwError "Unexpected native multi-token axiom {name}"
        for axiomName in ← collectAxioms name do
          unless allowed.contains axiomName do
            throwError "Unexpected axiom {axiomName} in {name}"
        count := count + 1
  if modules != 2 || count == 0 then
    throwError "Expected both native multi-token modules in the audit"
  for result in #[``NetworkStability.NativeMultiToken.guarded_conjuncts,
      ``NetworkStability.NativeMultiToken.scalar_latency,
      ``NetworkStability.NativeMultiToken.training_silence] do
    let some (.thmInfo _) := env.constants.find? result
      | throwError "Missing milestone theorem {result}"
  let some (.defnInfo target) := env.constants.find?
    ``NetworkStability.NativeMultiToken.NativeMultiTokenRefinement
    | throwError "Missing frozen refinement definition"
  unless target.type == .sort .zero do
    throwError "The frozen refinement definition must have type Prop"
  logInfo m!"Audited {count} native multi-token declarations"
