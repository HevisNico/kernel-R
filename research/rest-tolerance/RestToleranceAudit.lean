import RestTolerance.Observed
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut modules := 0
  let mut declarations := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    if (`RestTolerance).isPrefixOf mod then
      modules := modules + 1
      for name in data.constNames do
        let some info := env.constants.find? name
          | throwError "Missing declaration {name}"
        if info.isAxiom then
          throwError "Unexpected project axiom {name}"
        for axiomName in ← collectAxioms name do
          unless allowed.contains axiomName do
            throwError "Unexpected axiom {axiomName} in {name}"
        declarations := declarations + 1
  if modules != 2 || declarations == 0 then
    throwError "Expected two RestTolerance modules with declarations"
  logInfo m!"Rest tolerance axiom audit checked {declarations} declarations in {modules} modules"
