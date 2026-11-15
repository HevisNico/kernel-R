import Recognition
import TwoLayerTarget

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`Target, `Recognition, `TwoLayerTarget]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains env.header.moduleNames[idx.toNat]! do continue
      if info.isAxiom then throwError "Unexpected learned-coincidence axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
  let theoremName := ``LearnedCoincidence.learned_coincidence_recognition
  let some info := env.find? theoremName | throwError "Missing theorem {theoremName}"
  unless info.isTheorem do throwError "Expected a theorem: {theoremName}"
  logInfo m!"Learned coincidence audit passed."
