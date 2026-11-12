import Teaching.SelectorReturn
import Lean.Util.CollectAxioms

/-! Audit every declaration in the two changed modules, including unused
axioms and private/generated declarations. Dependencies are checked transitively. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets := #[`Teaching.SelectorRead, `Teaching.SelectorReturn]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut modules : Nat := 0
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    if targets.contains mod then
      modules := modules + 1
      for name in data.constNames do
        let some info := env.constants.find? name | throwError "Missing declaration {name}"
        if info.isAxiom then throwError "Unexpected project axiom {name}"
        for ax in ← collectAxioms name do
          unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
        if info.isTheorem then theorems := theorems + 1
  if modules != 2 then throwError "Incomplete selector-return audit: {modules} modules"
  if theorems == 0 then throwError "No selector-return theorems found"
  logInfo m!"Selector-return audit passed: {checked} declarations, {theorems} theorems, {modules} modules."
