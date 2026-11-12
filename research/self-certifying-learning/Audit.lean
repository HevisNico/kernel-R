import SelfCertifyingLearning
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Audit every declaration originating in a project module, regardless of
namespace, including private and compiler-generated declarations. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut candidates : NameSet := {}
  let mut modules : Nat := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    if (`SelfCertifyingLearning).isPrefixOf mod then
      modules := modules + 1
      for name in data.constNames do
        candidates := candidates.insert name
  for data in env.header.moduleData do
    for name in data.constNames do
      if (`SelfCertifyingLearning).isPrefixOf (privateToUserName name) &&
          !candidates.contains name then
        throwError "Project declaration outside audited modules: {name}"
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for name in candidates.toArray do
    let some info := env.constants.find? name
      | throwError "Missing declaration {name}"
    if info.isAxiom then throwError "Unexpected project axiom {name}"
    for ax in ← collectAxioms name do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    checked := checked + 1
    if info.isTheorem then theorems := theorems + 1
  if modules != 17 then throwError "Expected seventeen project modules, found {modules}"
  if theorems == 0 then throwError "No project theorems found"
  logInfo m!"SelfCertifyingLearning audit: {checked} declarations, {theorems} theorems, {modules} modules."
