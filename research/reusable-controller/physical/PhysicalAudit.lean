import PhysicalEvaluator
import Lean.Util.CollectAxioms

set_option maxHeartbeats 8000000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : List Name := [`PhysicalEvaluator, `ReusableController, `RecursiveLearning,
    `Search, `Teaching, `Thresholds, `Training, `Coincidence, `Network, `KernelR]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut candidates : NameSet := {}
  let mut modules : Nat := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    if roots.any (·.isPrefixOf mod) then
      modules := modules + 1
      for name in data.constNames do
        candidates := candidates.insert name
  let mut theorems : Nat := 0
  for name in candidates.toArray do
    let some info := env.constants.find? name | throwError "Missing declaration {name}"
    if info.isAxiom then throwError "Unexpected project axiom {name}"
    for ax in ← collectAxioms name do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
    if info.isTheorem then theorems := theorems + 1
  if modules < 174 then throwError "Incomplete physical module audit: {modules}"
  logInfo m!"Physical audit passed: {candidates.size} declarations, {theorems} theorems, {modules} modules."
