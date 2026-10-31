import KernelR
import Lean.Util.CollectAxioms

set_option maxHeartbeats 8000000

/-! Fail if any project theorem depends on an axiom outside Lean's standard
logical foundations. This includes admitted proofs and native evaluation axioms. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  -- ModuleData.constNames contains every imported constant name. Inspecting
  -- names first avoids materializing all of Mathlib's ConstantInfo entries.
  -- Include stage 2 as well, so declarations added in this file are audited.
  let inScope := fun name => (`KernelR).isPrefixOf name || (`A22).isPrefixOf name
  let mut candidates : NameSet := {}
  for data in env.header.moduleData do
    for name in data.constNames do
      if inScope name then candidates := candidates.insert name
  candidates := env.constants.foldStage2
    (fun names name _ => if inScope name then names.insert name else names) candidates
  for name in candidates.toArray do
    let some info := env.constants.find? name
      | throwError "Missing declaration {name} in axiom audit"
    if info.isTheorem then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  if checked == 0 then throwError "No project theorems found"
  logInfo m!"Axiom audit passed: {checked} project theorems; only propext, Classical.choice and Quot.sound allowed."
