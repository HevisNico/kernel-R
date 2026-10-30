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
  for (name, info) in env.constants.toList do
    if ((`KernelR).isPrefixOf name || (`A22).isPrefixOf name) && info.isTheorem then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  if checked == 0 then throwError "No project theorems found"
  logInfo m!"Axiom audit passed: {checked} project theorems; only propext, Classical.choice and Quot.sound allowed."
