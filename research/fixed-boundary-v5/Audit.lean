import Model
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`FixedBoundaryV5).isPrefixOf (privateToUserName name) then
      if info.isAxiom then throwError "Unexpected fixed-boundary axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
      if info.isTheorem then theorems := theorems + 1
  for name in #[``FixedBoundaryV5.choose_certified,
      ``FixedBoundaryV5.kernel_certified, ``FixedBoundaryV5.fresh_bounds,
      ``FixedBoundaryV5.maximum_wait_formula, ``FixedBoundaryV5.segment_certificate,
      ``FixedBoundaryV5.step_preserves_entry, ``FixedBoundaryV5.execution_safe,
      ``FixedBoundaryV5.execution_length, ``FixedBoundaryV5.execution_clock,
      ``FixedBoundaryV5.every_horizon_covered, ``FixedBoundaryV5.exact_horizon_prefix,
      ``FixedBoundaryV5.horizon_cost_bound, ``FixedBoundaryV5.issued_decisions_within_horizon,
      ``FixedBoundaryV5.horizon_issued_cost_bound, ``FixedBoundaryV5.no_refusal_inside_boundary,
      ``FixedBoundaryV5.early_refill_selected, ``FixedBoundaryV5.prudent_one_tick,
      ``FixedBoundaryV5.measured_violation_sound, ``FixedBoundaryV5.measured_violation_refuses] do
    let some info := env.find? name | throwError "Missing required theorem {name}"
    unless info.isTheorem do throwError "Required declaration is not a theorem: {name}"
  if theorems < 137 then throwError "Incomplete fixed-boundary proof audit"
  logInfo m!"FixedBoundaryV5 audit: {checked} declarations, {theorems} theorems."
