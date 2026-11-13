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
    if (`Sky130Supervisor).isPrefixOf (privateToUserName name) then
      if info.isAxiom then throwError "Unexpected project axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
      if info.isTheorem then theorems := theorems + 1
  for name in #[``Sky130Supervisor.capacity_respects_both,
      ``Sky130Supervisor.observation_encloses,
      ``Sky130Supervisor.choose_certified,
      ``Sky130Supervisor.maintenance_guard_is_mandatory,
      ``Sky130Supervisor.maintenance_no_overflow,
      ``Sky130Supervisor.segment_safe,
      ``Sky130Supervisor.step_safe,
      ``Sky130Supervisor.run_invariant,
      ``Sky130Supervisor.every_service_safe,
      ``Sky130Supervisor.every_boundary_respects_semantic_capacity,
      ``Sky130Supervisor.no_refusal_in_enclosed_domain,
      ``Sky130Supervisor.refined_zero_failed_services,
      ``Sky130Supervisor.preparation_cost_exact,
      ``Sky130Supervisor.preparation_progress,
      ``Sky130Supervisor.preparation_budget,
      ``Sky130Supervisor.entry_certificate_valid,
      ``Sky130Supervisor.guarded_preparation_step,
      ``Sky130Supervisor.preparation_trace_respects_capacity,
      ``Sky130Supervisor.certified_preparation_respects_capacity,
      ``Sky130Supervisor.preparation_silence_is_not_a_service,
      ``Sky130Supervisor.preparation_cost_is_charged,
      ``Sky130Supervisor.maintenance_count_bounded,
      ``Sky130Supervisor.total_run_cost_contains_preparation,
      ``Sky130Supervisor.actual_run_cost_bounded,
      ``Sky130Supervisor.certified_entry_run_safe,
      ``Sky130Supervisor.measured_loss_violation_sound,
      ``Sky130Supervisor.observed_violation_refuses,
      ``Sky130Supervisor.no_false_alarm_inside_boundary] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    unless info.isTheorem do throwError "Required declaration is not a theorem: {name}"
  if theorems < 142 then throwError "Incomplete conditional supervisor audit"
  logInfo m!"Sky130Supervisor audit: {checked} declarations, {theorems} theorem declarations."
