import Counterexample
import NativeReciprocal
import RoutedCalendarExamples
import FeedbackExamples
import PerpetualExamples
import ScheduleCounterexample
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`ChipFiring, `GuardedFeedback, `Counterexample, `NativeReciprocal,
    `RoutedCalendar, `RoutedCalendarExamples, `AutonomousFeedback, `FeedbackExamples,
    `PerpetualFeedback, `PerpetualExamples, `ScheduleCounterexample]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless modules.contains (env.header.moduleNames[idx.toNat]!) do continue
    if info.isAxiom then throwError "Unexpected network stability axiom {name}"
    for ax in ← collectAxioms name do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    if info.isTheorem then count := count + 1
  for name in #[``NetworkStability.ChipFiring.stabilize,
      ``NetworkStability.ChipFiring.memory_bound,
      ``NetworkStability.ChipFiring.weighted_budget,
      ``NetworkStability.Control.no_reachable_terminal,
      ``NetworkStability.Control.exceeds_any_ceiling,
      ``NetworkStability.GuardedFeedback.different_terminal_needs,
      ``NetworkStability.GuardedFeedback.episode_eq_of_margins,
      ``NetworkStability.NativeReciprocal.nominal_reciprocal_epoch,
      ``NetworkStability.RoutedCalendar.certified_episode,
      ``NetworkStability.RoutedCalendar.full_load_window,
      ``NetworkStability.RoutedCalendar.structural_episode,
      ``NetworkStability.RoutedCalendar.structural_sound,
      ``NetworkStability.RoutedCalendar.recovers_three_probe_model,
      ``NetworkStability.RoutedCalendar.handshake_correct,
      ``NetworkStability.RoutedCalendar.removing_return_changes_memory,
      ``NetworkStability.AutonomousFeedback.certified_feedback,
      ``NetworkStability.AutonomousFeedback.loop_does_not_terminate,
      ``NetworkStability.AutonomousFeedback.loop_has_no_strict_margin,
      ``NetworkStability.AutonomousFeedback.loop_accepts_zero_margin,
      ``NetworkStability.AutonomousFeedback.drive_disables_write,
      ``NetworkStability.AutonomousFeedback.Ring.ring_edges,
      ``NetworkStability.AutonomousFeedback.Ring.uniform_and,
      ``NetworkStability.AutonomousFeedback.reserve_prefix,
      ``NetworkStability.AutonomousFeedback.memory_stabilizes,
      ``NetworkStability.AutonomousFeedback.strict_probe_rank,
      ``NetworkStability.AutonomousFeedback.loop_memory_forever,
      ``NetworkStability.AutonomousFeedback.RecirculatingRing.one_write_then_perpetual,
      ``NetworkStability.AutonomousFeedback.ScheduleCounterexample.different_terminal_memory,
      ``NetworkStability.AutonomousFeedback.ScheduleCounterexample.both_orders_have_margins] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    unless info.isTheorem do throwError "Required declaration is not a theorem: {name}"
  logInfo m!"Network stability audit: {count} theorems."
