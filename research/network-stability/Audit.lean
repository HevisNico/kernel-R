import Counterexample
import NativeReciprocal
import RoutedCalendarExamples
import FeedbackExamples
import PerpetualExamples
import ScheduleCounterexample
import ScheduleExamples
import PortMemory
import FairnessExamples
import ConcreteFairness
import NativeEndpoint
import MarkCounterexample
import NativeComposition
import DatedReplay
import DatedFairness
import ReciprocalDated
import DatedTrainingControl
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`ChipFiring, `GuardedFeedback, `Counterexample, `NativeReciprocal,
    `RoutedCalendar, `RoutedCalendarExamples, `AutonomousFeedback, `FeedbackExamples,
    `PerpetualFeedback, `PerpetualExamples, `ScheduleCounterexample,
    `ScheduleConfluence, `ScheduleExamples,
    `FairMemory, `NetworkTheorem, `PortMemory, `FairnessExamples,
    `ConcreteFairness, `NativeEndpoint, `MarkFeedback, `MarkCounterexample, `NativeMarkTrace, `NativeRefinement,
    `PhaseAdmission, `NativeAdmissions, `NativeTransactions, `DatedFairness, `NativeTiming,
    `NativeWireTransactions, `NativeComposition, `DatedReplay, `ReciprocalClosure, `DatedNetwork, `DatedTrainingControl,
    `ReciprocalLearning, `ReciprocalReverseRows, `ReciprocalDated]
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
      ``NetworkStability.AutonomousFeedback.ScheduleCounterexample.both_orders_have_margins,
      ``NetworkStability.AutonomousFeedback.Schedule.different_cells_commute,
      ``NetworkStability.AutonomousFeedback.Schedule.exact_queue_order_can_differ,
      ``NetworkStability.AutonomousFeedback.Schedule.local_diamond,
      ``NetworkStability.AutonomousFeedback.Schedule.newman,
      ``NetworkStability.AutonomousFeedback.Schedule.terminal_memory_unique,
      ``NetworkStability.AutonomousFeedback.Schedule.certified_terminal_memory_unique,
      ``NetworkStability.AutonomousFeedback.Schedule.finite_prefix_confluence,
      ``NetworkStability.AutonomousFeedback.Schedule.write_closed_memory_unique,
      ``NetworkStability.AutonomousFeedback.Schedule.counterexample_violates_A,
      ``NetworkStability.AutonomousFeedback.Schedule.counterexample_violates_B,
      ``NetworkStability.AutonomousFeedback.Schedule.uniform_ring_order_independent,
      ``NetworkStability.AutonomousFeedback.Schedule.network_memory,
      ``NetworkStability.AutonomousFeedback.Schedule.fair_limit_unique,
      ``NetworkStability.AutonomousFeedback.Schedule.starved_is_unfair,
      ``NetworkStability.AutonomousFeedback.Schedule.starvation_model_has_diamonds,
      ``NetworkStability.AutonomousFeedback.Schedule.different_stable_memories_without_fairness,
      ``NetworkStability.AutonomousFeedback.Schedule.PortMemory.per_port_bounds,
      ``NetworkStability.AutonomousFeedback.Schedule.PortMemory.both_ports_and_recovery_can_be_pending,
      ``NetworkStability.AutonomousFeedback.Schedule.PortMemory.per_port_terminal_unique,
      ``NetworkStability.AutonomousFeedback.Schedule.PortMemory.per_port_fair_limit_unique,
      ``NetworkStability.AutonomousFeedback.Schedule.fifo_write_fair,
      ``NetworkStability.AutonomousFeedback.Schedule.noisy_fifo_write_fair,
      ``NetworkStability.NativeReciprocal.nominal_endpoint_exists,
      ``NetworkStability.NativeReciprocal.reciprocal_tokens,
      ``NetworkStability.NativeReciprocal.reciprocal_flow_headroom,
      ``NetworkStability.NativeReciprocal.rail_contact_control,
      ``NetworkStability.NativeReciprocal.uncertified_threshold_control,
      ``NetworkStability.NativeReciprocal.recovery_requires_non_fire_update,
      ``NetworkStability.NativeReciprocal.endpoint_ledger_does_not_replay_fire,
      ``NetworkStability.MarkFeedback.network_memory,
      ``NetworkStability.MarkFeedback.newman,
      ``NetworkStability.MarkFeedback.fifo_write_fair,
      ``NetworkStability.MarkFeedback.Control.distinct_terminal_memories,
      ``NetworkStability.MarkFeedback.Control.fifo_misses_reachable_write,
      ``NetworkStability.NativeReciprocal.reciprocal_native_event_words,
      ``NetworkStability.NativeReciprocal.positive_mark_requires_elapsed_time,
      ``NetworkStability.NativeReciprocal.forward_receiver_prefix,
      ``NetworkStability.NativeReciprocal.nominal_full_dated_replay,
      ``NetworkStability.NativeReciprocal.nominal_settled_exclusivity_fails,
      ``NetworkStability.NativeReciprocal.ProtectedReceipt.no_fixed_input_replay,
      ``NetworkStability.NativeReciprocal.ProtectedReceipt.recovery_dose,
      ``NetworkStability.NativeReciprocal.nominal_staged_dose_balance,
      ``NetworkStability.NativeReciprocal.ProtectedReceipt.certified_pair,
      ``NetworkStability.NativeReciprocal.certified_opposite_decisions_need_different_read_laws,
      ``NetworkStability.PhaseAdmission.network_memory,
      ``NetworkStability.PhaseAdmission.tied_occurrences_commute,
      ``NetworkStability.PhaseAdmission.Trace.chronological,
      ``NetworkStability.PhaseAdmission.Trace.zero_error_replay,
      ``NetworkStability.PhaseAdmission.Trace.rank_bound,
      ``NetworkStability.PhaseAdmission.ReopenRace.coincident_reopening_different_memory,
      ``NetworkStability.PhaseAdmission.ReopenRace.strict_gap_forces_same_first_action,
      ``NetworkStability.NativeReciprocal.nominal_admission_words,
      ``NetworkStability.NativeReciprocal.recordedMode_recovers_admission,
      ``NetworkStability.NativeReciprocal.ProtectedReceipt.dated_pair,
      ``NetworkStability.NativeReciprocal.nominal_forward_sender_transactions,
      ``NetworkStability.NativeReciprocal.nominal_reverse_sender_transactions,
      ``NetworkStability.NativeReciprocal.prepared_pulse_zero_doses,
      ``NetworkStability.NativeReciprocal.PreparedTransactions.responses,
      ``NetworkStability.PhaseAdmission.earliest_write_fair,
      ``NetworkStability.PhaseAdmission.earliest_limit_unique,
      ``NetworkStability.PhaseAdmission.clears_of_sublevel_budget,
      ``NetworkStability.PhaseAdmission.clears_of_locally_finite_service,
      ``NetworkStability.PhaseAdmission.Starvation.earliest_starves,
      ``NetworkStability.PhaseAdmission.Starvation.calendar_diamond,
      ``NetworkStability.NativeReciprocal.predicted_phase_after_fire,
      ``NetworkStability.NativeReciprocal.third_forward_predicted_slow,
      ``NetworkStability.NativeReciprocal.PreparedTransactions.return_windows,
      ``NetworkStability.NativeReciprocal.forward_receiver_transactions,
      ``NetworkStability.NativeReciprocal.reverse_receiver_transactions,
      ``NetworkStability.NativeReciprocal.birth_sender_transactions,
      ``NetworkStability.NativeReciprocal.nominal_composed_cuts,
      ``NetworkStability.PhaseAdmission.TransactionReplay.trace,
      ``NetworkStability.PhaseAdmission.TransactionReplay.append,
      ``NetworkStability.PhaseAdmission.replay_network_memory,
      ``NetworkStability.PhaseAdmission.Trace.through,
      ``NetworkStability.PhaseAdmission.through_terminal_unique,
      ``NetworkStability.NativeReciprocal.first_strong_birth_token_queued,
      ``NetworkStability.NativeReciprocal.birth_first_strong_native_certificate,
      ``NetworkStability.NativeReciprocal.birth_training_prefix_no_global_diamond,
      ``NetworkStability.PhaseAdmission.TieAdmissible.of_global,
      ``NetworkStability.PhaseAdmission.local_tie_diamond,
      ``NetworkStability.PhaseAdmission.dated_terminal_unique,
      ``NetworkStability.PhaseAdmission.dated_horizon_unique,
      ``NetworkStability.PhaseAdmission.dated_write_fair,
      ``NetworkStability.PhaseAdmission.dated_limit_unique,
      ``NetworkStability.PhaseAdmission.dated_noisy_safe,
      ``NetworkStability.PhaseAdmission.dated_network_memory,
      ``NetworkStability.NativeReciprocal.training_rejects_global,
      ``NetworkStability.NativeReciprocal.training_dates_replay,
      ``NetworkStability.NativeReciprocal.training_dated_memory,
      ``NetworkStability.NativeReciprocal.birth_weak_rows,
      ``NetworkStability.NativeReciprocal.feedback_weak_rows,
      ``NetworkStability.NativeReciprocal.first_forward_weak_row,
      ``NetworkStability.NativeReciprocal.first_reverse_weak_row,
      ``NetworkStability.NativeReciprocal.birth_protected_row,
      ``NetworkStability.NativeReciprocal.feedback_strong_row,
      ``NetworkStability.NativeReciprocal.forward_sender_entry_rows,
      ``NetworkStability.NativeReciprocal.reverse_entry_exact_boundary,
      ``NetworkStability.NativeReciprocal.reciprocal_route_has_tie_room,
      ``NetworkStability.NativeReciprocal.reciprocal_clipped_ties,
      ``NetworkStability.NativeReciprocal.reciprocal_rank_certificate,
      ``NetworkStability.NativeReciprocal.reciprocal_reserve_certificate,
      ``NetworkStability.NativeReciprocal.reciprocal_replay_network] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    unless info.isTheorem do throwError "Required declaration is not a theorem: {name}"
  logInfo m!"Network stability audit: {count} theorems."
