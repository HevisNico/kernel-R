import NativeMultiTokenTarget
import NativeMultiTokenMilestone
import SynchronizedProduct
import LaunchWave
import ProtectedReceipt
import PhysicalRefinement
import PrefixAccounting
import ReceiptProduct
import ReceiptTiming
import ReceiptWave
import LaunchReceiptChain
import TrainingClock
import TrainingStage
import GuardedReplay
import NativeHistory
import ExecutionCuts
import ExactNativeExecution
import ReceiptWindow
import NativeReceiptRows
import GuardedReceiptRows
import GuardedExternalRows
import ExactPrefixCorrespondence
import GuardedTraceWords
import NativeExternalRows
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut modules : Nat := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    if mod == `NativeMultiTokenTarget || mod == `NativeMultiTokenMilestone ||
        mod == `SynchronizedProduct || mod == `LaunchWave || mod == `ProtectedReceipt ||
        mod == `PhysicalRefinement || mod == `PrefixAccounting || mod == `ReceiptProduct ||
        mod == `ReceiptTiming || mod == `ReceiptWave || mod == `LaunchReceiptChain ||
        mod == `TrainingClock || mod == `TrainingStage || mod == `GuardedReplay ||
        mod == `NativeHistory || mod == `ExecutionCuts || mod == `ExactNativeExecution ||
        mod == `ReceiptWindow || mod == `NativeReceiptRows || mod == `GuardedReceiptRows ||
        mod == `GuardedExternalRows || mod == `ExactPrefixCorrespondence ||
        mod == `GuardedTraceWords || mod == `NativeExternalRows then
      modules := modules + 1
      for name in data.constNames do
        let some info := env.constants.find? name
          | throwError "Missing declaration {name}"
        if info.isAxiom then
          throwError "Unexpected native multi-token axiom {name}"
        for axiomName in ← collectAxioms name do
          unless allowed.contains axiomName do
            throwError "Unexpected axiom {axiomName} in {name}"
        count := count + 1
  if modules != 24 || count == 0 then
    throwError "Expected the target and all native multi-token proof modules in the audit"
  for result in #[``NetworkStability.NativeMultiToken.guarded_conjuncts,
      ``NetworkStability.NativeMultiToken.scalar_latency,
      ``NetworkStability.NativeMultiToken.training_silence,
      ``NetworkStability.NativeMultiToken.synchronized_ledger,
      ``NetworkStability.NativeMultiToken.weak_training_transaction,
      ``NetworkStability.NativeMultiToken.launch_wave,
      ``NetworkStability.NativeMultiToken.provisional_mark_recovery,
      ``NetworkStability.NativeMultiToken.protected_slow_admission,
      ``NetworkStability.NativeMultiToken.native_exact_execution,
      ``NetworkStability.NativeMultiToken.native_exact_admission_windows,
      ``NetworkStability.NativeMultiToken.native_exact_receipt_rows,
      ``NetworkStability.NativeMultiToken.guarded_receipt_replay,
      ``NetworkStability.NativeMultiToken.guarded_replay_in_native_receipt_order,
      ``NetworkStability.NativeMultiToken.exact_receipt_replay,
      ``NetworkStability.NativeMultiToken.exact_guarded_replay,
      ``NetworkStability.NativeMultiToken.external_row_matches,
      ``NetworkStability.NativeMultiToken.native_with_exact_guarded_replay,
      ``NetworkStability.NativeMultiToken.exact_prefix_correspondence,
      ``NetworkStability.NativeMultiToken.native_with_prefix_correspondence,
      ``NetworkStability.NativeMultiToken.native_exact_quiet_suffix,
      ``NetworkStability.NativeMultiToken.exact_training_row_doses,
      ``NetworkStability.NativeMultiToken.exact_launch_row_doses,
      ``NetworkStability.NativeMultiToken.guarded_trace_refinement,
      ``NetworkStability.NativeMultiToken.native_with_exact_row_doses,
      ``NetworkStability.NativeMultiToken.native_multi_token_refinement] do
    let some (.thmInfo _) := env.constants.find? result
      | throwError "Missing milestone theorem {result}"
  let some (.defnInfo target) := env.constants.find?
    ``NetworkStability.NativeMultiToken.NativeMultiTokenRefinement
    | throwError "Missing frozen refinement definition"
  unless target.type == .sort .zero do
    throwError "The frozen refinement definition must have type Prop"
  logInfo m!"Audited {count} native multi-token declarations"
