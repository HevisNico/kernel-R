import Teaching.NativeLearning
import Teaching.Feedback
import Teaching.LessonProbe
import Teaching.RoutedLesson
import Teaching.Dispatch
import Teaching.SelectorProtection
import Teaching.SelectorRead
import Teaching.SelectorReturnAudit
import Teaching.SelectorReprepareAudit
import Teaching.SelectorRoundAudit
import Teaching.SelectorPrecharge
import Teaching.TeacherReopen
import Teaching.TeacherStableClock
import Teaching.FrozenWorkFlow
import Teaching.CappedWorkRun
import Teaching.TeacherCappedCycle
import Teaching.CappedDispatch
import Teaching.NativeLesson
import Teaching.NativeAcceptance
import Teaching.AcceptanceDispatch
import Teaching.SerialAcceptance
import Teaching.LearnerReadout
import Teaching.ReadoutSeries
import Teaching.LearnerConjunction
import Teaching.LearnerFanIn
import Teaching.ScheduledGates
import Teaching.ScheduledCircuit
import Teaching.ReportFormula
import Teaching.ScheduledCommit
import Teaching.ScheduledProgram
import Thresholds.ThresholdProbe
import Thresholds.AdaptiveRounds
import Thresholds.CalibratedDecisionTree
import Thresholds.BlindNeedSearch
import Thresholds.PolicyReuse
import Thresholds.ThresholdTolerance
import Thresholds.TolerantErrorDose
import Thresholds.ErrorReadHandoff
import Thresholds.LiveErrorExpiry
import Thresholds.TrainingRead
import Thresholds.ParameterFuturePort
import Thresholds.ParameterTraining
import Coincidence.CoincidenceTiming
import Coincidence.TimedCurrentSeparation
import Coincidence.ParameterExecutionProduct
import Coincidence.CoincidenceReadTail
import Coincidence.CoincidenceNetworkContract
import Coincidence.CoincidenceLocalExecution
import Coincidence.CoincidenceProtectedTail
import Coincidence.CoincidenceSeparation
import Coincidence.OffsetAndDelay
import Training.StopLearningLatency
import Training.WideDoseRead
import Training.NativeStopLearning
import Training.SilentStep
import Training.Refractory
import Training.FiringStep
import Training.TrainingLoop
import Training.Driven
import Training.JointRead
import Training.TrainedCoincidence
import Training.ReadLag
import Network.FamilyProduct
import Network.RoutedProduct
import Network.FreeRead
import Network.AcyclicNetwork
import Network.WiredNetwork
import Network.SignalNetwork
import Search.SelfCalibratedProbe
import Search.SearchCells
import Search.TrainedSearch
import Search.NeedTolerance
import Search.VariableNeedTolerance
import Search.AsymmetricNeedTolerance
import Search.SearchActions
import Search.BisectionSearch
import Search.SuccessiveSearch
import Lean.Util.CollectAxioms

set_option maxHeartbeats 8000000

/-!
Axiom audit of the native package.

The scope is every declaration added by a module of this package (the six
folders imported above) or of the parent package `RecursiveLearning`,
whatever its namespace: private declarations and the auxiliary declarations
Lean generates (equation lemmas, `match` and proof helpers) included. A
declaration in the `RecursiveLearning` namespace that comes from any other
module is an error, so the scope cannot silently miss one.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let roots : List Name :=
    [`RecursiveLearning, `Teaching, `Thresholds, `Coincidence, `Training, `Network, `Search]
  let mut candidates : NameSet := {}
  let mut modules : Nat := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    if roots.any (·.isPrefixOf mod) then
      modules := modules + 1
      for name in data.constNames do
        candidates := candidates.insert name
  for data in env.header.moduleData do
    for name in data.constNames do
      if (`RecursiveLearning).isPrefixOf (privateToUserName name) && !candidates.contains name then
        throwError "{name} is in the RecursiveLearning namespace but outside the audited modules"
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for name in candidates.toArray do
    let some info := env.constants.find? name
      | throwError "Missing declaration {name}"
    if info.isAxiom then
      throwError "Unexpected project axiom {name}"
    for ax in ← collectAxioms name do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    checked := checked + 1
    if info.isTheorem then theorems := theorems + 1
  if modules < 85 then throwError "Only {modules} project modules found"
  if theorems == 0 then throwError "No project theorems found"
  logInfo m!"Native audit passed for {checked} declarations from {modules} modules, including {theorems} theorems."
