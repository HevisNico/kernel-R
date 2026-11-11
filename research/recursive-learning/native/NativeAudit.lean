import Dispatch
import CappedDispatch
import ReportFormula
import BlindNeedSearch
import PolicyReuse
import CoincidenceSeparation
import StopLearningLatency
import NativeStopLearning
import SilentStep
import Refractory
import FiringStep
import TrainingLoop
import Driven
import JointRead
import TrainedCoincidence
import OffsetAndDelay
import SelfCalibratedProbe
import FamilyProduct
import RoutedProduct
import Cascade
import FreeRead
import AcyclicNetwork
import WiredNetwork
import Lean.Util.CollectAxioms

set_option maxHeartbeats 8000000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let inScope := fun name =>
    let userName := privateToUserName name
    (`RecursiveLearning).isPrefixOf userName ||
      [`KernelR.Hybrid.ParameterExecution.independentPair,
        `KernelR.Hybrid.ParameterCompleteThrough.independentPair].contains userName
  let mut candidates : NameSet := {}
  for data in env.header.moduleData do
    for name in data.constNames do
      if inScope name then candidates := candidates.insert name
  candidates := env.constants.foldStage2
    (fun names name _ => if inScope name then names.insert name else names) candidates
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
  if theorems == 0 then throwError "No project theorems found"
  logInfo m!"RecursiveLearning audit passed for {checked} declarations, including {theorems} theorems."
