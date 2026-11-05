import KernelR.TrustedHeadline
import KernelR.TrustedBaseChecker

/-! Explicit review allowlist for the headline's statement semantics.

The checker computes its closure independently of this list. Proof values are
not mathematical assumptions of the statement and are checked separately by
Lean and Audit.lean. An incomplete list fails the build. The checked list is explicit, rather
than inferred from the theorem and accepted automatically.
-/
namespace KernelR.TrustedBase
open Lean
set_option maxHeartbeats 8000000

def trustedDeclarations : List Name := [
  `KernelR.Chain.pathJitter,
  `KernelR.Hybrid.AuxMode,
  `KernelR.Hybrid.BeforeGuards,
  `KernelR.Hybrid.BirthState,
  `KernelR.Hybrid.CellOrbitGerm,
  `KernelR.Hybrid.CellRightCrossing,
  `KernelR.Hybrid.CompleteThrough,
  `KernelR.Hybrid.Coord,
  `KernelR.Hybrid.CrossingCompleteThrough,
  `KernelR.Hybrid.CrossingExecution,
  `KernelR.Hybrid.Delivery,
  `KernelR.Hybrid.Delivery.head,
  `KernelR.Hybrid.Delivery.succ,
  `KernelR.Hybrid.Execution,
  `KernelR.Hybrid.Execution.emissionTimes,
  `KernelR.Hybrid.Execution.ledger,
  `KernelR.Hybrid.Execution.toWeak,
  `KernelR.Hybrid.Flow,
  `KernelR.Hybrid.Flow.ledger,
  `KernelR.Hybrid.Flow.toWeak,
  `KernelR.Hybrid.InRelativeBox,
  `KernelR.Hybrid.Jump,
  `KernelR.Hybrid.Jump.CrossingLeft,
  `KernelR.Hybrid.Jump.CrossingRight,
  `KernelR.Hybrid.Jump.ledger,
  `KernelR.Hybrid.Ledger,
  `KernelR.Hybrid.Ledger.add,
  `KernelR.Hybrid.Ledger.zero,
  `KernelR.Hybrid.MainMode,
  `KernelR.Hybrid.Move,
  `KernelR.Hybrid.Move.ledger,
  `KernelR.Hybrid.Parameters,
  `KernelR.Hybrid.PhysicalBox,
  `KernelR.Hybrid.PhysicalInvariant,
  `KernelR.Hybrid.Port,
  `KernelR.Hybrid.ReadyCoordinates,
  `KernelR.Hybrid.RestBand,
  `KernelR.Hybrid.Router,
  `KernelR.Hybrid.Snapshot,
  `KernelR.Hybrid.Snapshot.ObservationalEq,
  `KernelR.Hybrid.Snapshot.prependQueued,
  `KernelR.Hybrid.Snapshot.prependQuiet,
  `KernelR.Hybrid.Snapshot.requeue,
  `KernelR.Hybrid.UniversalCadenceOutcome,
  `KernelR.Hybrid.UpperRegion,
  `KernelR.Hybrid.Values,
  `KernelR.Hybrid.WeakBeforeGuards,
  `KernelR.Hybrid.WeakExecution,
  `KernelR.Hybrid.WeakExecution.CrossingFrom,
  `KernelR.Hybrid.WeakExecution.LeftBelow,
  `KernelR.Hybrid.WeakExecution.append,
  `KernelR.Hybrid.WeakExecution.emissionTimes,
  `KernelR.Hybrid.WeakExecution.ledger,
  `KernelR.Hybrid.WeakFlow,
  `KernelR.Hybrid.WeakFlow.LeftApproach,
  `KernelR.Hybrid.WeakFlow.ledger,
  `KernelR.Hybrid.WeakMove,
  `KernelR.Hybrid.WeakMove.ledger,
  `KernelR.Hybrid.a,
  `KernelR.Hybrid.appendPending,
  `KernelR.Hybrid.auxDrain,
  `KernelR.Hybrid.auxUpper,
  `KernelR.Hybrid.cadenceActivePort,
  `KernelR.Hybrid.cadenceChainTerminal,
  `KernelR.Hybrid.current,
  `KernelR.Hybrid.drive,
  `KernelR.Hybrid.errorAct,
  `KernelR.Hybrid.explicitFiniteChainRouter,
  `KernelR.Hybrid.familyPreparationBornSource,
  `KernelR.Hybrid.field,
  `KernelR.Hybrid.finiteCadenceTerminal,
  `KernelR.Hybrid.finiteChainPreparationCount,
  `KernelR.Hybrid.finiteChainPreparationPort,
  `KernelR.Hybrid.independentFamilySource,
  `KernelR.Hybrid.independentHeadQueue,
  `KernelR.Hybrid.markAct,
  `KernelR.Hybrid.nominalGain,
  `KernelR.Hybrid.pulse,
  `KernelR.Hybrid.response,
  `KernelR.Hybrid.setAux,
  `KernelR.Hybrid.setMain,
  `KernelR.Hybrid.setRaw,
  `KernelR.Hybrid.sourceTrain,
  `KernelR.Hybrid.work
]

private def locationFields (name : Name) : MetaM (List (String × Json)) := do
  let moduleName := (← findModuleOf? name).getD (← getEnv).mainModule
  let some ranges ← findDeclarationRanges? name
    | throwError "No generated source location for trusted declaration {name}"
  let first := ranges.selectionRange.pos.line
  let last := max first (if ranges.range.endPos.column == 0 then
    ranges.range.endPos.line - 1 else ranges.range.endPos.line)
  return [
    ("name", toJson name.toString), ("module", toJson moduleName.toString),
    ("file", toJson ("proof/lean/" ++ moduleName.toString.replace "." "/" ++ ".lean")),
    ("line", toJson first), ("end_line", toJson last)]

private def location (name : Name) : MetaM Json := do
  return Json.mkObj (← locationFields name)

/-- Export the checked reading list using Lean's declaration-name metadata.
The Python renderer records source hashes and selects a fixed Git commit. -/
def manifest : MetaM Json := do
  let report ← TrustedBaseChecker.check
    `KernelR.Hybrid.TrustedHeadline.every_finite_chain trustedDeclarations
  let env ← getEnv
  let mut entries : Array Json := #[]
  for name in trustedDeclarations do
    let fields ← locationFields name
    let support := report.declarations.toArray.filter fun declaration =>
      declaration != name && TrustedBaseChecker.parent env declaration == name
    let support := support.qsort (fun a b => a.toString < b.toString)
    entries := entries.push (Json.mkObj (fields ++ [
      ("auxiliaries", Json.arr (support.map fun declaration =>
        Json.mkObj [("name", toJson declaration.toString)]))]))
  return Json.mkObj [
    ("headline", ← location `KernelR.Hybrid.TrustedHeadline.every_finite_chain),
    ("trusted", Json.arr entries),
    ("traversal", toJson "Statement types, computational definition values, data-type interfaces and attributed compiler auxiliaries; proof values and pinned libraries are leaves.")]

open Elab Command in
run_cmd liftTermElabM do
  let report ← TrustedBaseChecker.check
    `KernelR.Hybrid.TrustedHeadline.every_finite_chain trustedDeclarations
  logInfo m!"Trusted statement check passed: {report.parents.toArray.size} semantic parents."

end KernelR.TrustedBase
