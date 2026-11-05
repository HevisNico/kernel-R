import Lean

/-! Mechanical statement-dependency closure.

Start at a declaration's TYPE, never its proof. Follow constants in that
expression and, for reachable computational definitions, in their VALUES.
Proof terms (including proof arguments and theorem values) are not unfolded.
For each reachable inductive/structure also visit constructor and projection
types. Compiler-generated auxiliaries (recursors, matchers, equation lemmas,
`proof_n` helpers and constructor/projection support) are inspected by type
and attributed to their semantic parent; their computational values are
visited when applicable. Attribution does not skip dependency traversal.

Project declarations are identified by their defining module, not merely
their namespace. Imported Mathlib, Init, Std, Lean and their explicitly named
pinned dependency modules are leaves; unknown module roots fail closed as
project code. Every declaration from the current module is considered project
code, which also lets standalone negative controls introduce fresh names.
Only recognized compiler-support suffixes are folded into a parent: an
arbitrary user definition nested in a trusted namespace remains a new name.

This is a dependency/interface check, not a replacement for Lean's kernel
or the independent axiom audit. The list supplied to `check` must be explicit.
-/
namespace KernelR.TrustedBaseChecker
open Lean Meta

def projectModule (moduleName : Name) : Bool :=
  !(#[`Init, `Std, `Lean, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets,
      `ImportGraph, `LeanSearchClient, `Plausible, `Cli].any (·.isPrefixOf moduleName))

def projectConstant (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => true
  | some index => projectModule env.header.moduleNames[index.toNat]!

private def auxiliaryPart (part : String) : Bool :=
  part.startsWith "match_" || part.startsWith "proof_" ||
  part.startsWith "eq_" || part.startsWith "_eq_" || part.startsWith "_sizeOf_" ||
  part.startsWith "_sparseCasesOn_" ||
  #["rec", "recOn", "casesOn", "brecOn", "below", "ibelow", "noConfusion",
    "noConfusionType", "inj", "injEq", "inj_iff", "sizeOf_spec", "ctorIdx",
    "_unary", "_sunfold", "_unsafe_rec", "equations", "splitter", "eta",
    "ext", "ext_iff", "elim", "ctorElim", "ctorElimType", "_f", "decEq"].contains part

private def sameModule (env : Environment) (first second : Name) : Bool :=
  env.getModuleIdxFor? first == env.getModuleIdxFor? second

/-- Parent attribution is metadata-based for constructors and projections,
then uses only recognized compiler auxiliary suffixes. -/
partial def parent (env : Environment) (name : Name) : Name := Id.run do
  let user := privateToUserName name
  let own := if env.contains user then user else name
  if let some projection := env.getProjectionFnInfo? name then
    if let some (.ctorInfo constructor) := env.find? projection.ctorName then
      return parent env constructor.induct
  if let some info := env.find? name then
    match info with
    | .ctorInfo constructor => return parent env constructor.induct
    | .recInfo recursor =>
      if let some inductName := recursor.all.head? then return parent env inductName
    | .defnInfo definition =>
      if user.getString!.startsWith "instDecidableEq" then
        if let .app (.const `DecidableEq _) (.const inductName _) := definition.type then
          if sameModule env name inductName then
            if let some (.inductInfo _) := env.find? inductName then
              return parent env inductName
    | _ => pure ()
  match user with
  | .str stem suffix =>
    if suffix == "go" && stem.getString! == "brecOn" && sameModule env name stem then
      return parent env stem
    if auxiliaryPart suffix && env.contains stem && sameModule env name stem then
      return parent env stem
    if auxiliaryPart suffix then
      -- An equation auxiliary may be nested below a matcher auxiliary.
      let owner := parent env stem
      if env.contains owner && sameModule env name owner then return owner
    return own
  | .num stem _ =>
    let owner := parent env stem
    if env.contains owner && sameModule env name owner then return owner
    return own
  | _ => return own

private partial def semanticConstants (expression : Expr) : MetaM NameSet := do
  if ← isProof expression then return {}
  match expression with
  | .const name _ => return ({} : NameSet).insert name
  | .app function argument =>
    return (← semanticConstants function).merge (← semanticConstants argument)
  | .forallE name domain body binder =>
    let names ← semanticConstants domain
    withLocalDecl name binder domain fun localVar => do
      return names.merge (← semanticConstants (body.instantiate1 localVar))
  | .lam name domain body binder =>
    let names ← semanticConstants domain
    withLocalDecl name binder domain fun localVar => do
      return names.merge (← semanticConstants (body.instantiate1 localVar))
  | .letE name type value body _ =>
    let names := (← semanticConstants type).merge (← semanticConstants value)
    withLetDecl name type value fun localVar => do
      return names.merge (← semanticConstants (body.instantiate1 localVar))
  | .mdata _ body => semanticConstants body
  | .proj structName _ value =>
    return (← semanticConstants value).insert structName
  | _ => return {}

structure Closure where
  declarations : NameSet := {}
  parents : NameSet := {}
  deriving Inhabited

private def allProjectNames (env : Environment) : Array Name := Id.run do
  let mut names : NameSet := {}
  for index in [:env.header.moduleData.size] do
    if projectModule env.header.moduleNames[index]! then
      for name in env.header.moduleData[index]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if projectConstant env name then names.insert name else names) names
  return names.toArray

private def traverse (headline : Name) (allowed : Option (List Name)) : MetaM Closure := do
  let env ← getEnv
  let some root := env.find? headline | throwError "Unknown headline {headline}"
  let mut auxiliaries : NameMap (Array Name) := {}
  for name in allProjectNames env do
    let owner := parent env name
    if owner != privateToUserName name then
      auxiliaries := auxiliaries.insert owner ((auxiliaries.find? owner).getD #[] |>.push name)
  let mut pending := (← semanticConstants root.type).toArray
  let mut result : Closure := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if !projectConstant env name || result.declarations.contains name then continue
    let some info := env.find? name | throwError "Missing reachable declaration {name}"
    let owner := parent env name
    if let some trusted := allowed then
      unless trusted.contains owner do
        throwError "Untrusted statement dependencies: {[owner]}"
    result := { declarations := result.declarations.insert name,
                parents := result.parents.insert owner }
    pending := pending ++ (← semanticConstants info.type).toArray
    if let some support := auxiliaries.find? owner then pending := pending ++ support
    match info with
    | .defnInfo definition =>
      if !(← isProp definition.type) then
        pending := pending ++ (← semanticConstants definition.value).toArray
    | .opaqueInfo definition =>
      if !(← isProp definition.type) then
        pending := pending ++ (← semanticConstants definition.value).toArray
    | .inductInfo inductInfo =>
      pending := pending ++ inductInfo.ctors.toArray
      if let some recordInfo := getStructureInfo? env name then
        pending := pending ++ recordInfo.fieldInfo.map (·.projFn)
    | _ => pure ()
  return result

/-- Compute the complete closure independently of any allowlist. -/
def closure (headline : Name) : MetaM Closure := traverse headline none

/-- Reject missing allowlist names and every unlisted semantic parent. -/
def check (headline : Name) (trusted : List Name) : MetaM Closure := do
  let env ← getEnv
  for name in trusted do
    unless env.contains name do throwError "Trusted declaration does not exist: {name}"
  -- The traversal itself is unchanged; an unlisted parent permits immediate
  -- rejection without unfolding an arbitrarily large untrusted construction.
  traverse headline (some trusted)

end KernelR.TrustedBaseChecker
