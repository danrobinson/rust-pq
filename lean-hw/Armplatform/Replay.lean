import Lean

/-! Reuse proof terms for a platform whose extracted definitions differ at a small
number of verified interfaces. Lean's kernel type-checks every rebuilt definition
and theorem after substituting the platform implementations and their lemmas. -/
namespace PlatformProof
open Lean Elab Command

private abbrev Renaming := Std.HashMap Name Name

private partial def substitute (names : Renaming) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => (names.get? n).map (fun target => .const target us)
    | .proj n i val => (names.get? n).bind fun target =>
        if target == n then none else some (.proj target i (substitute names val))
    | _ => none

private partial def rebuild (extraModules : List Name) (destination : Name) (source : Name) (names : IO.Ref Renaming) :
    CoreM Name := do
  if let some target := (← names.get).get? source then return target
  let env ← getEnv
  -- Only declarations compiled from the library and its proofs can refer to
  -- a library implementation. Imported arithmetic and Aeneas remain shared.
  let some idx := env.getModuleIdxFor? source | return source
  let origin := env.header.moduleNames[idx]!
  unless (extraModules ++ [`Slhdsa, `Armplatform, `Segmented, `Segmentedapi, `Platformadapter, `Facade, `Shakebatch]).any (·.isPrefixOf origin) do return source
  let info ← getConstInfo source
  let some body := info.value? true | return source
  let mut changed := false
  for n in info.type.getUsedConstants ++ body.getUsedConstants do
    if (← rebuild extraModules destination n names) != n then changed := true
  unless changed do
    names.modify (·.insert source source)
    return source
  let target := destination ++ source
  let map ← names.get
  let type := substitute map info.type
  let value := substitute map body
  let decl ← match info with
    | .defnInfo d => pure <| .defnDecl {d with name := target, type, value, all := [target]}
    | .thmInfo t => pure <| .thmDecl {t with name := target, type, value, all := [target]}
    | _ => throwError "unsupported declaration in proof replay: {source}"
  addDecl decl
  names.modify (·.insert source target)
  return target

/-- Rebuild all declarations needed by the specified roots with the specified
substitutions. Unaffected roots receive a checked alias under the new namespace. -/
def replay (destination : Name) (replacements : List (Name × Name)) (roots : Array Name) (extraModules : List Name := []) : CoreM Unit := do
  let names ← IO.mkRef (Std.HashMap.ofList replacements)
  for root in roots do
    let target ← rebuild extraModules destination root names
    if target == root then
      let info ← getConstInfo root
      let value := mkConst root (info.levelParams.map Level.param)
      addDecl <| .thmDecl { name := destination ++ root
                            type := info.type
                            levelParams := info.levelParams
                            value := value }

/-- Replay record-valued implementation contracts whose fields mention the selected code.
The kernel checks the new constructor and generates its recursor before checking
the caller proofs. Records must be supplied in dependency order. -/
def replayWithContracts (destination : Name) (replacements : List (Name × Name))
    (contracts : List Name) (roots : Array Name) (modules : List Name) : CoreM Unit := do
  let names ← IO.mkRef (Std.HashMap.ofList replacements)
  for source in contracts do
    let .inductInfo info ← getConstInfo source | throwError "expected a contract record: {source}"
    if info.isRec || info.isUnsafe || info.all != [source] then
      throwError "expected a safe nonrecursive contract record: {source}"
    let [ctor] := info.ctors | throwError "expected one constructor: {source}"
    let c ← getConstInfo ctor
    for dep in info.type.getUsedConstants ++ c.type.getUsedConstants do
      if dep != source then
        discard <| rebuild modules destination dep names
    let target := destination ++ source
    names.modify fun m => ((m.insert source target).insert ctor (destination ++ ctor)).insert
      (source ++ `rec) (target ++ `rec)
    let m ← names.get
    addDecl <| .inductDecl info.levelParams info.numParams
      [{name := target, type := substitute m info.type,
        ctors := [{name := destination ++ ctor, type := substitute m c.type}]}] false
  replay destination (← names.get).toList roots modules

end PlatformProof

namespace PlatformProof
open Lean

/-- Attach an existing statement to the independently translated entry. The
kernel checks that the proof inhabits the statement with that entry substituted. -/
def bindEntry (theoremName previousEntry actualEntry actualTheorem : Name) : CoreM Unit := do
  let info ← getConstInfo theoremName
  unless info.type.getUsedConstants.contains previousEntry do
    throwError "the statement of {theoremName} does not mention {previousEntry}"
  let type := info.type.replace fun
    | .const n us => if n == previousEntry then some (.const actualEntry us) else none
    | _ => none
  addDecl <| .thmDecl { name := actualTheorem
                        levelParams := info.levelParams
                        type
                        value := mkConst theoremName (info.levelParams.map Level.param) }
end PlatformProof

namespace PlatformProof
open Lean Meta

/-- Transport a complete interface theorem across a proved equality of functions. -/
def transport (theoremName previousEntry actualEntry equality target : Name) : MetaM Unit := do
  let info ← getConstInfo theoremName
  unless info.type.getUsedConstants.contains previousEntry do
    throwError "{theoremName} does not mention {previousEntry}"
  let impl := mkConst actualEntry
  withLocalDeclD `implementation (← inferType impl) fun f => do
    let predicate ← mkLambdaFVars #[f] (info.type.replace fun
      | .const n _ => if n == previousEntry then some f else none
      | _ => none)
    let eq ← mkAppM ``congrArg #[predicate, mkConst equality]
    let proof ← mkAppM ``Eq.mp #[eq, mkConst theoremName (info.levelParams.map Level.param)]
    addDecl <| .thmDecl { name := target, type := (mkApp predicate impl).headBeta,
                          levelParams := info.levelParams, value := proof }
end PlatformProof
