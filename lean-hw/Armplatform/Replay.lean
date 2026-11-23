import Lean

/-! Reuse proof terms for a platform whose extracted definitions differ at a small
number of verified interfaces. Lean's kernel type-checks every rebuilt definition
and theorem after substituting the platform implementations and their lemmas. -/
namespace PlatformProof
open Lean Elab Command

private abbrev Renaming := Std.HashMap Name (Name × Bool)

/-- Only this temporary free variable can occur in a rebuilt closed declaration.
It is abstracted over the explicit hypothesis before the kernel admits the declaration. -/
private def premiseVar : Expr := mkFVar ⟨`platformPremise⟩

private def substitute (names : Renaming) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => (names.get? n).map (fun (target, needsPremise) =>
      let replacement := mkConst target us
      if needsPremise then mkApp replacement premiseVar else replacement)
    | _ => none

private partial def rebuild (destination : Name) (source : Name) (names : IO.Ref Renaming) (premise : Option Name) :
    CoreM Name := do
  if let some target := (← names.get).get? source then return target.1
  let env ← getEnv
  -- Only declarations compiled from the library and its proofs can refer to
  -- a library implementation. Imported arithmetic and Aeneas remain shared.
  let some idx := env.getModuleIdxFor? source | return source
  let origin := env.header.moduleNames[idx]!
  unless [`Slhdsa, `Armplatform, `Segmented, `Segmentedapi, `Platformadapter, `Facade, `Shakebatch].any (·.isPrefixOf origin) do return source
  let info ← getConstInfo source
  let some body := info.value? true | return source
  let mut changed := false
  for n in info.type.getUsedConstants ++ body.getUsedConstants do
    if (← rebuild destination n names premise) != n then changed := true
  unless changed do
    names.modify (·.insert source (source, false))
    return source
  let target := destination ++ source
  let map ← names.get
  let type := substitute map info.type
  let value := substitute map body
  let conditional := type.hasFVar || value.hasFVar
  let (type, value) ← if conditional then do
    let some law := premise | throwError "missing explicit replay hypothesis"
    let domain := mkConst law
    pure (Lean.mkForall `platformPremise .default domain (type.abstract #[premiseVar]),
          Lean.mkLambda `platformPremise .default domain (value.abstract #[premiseVar]))
  else pure (type, value)
  let decl ← match info with
    | .defnInfo d => pure <| .defnDecl {d with name := target, type, value, all := [target]}
    | .thmInfo t => pure <| .thmDecl {t with name := target, type, value, all := [target]}
    | _ => throwError "unsupported declaration in proof replay: {source}"
  addDecl decl
  names.modify (·.insert source (target, conditional))
  return target

/-- Rebuild all declarations needed by the specified roots with the specified
substitutions. Unaffected roots receive a checked alias under the new namespace. -/
private def replayCore (destination : Name) (premise : Option Name)
    (replacements : List (Name × (Name × Bool))) (roots : Array Name) : CoreM Unit := do
  let names ← IO.mkRef (Std.HashMap.ofList replacements)
  for root in roots do
    let target ← rebuild destination root names premise
    if target == root then
      let info ← getConstInfo root
      let value := mkConst root (info.levelParams.map Level.param)
      addDecl <| .thmDecl { name := destination ++ root
                            type := info.type
                            levelParams := info.levelParams
                            value := value }

def replay (destination : Name) (replacements : List (Name × Name)) (roots : Array Name) : CoreM Unit :=
  replayCore destination none (replacements.map fun (old, new) => (old, new, false)) roots

/-- Parameterize exactly those rebuilt theorems that use one of the conditional
bindings. Implementations and other unrelated proofs keep their original types. -/
def replayAssuming (destination law : Name) (ordinary conditional : List (Name × Name))
    (roots : Array Name) : CoreM Unit :=
  replayCore destination (some law)
    ((ordinary.map fun (old, new) => (old, new, false)) ++
      (conditional.map fun (old, new) => (old, new, true))) roots

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
