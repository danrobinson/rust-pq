import Lean

/-! Kernel-checked specialization of the security proof to a different hash family.
Only the listed project modules can require rebuilding. -/
namespace ShakeProof
open Lean Elab Command

private abbrev Renaming := Std.HashMap Name Name

private def substitute (names : Renaming) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => (names.get? n).map (fun target => .const target us)
    | _ => none

private partial def rebuild (destination : Name) (source : Name) (names : IO.Ref Renaming) :
    CoreM Name := do
  if let some target := (← names.get).get? source then return target
  let env ← getEnv
  -- VCVio provides the same parameterized scheme and reduction for both families.
  let some idx := env.getModuleIdxFor? source | return source
  let origin := env.header.moduleNames[idx]!
  unless [`MLink, `ME2E, `MReduction].any (·.isPrefixOf origin) do return source
  let info ← getConstInfo source
  let some body := info.value? true | return source
  let mut changed := false
  for n in info.type.getUsedConstants ++ body.getUsedConstants do
    if (← rebuild destination n names) != n then changed := true
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
  try addDecl decl catch ex => throwError "{source}: {ex.toMessageData}"
  names.modify (·.insert source target)
  return target

/-- Rebuild all declarations needed by the specified roots with the specified
substitutions. Unaffected roots receive a checked alias under the new namespace. -/
def replay (destination : Name) (replacements : List (Name × Name)) (roots : Array Name) : CoreM Unit := do
  let names ← IO.mkRef (Std.HashMap.ofList replacements)
  for root in roots do
    let target ← rebuild destination root names
    if target == root then
      let info ← getConstInfo root
      let value := mkConst root (info.levelParams.map Level.param)
      addDecl <| .thmDecl { name := destination ++ root
                            type := info.type
                            levelParams := info.levelParams
                            value := value }

end ShakeProof
