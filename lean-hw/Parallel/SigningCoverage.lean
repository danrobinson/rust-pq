import Lean
open Lean
namespace slhdsa.ParallelSigning.Coverage

private partial def visit (env : Environment) (declName : Name) : StateM NameSet Unit := do
  if (←get).contains declName then return
  modify (·.insert declName)
  let some idx := env.getModuleIdxFor? declName | return
  unless [`Buffered,`Parallel,`Shakebatch,`Shakeopt,`Slhdsa,`Facade,`Cachepath,`Fused].any (·.isPrefixOf env.header.moduleNames[idx]!) do return
  if let some (.defnInfo d) := env.find? declName then
    for child in d.value.getUsedConstants do visit env child

def reaches (root : Name) (required : List Name) : CoreM Unit := do
  let env ← getEnv
  let info ← getConstInfo root
  let (_,seen) := (info.type.getUsedConstants.toList.forM (visit env)).run {}
  for child in required do
    unless seen.contains child do throwError "{root} does not reach {child}. Candidates: {seen.toList.filter (fun n => n.toString.endsWith child.getString!)}"

def excludes (root bad : Name) : CoreM Unit := do
  let env ← getEnv
  let info ← getConstInfo root
  let (_,seen) := (info.type.getUsedConstants.toList.forM (visit env)).run {}
  if seen.contains bad then throwError "{root} still consumes the projected WOTS output {bad}"

end slhdsa.ParallelSigning.Coverage
