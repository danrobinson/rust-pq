import Shakebatch.WidthEightNamed

open Lean Elab Command
namespace slhdsa.WidthEight.Coverage

/- Inspect only executable definitions reachable from the statement. In
particular, referring to a primitive in a proof term cannot establish coverage. -/
private partial def visit (env : Environment) (declName : Name) : StateM NameSet Unit := do
  if (← get).contains declName then return
  modify (·.insert declName)
  let some idx := env.getModuleIdxFor? declName | return
  unless [`Slhdsa,`Parallel,`Shakeopt,`Shakebatch,`Cachepath,`Cacheops,`Facade].any
    (·.isPrefixOf env.header.moduleNames[idx]!) do return
  if let some (.defnInfo d) := env.find? declName then
    for child in d.value.getUsedConstants do visit env child

private def reaches (root : Name) (expected : List Name) : CoreM Unit := do
  let env ← getEnv
  let info ← getConstInfo root
  let start := match info with
    | .defnInfo _ => #[root]
    | _ => info.type.getUsedConstants.toList.toArray
  let (_, reached) := (start.forM (visit env)).run {}
  for declName in expected do
    unless reached.contains declName do
      throwError "width-eight public statement {root} does not reach {declName}; candidates: {reached.toList.filter (fun n => n.toString.endsWith declName.getString!)}"

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for s in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for (api,absorb) in [(`WidthEightAppleAPI,`AppleSingleStream.KappleouterRust.shake256.Sponge.absorb),
        (`WidthEightX86API,`KxouterRust.shake256.Sponge.absorb)] do
      let ns := api ++ s
      for op in [`sign_spec,`sign_deterministic_spec] do
        reaches (ns ++ op) [`ParallelFusedSignature.sign,`Shakeopt.ForsWideSignature.signature,
          `slhdsa.WidthEight.Platform.available,absorb]
      reaches (ns ++ `verify_spec) [`slhdsa.WidthEight.Platform.recovery,absorb]
      reaches (ns ++ `seeded_roundtrip) [`slhdsa.ParallelKeygenHost.Sh.shake.slh.slh_keygen_internal,
        `ParallelFusedSignature.sign,`Shakeopt.ForsWideSignature.signature,absorb]

end slhdsa.WidthEight.Coverage
