import Shakebatch.WidthEightNamed
import Shakebatch.WidthEightOuterHosted

open Lean Elab Command
namespace slhdsa.WidthEight.Coverage

/- Inspect only executable definitions reachable from the statement. In
particular, referring to a primitive in a proof term cannot establish coverage. -/
private partial def visit (env : Environment) (declName : Name) : StateM NameSet Unit := do
  if (← get).contains declName then return
  modify (·.insert declName)
  let some idx := env.getModuleIdxFor? declName | return
  unless [`Buffered,`Fused,`Slhdsa,`Parallel,`Shakeopt,`Shakebatch,`Cachepath,`Cacheops,`Facade].any
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
      let hosted := if api == `WidthEightAppleAPI then `WidthEightApple else `WidthEightX86
      let ns := api ++ s
      let hw := if api == `WidthEightAppleAPI then `BufferedApple.slhdsa.Buffered.Host.apple else `BufferedX86.slhdsa.Buffered.Host.x86
      let subtree := if api == `WidthEightAppleAPI then `BufferedApple.slhdsa.Buffered.subtree else `BufferedX86.slhdsa.Buffered.subtree
      for op in [`sign_spec,`sign_deterministic_spec,`slh_sign_spec,`slh_sign_internal_spec] do
        reaches (ns ++ op) [hw,subtree,`slhdsa.Buffered.Full.leaves,`slhdsa.Fused.xmss_sign_batch,`slhdsa.Fused.xmss_sign_batch_loop2,
          `slhdsa.Fused.xmss_sign_batch_loop3,`slhdsa.Fused.xmss_sign_batch_loop5,hosted ++ `slhdsa.WidthEight.Fors.signature,
          `slhdsa.WidthEight.Platform.available,
          `slhdsa.NativeVerify.ActiveHash.short_active,`slhdsa.NativeVerify.ActiveHash.pair_active,
          `slhdsa.NativeVerify.ForsFused.fused,absorb]
      for op in [`verify_spec,`slh_verify_internal_spec,`slh_verify_spec] do
        reaches (ns ++ op) [`slhdsa.WidthEight.Platform.recovery,absorb]
      let key := if api == `WidthEightAppleAPI then `KeygenAppleHashes.slhdsa.ParallelKeygenHost.ShNode.engine else `KeygenX86Hashes.slhdsa.ParallelKeygenHost.ShNode.engine
      reaches (ns ++ `seeded_roundtrip) [key,hw,subtree,`slhdsa.Buffered.Full.leaves,`slhdsa.ParallelKeygenHost.Sh.shake.slh.slh_keygen_internal,
        `slhdsa.Fused.xmss_sign_batch,hosted ++ `slhdsa.WidthEight.Fors.signature,absorb]

end slhdsa.WidthEight.Coverage
