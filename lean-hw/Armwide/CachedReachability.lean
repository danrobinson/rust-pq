import Armwide.CachedTargets

open Lean Elab Command
namespace slhdsa.CachedArm.Audit

/- Inspect only executable definitions reachable from the statement. In
particular, referring to a primitive in a proof term cannot establish coverage. -/
private partial def visit (env : Environment) (declName : Name) : StateM NameSet Unit := do
  if (← get).contains declName then return
  modify (·.insert declName)
  let some idx := env.getModuleIdxFor? declName | return
  unless [`Slhdsa,`Armwide,`Armplatform,`Armstream,`Cacheops,`Cachepath,`Segmented,`Segmentedapi].any
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
      throwError "cached signing statement {root} does not reach {declName}"

run_cmd liftCoreM do
  let hashes := [`ArmStreamRust.sha256.sha256_from,`ArmStreamRust.sha512.sha512_from]
  reaches `slhdsa.CachedArm.digest hashes
  let native := [`slhdsa.ArmForsTree.Entry.fors.fors_sign,`slhdsa.WideFors.dispatch,
    `slhdsa.Armwide.Public.Dispatcher.wots.wots_sign,`slhdsa.Armwide.XmssLeaves.Signer.xmss.xmss_sign,
    `slhdsa.Armwide.Hypertree.xmss.xmss_pk_from_sig]
  reaches `slhdsa.CachedArm.keygen_sign_stream (hashes ++ native)
  reaches `slhdsa.CachedArm.seeded_roundtrip (hashes ++ native ++ [
    `ArmSdk.AppleContext.slhdsa.SegmentedApi.Program.slh.slh_verify])
  reaches `LinuxNativeCacheParallel.ArmCachedParallel.CacheopsRust.cache.parallelSign.sha2_joined [`ArmStreamRust.sha512.compress]
  reaches `LinuxNativeCache.slhdsa.CachedArm.keygen_sign_stream (hashes ++ [`ArmStreamRust.sha512.compress])
  reaches `LinuxNativeCacheRoundTrip.slhdsa.CachedArm.seeded_roundtrip (hashes ++ [
    `ArmStreamRust.sha512.compress,
    `LinuxNativeCacheRoundTrip.ArmSdk.AppleContext.slhdsa.SegmentedApi.Program.slh.slh_verify])

end slhdsa.CachedArm.Audit
