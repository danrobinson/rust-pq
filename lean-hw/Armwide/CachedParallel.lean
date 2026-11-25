import Armwide.CachedLinux
import Parallel.CacheJoinedCaller

open Lean Elab Command

/- The parallel-enabled extracted caller uses the native serial path when its
worker returns None. Its Some path consumes the joined ticket publication theorem. -/
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let bindings := [`hash.seed_ctx,`wots.wots_sign,`xmss.xmss_sign,`xmss.xmss_pk_from_sig,
    `fors.fors_sign,`fors.fors_pk_from_sig,`cache.sha2_ops.sign_from_digest_loop,
    `cache.sha2_ops.sign_from_digest].map fun n => (`CacheopsRust ++ n,`ArmCached.CacheopsRust ++ n)
  slhdsa.Armwide.Hypertree.replayFeatures `ArmCachedParallel
    ((`slhdsa.cache.endtoend.sign_from_digest_spec,`slhdsa.CachedArm.sign_from_digest_spec)::bindings)
    #[`CacheopsRust.cache.parallelSign.sha2_joined] [`Parallel]

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `LinuxNativeCacheParallel [
    (`slhdsa.sha512.compress,`ArmStreamRust.sha512.compress),
    (`slhdsa.S512.compress_spec,`slhdsa.PlatformStream.arm512_block)]
    #[`ArmCachedParallel.CacheopsRust.cache.parallelSign.sha2_joined]
    [`Parallel,`Armwide,`Armplatform,`Cacheops,`Cachepath]
