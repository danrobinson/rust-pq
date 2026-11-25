import Armwide.CachedRoundTrip
import Armwide.CachedParallel

open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `LinuxNativeCacheRoundTrip [
    (`slhdsa.sha512.compress,`ArmStreamRust.sha512.compress),
    (`slhdsa.S512.compress_spec,`slhdsa.PlatformStream.arm512_block)]
    #[`slhdsa.CachedArm.seeded_roundtrip] [`Armwide,`Armplatform,`Cacheops,`Cachepath]

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `LinuxNativeCacheParallel [
    (`slhdsa.sha512.compress,`ArmStreamRust.sha512.compress),
    (`slhdsa.S512.compress_spec,`slhdsa.PlatformStream.arm512_block)]
    #[`ArmCachedParallel.CacheopsRust.cache.parallelSign.sha2_joined]
    [`Parallel,`Armwide,`Armplatform,`Cacheops,`Cachepath]
