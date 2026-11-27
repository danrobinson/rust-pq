import Armwide.CachedSession
import Cachepath.PlatformSha2Linux

open Lean Elab Command

/- Linux AArch64 may use its SHA-512 instruction path when initializing the
hash context or processing a scalar compression tail. Recheck the complete
native cached signer with this target-specific primitive installed. -/
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `LinuxNativeCache [
    (`slhdsa.sha512.compress,`ArmStreamRust.sha512.compress),
    (`slhdsa.S512.compress_spec,`slhdsa.PlatformStream.arm512_block)]
    #[`slhdsa.CachedArm.sign_from_digest_spec,`slhdsa.CachedArm.sign_from_digest_with_cache_spec,
      `ArmCachedApi.CacheopsRust.Public.sign_cached_spec,`ArmCachedApi.CacheopsRust.Public.sign_deterministic_cached_spec,
      `ArmCachedApi.CacheopsRust.Public.sign_cached_mut_spec,`ArmCachedApi.CacheopsRust.Public.sign_deterministic_cached_mut_spec,
      `slhdsa.CachedArm.keygen_sign_stream]
    [`Armwide,`Armplatform,`Cacheops,`Cachepath]
