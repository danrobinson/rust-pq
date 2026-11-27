import Cachepath.PlatformSha2
import Cachepath.KeygenVerify

/-! Replay both hash families together with the implementations selected on portable targets. -/
open Lean Elab Command

set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replayWithContracts `PortableSession
    (PortablePlatform.kernels ++ PlatformProof.spongeBindings `slhdsa.PlatformShake `ShakeAbsRust ++
      [(`slhdsa.shake256.Sponge.mk, `ShakeAbsRust.shake256.Sponge.mk),
       (`shake256.Sponge, `ShakeAbsRust.shake256.Sponge)])
    [`CacheopsRust.Closed.FastSpec, `CacheopsRust.Closed.DispatchCorrect]
    #[`CacheopsRust.Public.scalar_build_and_sign_many, `CacheopsRust.Public.scalar_keygen_then_sign_many,
      `CacheopsRust.Public.scalar_keygen_sign_verify, `CacheopsRust.Public.scalar_keygen_sign_verify_with_precompute] (Cachepath.PlatformSha2.modules ++ [`Shakeopt])
