import Cachepath.BuiltSession
import Armplatform.Internal
import X86platform.Fors
import Portableplatform.Public

/-! Kernel-replay the cached digest signer with the same backend implementations
and primitive proofs used by the platform-specific public SHA-2 APIs. -/
open Lean Elab Command

namespace Cachepath.PlatformSha2

def roots := #[`slhdsa.cache.endtoend.sign_from_digest_with_cache_spec,
  `CacheopsRust.Public.sign_cached_spec, `CacheopsRust.Public.sign_deterministic_cached_spec,
  `CacheopsRust.Public.sign_cached_mut_spec, `CacheopsRust.Public.sign_deterministic_cached_mut_spec,
  `CacheopsRust.Public.new_then_sign, `CacheopsRust.Public.new_then_sign_many,
  `CacheopsRust.Public.scalar_build_and_sign_many]

def modules := [`Cacheops, `Cachepath]

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `AppleCached ArmPlatformProof.armReplacements roots modules
  PlatformProof.replay `X86Cached X86Platform.calls roots modules
  PlatformProof.replay `PortableCached PortablePlatform.kernels roots modules

end Cachepath.PlatformSha2
