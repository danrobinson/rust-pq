import Armwide.CachedSign
import Cachepath.BuiltSession
import Cachepath.KeygenSession
import Armwide.XmssCacheBuilder

open Lean Elab Command
namespace slhdsa.CachedArm

/- Reuse the public cache-key, context, mutable update and eviction proofs with
the native digest signer installed in each caller. -/
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  Armwide.Hypertree.replayFeatures `ArmCachedApi [
    (`CacheopsRust.cache.sha2_ops.sign_from_digest,`ArmCached.CacheopsRust.cache.sha2_ops.sign_from_digest),
    (`slhdsa.cache.endtoend.sign_from_digest_spec,`slhdsa.CachedArm.sign_from_digest_spec),
    (`slhdsa.cache.endtoend.sign_from_digest_with_cache_spec,`slhdsa.CachedArm.sign_from_digest_with_cache_spec)]
    #[`CacheopsRust.Public.sign_cached_spec,`CacheopsRust.Public.sign_deterministic_cached_spec,
      `CacheopsRust.Public.sign_cached_mut_spec,`CacheopsRust.Public.sign_deterministic_cached_mut_spec,
      `CacheopsRust.Public.keygen_then_sign_many,
      `CacheopsRust.Public.new_then_sign,`CacheopsRust.Public.new_then_sign_many]
    [`Cacheops,`Cachepath]

end slhdsa.CachedArm
