import Armwide.CachedSignProgram
import Armwide.CachedSignReplay
open Aeneas Aeneas.Std Result slhdsa slhdsa.cache.endtoend CacheopsRust
namespace slhdsa.CachedArm
open slhdsa.Armwide.CachedSign (normalized_wots)
set_option allowUnsafeReducibility true in
attribute [local reducible] ArmCached.CacheopsRust.hash.seed_ctx ArmCached.CacheopsRust.wots.wots_sign ArmCached.CacheopsRust.fors.fors_sign ArmCached.CacheopsRust.fors.fors_pk_from_sig ArmCached.CacheopsRust.xmss.xmss_sign ArmCached.CacheopsRust.xmss.xmss_pk_from_sig
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

run_cmd Replay.emit "private theorem sign_from_digest_loop_spec" "/-- Extracted Rust `cache::sha2_ops::sign_from_digest`"
run_cmd Replay.emit "theorem sign_from_digest_spec {" "/-- End-to-end extracted pipeline composing `CacheValid`"
run_cmd Replay.emit "theorem sign_from_digest_with_cache_spec {" "/-! ## End-to-End Cached Hypertree"

end slhdsa.CachedArm
