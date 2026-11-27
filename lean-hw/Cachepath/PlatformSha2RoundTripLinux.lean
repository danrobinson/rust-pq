import Cachepath.PlatformSha2RoundTrip
import Cachepath.PlatformSha2Linux
open Lean Elab Command

set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `LinuxSha2Session [
    (`slhdsa.sha512.compress, `ArmStreamRust.sha512.compress),
    (`slhdsa.S512.compress_spec, `slhdsa.PlatformStream.arm512_block)]
    #[`AppleSha2Session.CacheopsRust.Public.sha2_seeded_roundtrip]
    (Cachepath.PlatformSha2.modules ++ [`Shakeopt])

-- Verify the concrete functions named in the final theorem statements and link the
-- signers and builders to the independently source-checked platform replays.
run_cmd liftCoreM do
  for (session, builder, signer, verifier) in [
    (`X86Sha2Session.CacheopsRust.Public.sha2_seeded_roundtrip,
     `X86Sha2Session.slhdsa.cache.sha2_ops.build_xmss_tree,
     `X86Sha2Session.CacheopsRust.Public.cache.sign_cached, `X86Message.slhdsa.SegmentedApi.Program.slh.slh_verify),
    (`AppleSha2Session.CacheopsRust.Public.sha2_seeded_roundtrip,
     `slhdsa.cache.sha2_ops.build_xmss_tree, `AppleSha2Session.CacheopsRust.Public.cache.sign_cached,
     `AppleSha2Verifier.slhdsa.SegmentedApi.Program.slh.slh_verify),
    (`LinuxSha2Session.AppleSha2Session.CacheopsRust.Public.sha2_seeded_roundtrip,
     `LinuxSha2Session.slhdsa.cache.sha2_ops.build_xmss_tree,
     `LinuxSha2Session.AppleSha2Session.CacheopsRust.Public.cache.sign_cached,
     `LinuxSha2Session.AppleSha2Verifier.slhdsa.SegmentedApi.Program.slh.slh_verify)] do
    let info ← getConstInfo session
    unless [builder, signer, verifier].all info.type.getUsedConstants.contains do
      throwError "incorrect implementation in seeded round-trip theorem {session}"

example : @X86Sha2Session.CacheopsRust.Public.cache.sign_cached = @X86Cached.CacheopsRust.Public.cache.sign_cached := rfl
example : @AppleSha2Session.CacheopsRust.Public.cache.sign_cached = @AppleCached.CacheopsRust.Public.cache.sign_cached := rfl
example : @LinuxSha2Session.AppleSha2Session.CacheopsRust.Public.cache.sign_cached = @LinuxArmCached.AppleCached.CacheopsRust.Public.cache.sign_cached := rfl
example : @X86Sha2Session.slhdsa.cache.sha2_ops.build_xmss_tree = @X86Cached.slhdsa.cache.sha2_ops.build_xmss_tree := rfl
example : @LinuxSha2Session.slhdsa.cache.sha2_ops.build_xmss_tree = @LinuxArmCached.slhdsa.cache.sha2_ops.build_xmss_tree := rfl
