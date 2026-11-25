import Cachepath.Sha2Seeded
import Cachepath.PlatformSha2
import X86platform.Public

open Lean Elab Command

set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `X86Sha2Session (X86Platform.calls ++ [
    (`PortableMessage.slhdsa.SegmentedApi.Program.slh.slh_verify,
     `X86Message.slhdsa.SegmentedApi.Program.slh.slh_verify),
    (`PortableMessage.slhdsa.SegmentedApi.verify_spec, `X86Message.slhdsa.SegmentedApi.verify_spec)])
    #[`CacheopsRust.Public.sha2_seeded_roundtrip] (Cachepath.PlatformSha2.modules ++ [`Shakeopt])

/- The same complete session for the two Arm configurations in which wide dispatch is disabled. -/
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `AppleSha2Verifier ArmPlatformProof.armReplacements #[`slhdsa.SegmentedApi.verify_spec]
  PlatformProof.replay `AppleSha2Session (ArmPlatformProof.armReplacements ++ [
    (`PortableMessage.slhdsa.SegmentedApi.Program.slh.slh_verify,
     `AppleSha2Verifier.slhdsa.SegmentedApi.Program.slh.slh_verify),
    (`PortableMessage.slhdsa.SegmentedApi.verify_spec, `AppleSha2Verifier.slhdsa.SegmentedApi.verify_spec)])
    #[`CacheopsRust.Public.sha2_seeded_roundtrip] (Cachepath.PlatformSha2.modules ++ [`Shakeopt])
