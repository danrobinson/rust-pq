import Shakebatch.PortablePublic
open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let roots := PlatformProof.shakeApiRoots.filter (fun n =>
    [`sign_spec, `sign_deterministic_spec, `verify_spec, `slh_sign_spec, `slh_verify_spec].contains
      (Name.mkSimple n.getString!))
  PlatformProof.replay `PortableSegmented
    (PlatformProof.spongeBindings `slhdsa.PlatformShake `ShakeAbsRust ++
      [(`shake256.Sponge, `ShakeAbsRust.shake256.Sponge)])
    ((roots ++ #[`slhdsa.Shake.api_sign_spec, `slhdsa.Shake.api_sign_deterministic_spec,
      `slhdsa.Shake.api_verify_spec]).map (`SegmentedPublic ++ ·)) [`Shakeopt]
