import Armwide.RoundTrip
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let internal := #[`slhdsa.NativeArmSignature.slh_sign_internal_spec,
                    `slhdsa.NativeArmSignature.slh_verify_internal_spec]
  let publicRoots := ArmPlatformProof.contextRoots.map (`ArmSdk.AppleContext.SegmentedSdk ++ ·)
  PlatformProof.replay `LinuxArmSdk [
    (`slhdsa.sha512.compress,`ArmStreamRust.sha512.compress),
    (`slhdsa.S512.compress_spec,`slhdsa.PlatformStream.arm512_block)]
    (internal ++ publicRoots ++ NativeArmApi.internalRoots.map (`ArmInternal ++ ·)
      ++ NativeArmApi.profiles.map (fun s => `NativeArmApi ++ s ++ `roundTrip)
      ++ NativeArmApi.keyRoots.map (`ArmKeys ++ ·) ++ NativeArmApi.sessionRoots.map (`ArmSession ++ ·)) [`Armwide]
