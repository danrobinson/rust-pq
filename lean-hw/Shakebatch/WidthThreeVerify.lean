import Shakebatch.WidthThreeLinux
open Aeneas Aeneas.Std Result

namespace slhdsa.WidthThree
noncomputable section
noncomputable abbrev verifiedFors := @LinuxNativeRecovery.slhdsa.NativeVerify.linuxRecovery.fors
noncomputable abbrev verifiedForsSpec := @LinuxNativeRecovery.slhdsa.NativeVerify.linuxRecovery.fors_spec
noncomputable abbrev verifiedXmss := @WidthThreeLinuxSDK.CacheopsRust.NativeVerifier.xmssPk LinuxNativeRecovery.slhdsa.NativeVerify.linuxRecovery
noncomputable abbrev verifiedXmssSpec := @WidthThreeLinuxSDK.CacheopsRust.NativeVerifier.xmssSpec LinuxNativeRecovery.slhdsa.NativeVerify.linuxRecovery
end
end slhdsa.WidthThree

open Lean Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  -- Use the host-sponge XMSS climb and the native WOTS recovery kernel.
  let pairs := Cachepath.NativeHashReplay.bindings `KspongeLRust `slhdsa.ShakeBatch.Linux
  let mut roots := #[]
  for setName in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`verify_spec,`slh_verify_spec,`slh_verify_internal_spec] do
      let base := `slhdsa ++ setName ++ op
      roots := roots.push (if (← getEnv).contains (`SegmentedPublic ++ base) then `SegmentedPublic ++ base else base)
    for op in ["_verify","_verify_with_context"] do
      roots := roots.push (`slh_dsa ++ Name.mkSimple (setName.toString ++ op))
  PlatformProof.replay `WidthThreeVerifySDK (pairs ++ [
    (`slhdsa.shake.fors.fors_pk_from_sig,`slhdsa.WidthThree.verifiedFors),
    (`slhdsa.Shake.fors_verify_spec,`slhdsa.WidthThree.verifiedForsSpec),
    (`slhdsa.shake.xmss.xmss_pk_from_sig,`slhdsa.WidthThree.verifiedXmss),
    (`slhdsa.Shake.xmss_pk_from_sig_spec,`slhdsa.WidthThree.verifiedXmssSpec)])
    roots [`Cachepath,`Shakeopt]
