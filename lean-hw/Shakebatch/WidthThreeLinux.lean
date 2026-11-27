import Shakebatch.WidthThreePublic
open Lean Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let pairs := Cachepath.NativeHashReplay.bindings `KspongeLRust `slhdsa.ShakeBatch.Linux
  PlatformProof.replay `WidthThreeLinux (pairs ++ [
    (`slhdsa.NativeVerify.linuxRecovery, `LinuxNativeRecovery.slhdsa.NativeVerify.linuxRecovery)])
    #[`slhdsa.WidthThree.parallel_sign_spec,`slhdsa.WidthThree.parallel_context_spec] [`Parallel,`Cachepath,`Shakeopt]

open Lean Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let mut roots := #[]
  for setName in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`keygen_spec,`slh_keygen_internal_spec,`slh_sign_internal_spec,`slh_verify_internal_spec,
               `sign_spec,`sign_deterministic_spec,`verify_spec,`slh_sign_spec,`slh_verify_spec] do
      let base := `slhdsa ++ setName ++ op
      let goal := if (← getEnv).contains (`SegmentedPublic ++ base) then `SegmentedPublic ++ base else base
      roots := roots.push (`WidthThreeSDK ++ goal)
  let pairs := Cachepath.NativeHashReplay.bindings `KspongeLRust `slhdsa.ShakeBatch.Linux
  PlatformProof.replay `WidthThreeLinuxSDK (pairs ++ [
    (`slhdsa.NativeVerify.linuxRecovery,`LinuxNativeRecovery.slhdsa.NativeVerify.linuxRecovery)])
    roots [`Cachepath,`Shakeopt]
  let mut compat := #[]
  for root in PlatformProof.shakeFacadeRoots do
    let param := `WidthThreeCompat ++ root
    if (← getEnv).contains param then compat := compat.push param
  PlatformProof.replay `WidthThreeLinuxCompat (pairs ++ [
    (`slhdsa.NativeVerify.linuxRecovery,`LinuxNativeRecovery.slhdsa.NativeVerify.linuxRecovery)])
    compat [`Cachepath,`Shakeopt]
  for entry in [`WidthThreeLinux.slhdsa.ParallelCaller.Sh.shake.slh.slh_sign_internal,
      `WidthThreeLinux.slhdsa.ParallelCaller.Sh.shake.slh.shake_sign_ctx,
      `WidthThreeLinuxSDK.WidthThreeSDK.SegmentedPublic.slhdsa.sets.shake_128s.sign,
      `WidthThreeLinuxSDK.WidthThreeSDK.slhdsa.sets.shake_128s.keygen] do
    unless (← getEnv).contains entry do throwError "missing native sponge in {entry}"
