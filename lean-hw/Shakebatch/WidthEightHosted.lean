import Shakebatch.WidthEightPublic

open Lean Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let mut roots := #[]
  for setName in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`slh_sign_internal_spec,`slh_verify_internal_spec,`sign_spec,`sign_deterministic_spec,
               `verify_spec,`slh_sign_spec,`slh_verify_spec] do
      let base := `slhdsa ++ setName ++ op
      let root := if (← getEnv).contains (`SegmentedPublic ++ base) then `SegmentedPublic ++ base else base
      roots := roots.push (`WidthEightSDK ++ root)
  let apple ← Cachepath.NativeHashReplay.appleBindings
  for (target,pairs) in [(`WidthEightApple,apple),
      (`WidthEightX86,Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)] do
    PlatformProof.replay target pairs roots [`Cachepath,`Shakeopt,`Shakebatch]
    for fn in [`WidthEightSDK.ShakeoptSeg.shake.slh.slh_sign,`WidthEightSDK.ShakeoptSeg.shake.slh.slh_verify] do
      unless (← getEnv).contains (target ++ fn) do throwError "missing hosted sponge in {target ++ fn}"
