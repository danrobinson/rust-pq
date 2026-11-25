import Shakebatch.WidthEightTree
import Shakebatch.NativeFacade
namespace slhdsa.WidthEight
noncomputable section
abbrev htSign (host : Platform) := @WidthEightTree.slhdsa.shake.ht.ht_sign host
abbrev htSignSpec (host : Platform) := @WidthEightTree.slhdsa.Shake.ht_sign_spec host

open Lean Meta Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let mapping := [
    (`slhdsa.shake.fors.fors_sign,`slhdsa.WidthEight.forsSign),
    (`slhdsa.Shake.fors_sign_domain,`slhdsa.WidthEight.forsSign_spec),
    (`slhdsa.shake.fors.fors_pk_from_sig,`slhdsa.WidthEight.forsRecover),
    (`slhdsa.Shake.fors_verify_spec,`slhdsa.WidthEight.forsRecoverSpec),
    (`slhdsa.shake.xmss.xmss_pk_from_sig,`slhdsa.WidthEight.xmssRecover),
    (`slhdsa.Shake.xmss_pk_from_sig_spec,`slhdsa.WidthEight.xmssRecoverSpec),
    (`slhdsa.shake.ht.ht_sign,`slhdsa.WidthEight.htSign),
    (`slhdsa.Shake.ht_sign_spec,`slhdsa.WidthEight.htSignSpec)]
  let names ← IO.mkRef (Std.HashMap.ofList mapping)
  for setName in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`slh_sign_internal_spec,`slh_verify_internal_spec,
               `sign_spec,`sign_deterministic_spec,`verify_spec,`slh_sign_spec,`slh_verify_spec] do
      let base := `slhdsa ++ setName ++ op
      let goal := if (← getEnv).contains (`SegmentedPublic ++ base) then `SegmentedPublic ++ base else base
      let actual ← CacheopsRust.NativeVerifier.abstractCalls `WidthEightSDK [`Slhdsa,`Shakebatch,`Shakeopt,`Facade]
        goal names `slhdsa.WidthEight.Platform
      unless actual == `WidthEightSDK ++ goal do throwError "missed public entry {goal}"
end
end slhdsa.WidthEight
