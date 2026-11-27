import Shakebatch.WidthEightModel

open Lean Meta Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let names ← IO.mkRef (Std.HashMap.ofList [
    (`slhdsa.shake.xmss.xmss_sign,`slhdsa.WidthEight.xmssSign),
    (`slhdsa.Shake.xmss_sign_spec,`slhdsa.WidthEight.xmssSign_spec),
    (`slhdsa.shake.xmss.xmss_pk_from_sig,`slhdsa.WidthEight.xmssRecover),
    (`slhdsa.Shake.xmss_pk_from_sig_spec,`slhdsa.WidthEight.xmssRecoverSpec)])
  let root := `slhdsa.Shake.ht_sign_spec
  let actual ← CacheopsRust.NativeVerifier.abstractCalls `WidthEightTree [`Slhdsa] root names `slhdsa.WidthEight.Platform
  unless actual == `WidthEightTree ++ root do throwError "width-eight hypertree substitution missed its root"
