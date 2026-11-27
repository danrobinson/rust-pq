import Shakebatch.WidthThreeHost
import Shakebatch.NativeFacade
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthThree
noncomputable section

structure SigningPrimitives where
  wots : Certified
  fors : ForsSigner

abbrev node (c : SigningPrimitives) := @shake.xmss.xmss_node c.wots.ops
abbrev nodeSpec (c : SigningPrimitives) := @node_spec c.wots.ops c.wots.laws.toKeyCorrect
abbrev xmssRecovery (_ : SigningPrimitives) := @CacheopsRust.NativeVerifier.xmssPk NativeVerify.linuxRecovery
abbrev xmssRecoverySpec (_ : SigningPrimitives) := @CacheopsRust.NativeVerifier.xmssSpec NativeVerify.linuxRecovery
abbrev forsSign (c : SigningPrimitives) := @c.fors.run
abbrev forsSignSpec (c : SigningPrimitives) := @c.fors.correct
abbrev forsRecovery (_ : SigningPrimitives) := @NativeVerify.linuxRecovery.fors
abbrev forsRecoverySpec (_ : SigningPrimitives) := @NativeVerify.linuxRecovery.fors_spec
abbrev htSign (c : SigningPrimitives) := @WidthThreeTree.slhdsa.shake.ht.ht_sign c.wots
abbrev htSignSpec (c : SigningPrimitives) := @WidthThreeTree.slhdsa.Shake.ht_sign_spec c.wots

open Lean Meta Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let mapping := [
    (`slhdsa.shake.xmss.xmss_node,`slhdsa.WidthThree.node),
    (`slhdsa.Shake.xmss_node_spec,`slhdsa.WidthThree.nodeSpec),
    (`slhdsa.shake.fors.fors_sign,`slhdsa.WidthThree.forsSign),
    (`slhdsa.Shake.fors_sign_domain,`slhdsa.WidthThree.forsSignSpec),
    (`slhdsa.shake.fors.fors_pk_from_sig,`slhdsa.WidthThree.forsRecovery),
    (`slhdsa.Shake.fors_verify_spec,`slhdsa.WidthThree.forsRecoverySpec),
    (`slhdsa.shake.xmss.xmss_pk_from_sig,`slhdsa.WidthThree.xmssRecovery),
    (`slhdsa.Shake.xmss_pk_from_sig_spec,`slhdsa.WidthThree.xmssRecoverySpec),
    (`slhdsa.shake.ht.ht_sign,`slhdsa.WidthThree.htSign),
    (`slhdsa.Shake.ht_sign_spec,`slhdsa.WidthThree.htSignSpec)]
  let names ← IO.mkRef (Std.HashMap.ofList mapping)
  for setName in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`keygen_spec,`slh_keygen_internal_spec,`slh_sign_internal_spec,`slh_verify_internal_spec,
               `sign_spec,`sign_deterministic_spec,`verify_spec,`slh_sign_spec,`slh_verify_spec] do
      let base := `slhdsa ++ setName ++ op
      let goal := if (← getEnv).contains (`SegmentedPublic ++ base) then `SegmentedPublic ++ base else base
      let actual ← CacheopsRust.NativeVerifier.abstractCalls `WidthThreeSDK [`Slhdsa,`Shakebatch,`Shakeopt,`Facade]
        goal names `slhdsa.WidthThree.SigningPrimitives
      unless actual == `WidthThreeSDK ++ goal do throwError "missed public entry {goal}"

  for root in PlatformProof.shakeFacadeRoots do
    let actual ← CacheopsRust.NativeVerifier.abstractCalls `WidthThreeCompat
      [`Slhdsa,`Shakebatch,`Shakeopt,`Facade] root names `slhdsa.WidthThree.SigningPrimitives
    if root.toString.endsWith "_sign" || root.toString.endsWith "_verify" || root.toString.endsWith "_new" then
      unless actual != root do throwError "missed RustCrypto implementation {root}"

end
end slhdsa.WidthThree
