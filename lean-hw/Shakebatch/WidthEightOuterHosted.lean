import Shakebatch.WidthEightHosted
import Shakebatch.WidthEightOuter

open Lean Elab Command
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let base := `slhdsa.WidthEight.xmssSign
  for (dst,published,bindings) in [
      (`WidthEightOuterApple,`WidthEightApple,← Cachepath.NativeHashReplay.appleBindings),
      (`WidthEightOuterX86,`WidthEightX86,Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)] do
    let target := published ++ base
    unless (←getEnv).contains target do throwError "missing released XMSS signer {target}"
    -- Reuse the public proof’s existing scalar substitutions; replay only the newly
    -- extracted dispatch and its branch-equality proof.
    let env ← getEnv
    let mut known := [(base,target),(`slhdsa.WidthEight.Platform.fused,`slhdsa.WidthEight.Platform.fused),
      (`slhdsa.Fused.xmss_sign_batch,`slhdsa.Fused.xmss_sign_batch)]
    for (n,_) in env.constants.toList do
      if published.isPrefixOf n then
        let src := n.replacePrefix published Name.anonymous
        if env.contains src then known := (src,n)::known
    PlatformProof.replay dst (known ++ bindings) #[`slhdsa.WidthEight.outer_eq]
      [`Fused.Outer,`Fused.OuterProgram,`Cachepath,`Shakeopt]
    unless (←getEnv).contains (dst ++ `slhdsa.Fused.Outer.shake.xmss.xmss_sign) do
      throwError "outer signer did not specialize the native sponge for {published}"
