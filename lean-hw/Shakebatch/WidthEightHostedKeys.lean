import Shakebatch.WidthEightGeneratedKeys

open Lean Elab Command
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let env ← getEnv
  for (dest,outer,host,root,bindings) in [
      (`WidthEightAppleKeys,`WidthEightOuterApple,`WidthEightApple,`slhdsa.WidthEight.apple_keys,← Cachepath.NativeHashReplay.appleBindings),
      (`WidthEightX86Keys,`WidthEightOuterX86,`WidthEightX86,`slhdsa.WidthEight.x86_keys,
        Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)] do
    let mut known := bindings
    for ns in [host,outer] do
      for (n,_) in env.constants.toList do
        if ns.isPrefixOf n then
          let src := n.replacePrefix ns Name.anonymous
          if env.contains src then known := (src,n)::known
    PlatformProof.replay dest known #[root] [`Shakebatch.WidthEightGeneratedKeys,`Shakebatch.WidthEightKeygen,`Fused.Outer,`Fused.OuterNode,`Fused.OuterProgram,`Cachepath,`Shakeopt]
    unless ((←getEnv).contains (outer ++ `slhdsa.Fused.Outer.shake.xmss.xmss_node) ||
        (←getEnv).contains (dest ++ `slhdsa.Fused.Outer.shake.xmss.xmss_node)) &&
        (←getEnv).contains (dest ++ `slhdsa.WidthEight.sourceEngine) do
      throwError "missing feature-dispatched native XMSS node in {dest}"
