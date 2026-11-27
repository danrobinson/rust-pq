import Buffered.ForsHorizontal.Entry
import Buffered.Hosted
open Lean Elab Command

set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let env ← getEnv
  for (dest,shared,bindings) in [
      (`ForsTreeApple,`BufferedApple,← Cachepath.NativeHashReplay.appleBindings),
      (`ForsTreeX86,`BufferedX86,Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)] do
    let mut known := bindings
    for (n,_) in env.constants.toList do
      if shared.isPrefixOf n then
        let original := n.replacePrefix shared Name.anonymous
        if env.contains original then known := (original,n)::known
    PlatformProof.replay dest known #[`slhdsa.ForsHorizontal.subtree_spec] [`Buffered,`Cachepath,`Shakeopt]
    unless (←getEnv).contains (dest ++ `slhdsa.ForsHorizontal.subtree) do
      throwError "native scalar SHAKE missing in horizontal FORS tree {dest}"
