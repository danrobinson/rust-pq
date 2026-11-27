import Buffered.Hosted
import Buffered.AllNodes

open Lean Elab Command
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let env ← getEnv
  for (dest,existing,root,bindings) in [
      (`BufferedAppleKeys,`BufferedApple,`slhdsa.Buffered.Host.apple_all,← Cachepath.NativeHashReplay.appleBindings),
      (`BufferedX86Keys,`BufferedX86,`slhdsa.Buffered.Host.x86_all,
        Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)] do
    let mut known := bindings
    for (n,_) in env.constants.toList do
      if existing.isPrefixOf n then
        let src := n.replacePrefix existing Name.anonymous
        if env.contains src then known := (src,n)::known
    PlatformProof.replay dest known #[root] [`Buffered,`Cachepath,`Shakeopt]
