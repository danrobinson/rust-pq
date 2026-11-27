import Fused.Host
import Cachepath.NativeHashReplay

open Lean Elab Command
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for (dst,host,bindings) in [
      (`FusedApple,`apple,← Cachepath.NativeHashReplay.appleBindings),
      (`FusedX86,`x86,Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)] do
    let root := `slhdsa.Fused.Host ++ Name.mkSimple (host.toString ++ "_subtree")
    PlatformProof.replay dst bindings #[root] [`Fused,`Parallel,`Cachepath,`Shakeopt]
    unless (← getEnv).contains (dst ++ `slhdsa.Fused.Host ++ host) do
      throwError "wide XMSS subtree did not reach the selected {host} sponge"
