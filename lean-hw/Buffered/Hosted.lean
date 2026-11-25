import Buffered.SignHost
import Cachepath.NativeHashReplay

open Lean Elab Command
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for (dst,host,bindings) in [
      (`BufferedApple,`apple,← Cachepath.NativeHashReplay.appleBindings),
      (`BufferedX86,`x86,Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)] do
    let entry := `slhdsa.Buffered.Host ++ host
    let root := `slhdsa.Buffered.Host ++ Name.mkSimple (host.toString ++ "_nodes")
    PlatformProof.replay dst bindings #[root] [`Buffered,`Cachepath,`Shakeopt]
    unless (←getEnv).contains (dst ++ entry) && (←getEnv).contains (dst ++ `slhdsa.Buffered.subtree) do
      throwError "missing native buffered subtree and scalar child hashes in {dst}"
