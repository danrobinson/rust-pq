import Parallel.KeygenPublic
import Cachepath.NativeHashReplay

open Lean Elab Command
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let scope := [`Parallel]
  PlatformProof.replay `KeygenLinuxHashes (Cachepath.NativeHashReplay.bindings `KspongeLRust `slhdsa.ShakeBatch.Linux)
    #[`slhdsa.ParallelKeygenHost.ShNode.linux_keys,`slhdsa.ParallelKeygenHost.sh_linux_public] scope
  PlatformProof.replay `KeygenX86Hashes (Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)
    #[`slhdsa.ParallelKeygenHost.ShNode.x86_keys,`slhdsa.ParallelKeygenHost.sh_x86_public] scope
  PlatformProof.replay `KeygenAppleHashes (← Cachepath.NativeHashReplay.appleBindings)
    #[`slhdsa.ParallelKeygenHost.ShNode.apple_keys,`slhdsa.ParallelKeygenHost.sh_apple_public] scope
