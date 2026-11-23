import Armplatform.Internal
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let roots := ArmPlatformProof.internalRoots.map (`AppleInternal ++ ·)
  PlatformProof.replay `LinuxInternal [
    (`slhdsa.sha512.compress,`ArmStreamRust.sha512.compress),
    (`slhdsa.S512.compress_spec,`slhdsa.PlatformStream.arm512_block)] roots
