import Cachepath.PlatformSha2
open Lean Elab Command Cachepath.PlatformSha2

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `LinuxArmCached [
    (`slhdsa.sha512.compress, `ArmStreamRust.sha512.compress),
    (`slhdsa.S512.compress_spec, `slhdsa.PlatformStream.arm512_block)]
    (roots.map (`AppleCached ++ ·)) modules
