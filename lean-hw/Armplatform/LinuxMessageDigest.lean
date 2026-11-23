import Armplatform.MessageDigest
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `LinuxMessage [
    (`slhdsa.sha512.compress,`ArmStreamRust.sha512.compress),
    (`slhdsa.S512.compress_spec,`slhdsa.PlatformStream.arm512_block)] #[`AppleMessage.slhdsa.Segmented.digest_spec]

#print axioms LinuxMessage.AppleMessage.slhdsa.Segmented.digest_spec
