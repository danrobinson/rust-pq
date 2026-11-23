import Platformadapter.Apple
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `LinuxFacade [
    (`slhdsa.sha512.compress,`ArmStreamRust.sha512.compress),
    (`slhdsa.S512.compress_spec,`slhdsa.PlatformStream.arm512_block)]
    (PlatformFacadeProof.roots.map (`AppleFacade.FacadeContext.FacadeAdapter ++ ·))
