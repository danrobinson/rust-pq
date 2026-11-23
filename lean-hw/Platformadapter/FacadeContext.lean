import Platformadapter.Facade
import Armplatform.Context
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `FacadeContext ArmPlatformProof.contextReplacements
    (PlatformFacadeProof.roots.map (`FacadeAdapter ++ ·))
