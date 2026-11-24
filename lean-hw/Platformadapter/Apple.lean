import Platformadapter.FacadeContext
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `AppleFacade ArmPlatformProof.armReplacements
    (PlatformFacadeProof.roots.map (`FacadeContext.FacadeAdapter ++ ·))
