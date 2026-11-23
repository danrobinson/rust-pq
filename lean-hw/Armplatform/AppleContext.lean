import Armplatform.Context
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `AppleContext ArmPlatformProof.armReplacements
    (ArmPlatformProof.contextRoots.map (`SegmentedSdk ++ ·))
