import Armplatform.LinuxInternal
import Segmented.Digest
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `AppleMessage ArmPlatformProof.armReplacements #[`slhdsa.Segmented.digest_spec]

#print axioms AppleMessage.slhdsa.Segmented.digest_spec
