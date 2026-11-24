import Armplatform.Internal
import Segmentedapi.Top
open Lean Elab Command

namespace ArmPlatformProof

def contextRoots : Array Name := Id.run do
  let mut roots := #[]
  for set in [`sha2_128s,`sha2_128f,`sha2_192s,`sha2_192f,`sha2_256s,`sha2_256f] do
    for op in [`sign_spec,`sign_deterministic_spec,`verify_spec,`slh_sign_spec,`slh_verify_spec] do
      roots := roots.push (`slhdsa ++ set ++ op)
  return roots

def contextReplacements : List (Name × Name) := [
  (`slhdsa.slh.slh_sign,`slhdsa.SegmentedApi.Program.slh.slh_sign),
  (`slhdsa.slh_sign_spec,`slhdsa.SegmentedApi.sign_spec),
  (`slhdsa.slh.slh_verify,`slhdsa.SegmentedApi.Program.slh.slh_verify),
  (`slhdsa.slh_verify_spec,`slhdsa.SegmentedApi.verify_spec)]
end ArmPlatformProof

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `SegmentedSdk ArmPlatformProof.contextReplacements ArmPlatformProof.contextRoots
