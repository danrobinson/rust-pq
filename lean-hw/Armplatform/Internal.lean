import Slhdsa.Proofs.Sets
import Armplatform.ForsLoops
import Armstream.Proof
open Lean Elab Command

namespace ArmPlatformProof
def internalRoots : Array Name := Id.run do
  let mut roots := #[]
  for set in [`sha2_128s, `sha2_128f, `sha2_192s, `sha2_192f, `sha2_256s, `sha2_256f] do
    for op in [`slh_sign_internal_spec,`slh_verify_internal_spec] do
      roots := roots.push (`slhdsa ++ set ++ op)
  return roots

def armReplacements : List (Name × Name) := [
  (`slhdsa.fors.fors_batch_loop3,`slhdsa.PlatformFors.armTreeLoop),
  (`slhdsa.fors_batch_loop3_spec,`slhdsa.PlatformFors.armTreeLoopSpec),
  (`slhdsa.fors.fors_pk_from_sig_loop2,`slhdsa.PlatformFors.armPathLoop),
  (`slhdsa.fors_pk_from_sig_loop2_spec,`slhdsa.PlatformFors.armPathLoopSpec),
  (`slhdsa.sha256.sha256_from,`ArmStreamRust.sha256.sha256_from),
  (`slhdsa.sha256_from_spec,`slhdsa.PlatformStream.arm256_from),
  (`slhdsa.sha512.sha512_from,`ArmStreamRust.sha512.sha512_from),
  (`slhdsa.S512.sha512_from_spec,`slhdsa.PlatformStream.arm512_from)]
end ArmPlatformProof

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `AppleInternal ArmPlatformProof.armReplacements ArmPlatformProof.internalRoots
