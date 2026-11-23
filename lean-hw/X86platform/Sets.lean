import X86platform.Fors
import Slhdsa.Proofs.Sets
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let mut entries := #[]
  for set in [`sha2_128s,`sha2_128f,`sha2_192s,`sha2_192f,`sha2_256s,`sha2_256f] do
    for op in [`slh_keygen_internal_spec,`slh_sign_internal_spec,`slh_verify_internal_spec] do
      entries := entries.push (`slhdsa ++ set ++ op)
  PlatformProof.replay `X86Internal X86Platform.calls entries

#print axioms X86Internal.slhdsa.sha2_128s.slh_sign_internal_spec
#print axioms X86Internal.slhdsa.sha2_256f.slh_verify_internal_spec
