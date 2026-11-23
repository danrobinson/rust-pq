import X86platform.Sets
import Segmentedapi.Top
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `X86Message X86Platform.calls
    #[`slhdsa.SegmentedApi.sign_spec,`slhdsa.SegmentedApi.verify_spec]

def X86Platform.publicCalls : List (Name × Name) :=
  X86Platform.calls ++
    [(`slhdsa.slh.slh_sign,`X86Message.slhdsa.SegmentedApi.Program.slh.slh_sign),
     (`slhdsa.slh_sign_spec,`X86Message.slhdsa.SegmentedApi.sign_spec),
     (`slhdsa.slh.slh_verify,`X86Message.slhdsa.SegmentedApi.Program.slh.slh_verify),
     (`slhdsa.slh_verify_spec,`X86Message.slhdsa.SegmentedApi.verify_spec)]

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let mut entries := #[]
  for set in [`sha2_128s,`sha2_128f,`sha2_192s,`sha2_192f,`sha2_256s,`sha2_256f] do
    for op in [`slh_sign_spec,`slh_verify_spec,`sign_spec,`sign_deterministic_spec,`verify_spec] do
      entries := entries.push (`slhdsa ++ set ++ op)
  PlatformProof.replay `X86Public X86Platform.publicCalls entries

#print axioms X86Public.slhdsa.sha2_128s.sign_spec
#print axioms X86Public.slhdsa.sha2_256f.verify_spec
