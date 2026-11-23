import Armplatform.Replay
import Segmentedapi.Top
import Slhdsa.Proofs.Sets
open Lean Elab Command

namespace PortablePlatform
def compression : List (Name × Name) :=
  [(`slhdsa.sha256.compress,`slhdsa.sha256.compress_portable),
   (`slhdsa.compress_spec,`slhdsa.compress_portable_spec),
   (`slhdsa.sha512.compress,`slhdsa.sha512.compress_portable),
   (`slhdsa.S512.compress_spec,`slhdsa.S512.compress_portable_spec)]

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `PortableChain compression #[`slhdsa.chain_blocks_portable_spec]

def kernels : List (Name × Name) :=
  compression ++
    [(`slhdsa.hash.chain_blocks,`PortableChain.slhdsa.hash.chain_blocks_portable),
     (`slhdsa.chain_blocks_spec,`PortableChain.slhdsa.chain_blocks_portable_spec)]

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `PortableMessage kernels
    #[`slhdsa.SegmentedApi.sign_spec,`slhdsa.SegmentedApi.verify_spec]

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let calls := kernels ++
    [(`slhdsa.slh.slh_sign,`PortableMessage.slhdsa.SegmentedApi.Program.slh.slh_sign),
     (`slhdsa.slh_sign_spec,`PortableMessage.slhdsa.SegmentedApi.sign_spec),
     (`slhdsa.slh.slh_verify,`PortableMessage.slhdsa.SegmentedApi.Program.slh.slh_verify),
     (`slhdsa.slh_verify_spec,`PortableMessage.slhdsa.SegmentedApi.verify_spec)]
  let mut entries := #[]
  for set in [`sha2_128s,`sha2_128f,`sha2_192s,`sha2_192f,`sha2_256s,`sha2_256f] do
    for op in [`slh_keygen_internal_spec,`slh_sign_internal_spec,`slh_verify_internal_spec,
               `slh_sign_spec,`slh_verify_spec,`keygen_spec,`public_key_spec,`sign_spec,
               `sign_deterministic_spec,`verify_spec] do
      entries := entries.push (`slhdsa ++ set ++ op)
  PlatformProof.replay `PortableAPI calls entries
end PortablePlatform
#print axioms PortableAPI.slhdsa.sha2_128s.sign_spec
#print axioms PortableAPI.slhdsa.sha2_256f.verify_spec
