import Armplatform.Replay
import Armstream.Proof
import Slhdsa.Proofs.Sets
open Lean Elab Command

/-! Key generation has the same extracted call graph as the verified Arm
hardware build on Apple. Linux selects its separately verified single-block
SHA-512 wrapper. The extraction gate checks every reachable definition. -/
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let mut roots := #[]
  for set in [`sha2_128s, `sha2_128f, `sha2_192s, `sha2_192f, `sha2_256s, `sha2_256f] do
    for op in [`keygen_spec, `public_key_spec, `slh_keygen_internal_spec] do
      roots := roots.push (`slhdsa ++ set ++ op)
  PlatformProof.replay `ArmLinux
    [(`slhdsa.sha512.compress, `ArmStreamRust.sha512.compress),
     (`slhdsa.S512.compress_spec, `slhdsa.PlatformStream.arm512_block)] roots

#print axioms ArmLinux.slhdsa.sha2_128s.keygen_spec
#print axioms ArmLinux.slhdsa.sha2_256s.keygen_spec
