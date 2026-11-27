import Armwide.XmssKeygen
import Armplatform.Replay
import Slhdsa.Proofs.Sets

open Lean Elab Command Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.XmssLeaves.Generate

noncomputable abbrev wideSeeded256 := @slh.slh_keygen_internal ⟨true⟩ ⟨false⟩
noncomputable abbrev wideSeeded512 := @slh.slh_keygen_internal ⟨true⟩ ⟨true⟩
noncomputable abbrev wideSeeded256_spec := @keygen_fips ⟨true⟩ ⟨false⟩
noncomputable abbrev wideSeeded512_spec := @keygen_fips ⟨true⟩ ⟨true⟩
end slhdsa.Armwide.XmssLeaves.Generate

/- Specialize the actual seeded public APIs and all parameter constants for both native SHA-512 decisions. -/
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for (destination,op,proof) in [(`ArmWideKeygen256,`wideSeeded256,`wideSeeded256_spec),
      (`ArmWideKeygen512,`wideSeeded512,`wideSeeded512_spec)] do
    let mut roots := #[]
    for family in [`sha2_128s,`sha2_128f,`sha2_192s,`sha2_192f,`sha2_256s,`sha2_256f] do
      for api in [`slh_keygen_internal_spec,`keygen_spec] do roots := roots.push (`slhdsa ++ family ++ api)
    let prefixName := `slhdsa.Armwide.XmssLeaves.Generate
    PlatformProof.replay destination [(`slhdsa.slh.slh_keygen_internal,prefixName ++ op),
      (`slhdsa.slh_keygen_internal_spec,prefixName ++ proof)] roots
