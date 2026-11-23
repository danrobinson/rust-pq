import Shakebatch.Sets
import Armplatform.Replay
open Lean
namespace PlatformProof

/-- Rebuild all sixty public wrappers with the target's five proven FORS/WOTS operations
and its sequential sponge for message hashing and all scalar fallback paths. -/
def shakeApi (destination backend sponge : Name) : CoreM Unit := do
  let mut bindings := [
    (`slhdsa.shake256.Sponge, sponge ++ `shake256.Sponge),
    (`slhdsa.shake256.Sponge.pos, sponge ++ `shake256.Sponge.pos),
    (`slhdsa.shake256.Sponge.lanes, sponge ++ `shake256.Sponge.lanes),
    (`slhdsa.shake256.Sponge.new, sponge ++ `shake256.Sponge.new),
    (`slhdsa.shake256.Sponge.absorb, sponge ++ `shake256.Sponge.absorb),
    (`slhdsa.shake256.Sponge.finish, sponge ++ `shake256.Sponge.finish),
    (`slhdsa.Keccak.view, backend ++ `view),
    (`slhdsa.Keccak.new_spec, backend ++ `new_spec),
    (`slhdsa.Keccak.absorb_spec, backend ++ `absorb_spec),
    (`slhdsa.Keccak.finish_spec, backend ++ `finish_spec)]
  for (moduleName, functionName, backendName) in
      [(`fors,`fors_sign,`sign),(`fors,`fors_pk_from_sig,`recover),
       (`wots,`wots_pk_gen,`wots_pk_gen),(`wots,`wots_sign,`wots_sign),
       (`wots,`wots_pk_from_sig,`wots_pk_from_sig)] do
    let thm := Name.mkSimple (toString functionName ++ "_spec")
    bindings := (`slhdsa.shake ++ moduleName ++ functionName, backend ++ backendName) ::
      (`slhdsa.Shake ++ thm, backend ++ thm) :: bindings
  let mut roots := #[`slhdsa.Shake.xmss_node_spec,`slhdsa.Shake.xmss_sign_spec,`slhdsa.Shake.xmss_pk_from_sig_spec]
  for setName in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for op in [`keygen_spec,`public_key_spec,`sign_spec,`sign_deterministic_spec,`verify_spec,
               `slh_keygen_internal_spec,`slh_sign_internal_spec,`slh_verify_internal_spec,`slh_sign_spec,`slh_verify_spec] do
      roots := roots.push (`slhdsa ++ setName ++ op)
  replay destination bindings roots

end PlatformProof
