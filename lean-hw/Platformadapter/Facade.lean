import Facade
import Platformadapter.Proof
import Armplatform.Replay
open Lean Elab Command

namespace PlatformFacadeProof

def roots : Array Name := Id.run do
  let mut rs := #[`slh_dsa.multipart_sign_eq, `slh_dsa.multipart_verify_eq, `slh_dsa.multipart_randomized_eq]
  for set in ["128s","128f","192s","192f","256s","256f"] do
    for op in ["sign","sign_with_context","verify","verify_with_context","randomized_sign","new","parsers","der"] do
      rs := rs.push (`slh_dsa ++ Name.mkSimple ("sha2_" ++ set ++ "_" ++ op))
  return rs

end PlatformFacadeProof

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `FacadeAdapter [
    (`slhdsa.adapter.sign_into,`slhdsa.PlatformAdapter.adapter.sign_into),
    (`slhdsa.adapter_sign_into_spec,`slhdsa.PlatformAdapter.sign_into_spec),
    (`slhdsa.adapter_sign_into_long_ctx,`slhdsa.PlatformAdapter.sign_into_long_ctx)] PlatformFacadeProof.roots
