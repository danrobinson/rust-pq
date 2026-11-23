import Facade
import Shakebatch.FacadeKat
import Shakebatch.NativeApi

open Lean Elab Command
namespace PlatformProof

def shakeFacadeRoots : Array Name := Id.run do
  let mut roots := #[`slh_dsa.multipart_sign_eq, `slh_dsa.multipart_verify_eq, `slh_dsa.multipart_randomized_eq]
  for shape in ["128s", "128f", "192s", "192f", "256s", "256f"] do
    for op in ["sign", "sign_with_context", "verify", "verify_with_context", "randomized_sign", "new", "parsers", "der"] do
      roots := roots.push (`slh_dsa ++ Name.mkSimple ("shake_" ++ shape ++ "_" ++ op))
    for op in ["algorithms", "errors"] do
      roots := roots.push (`slh_dsa.Kat ++ Name.mkSimple ("shake_" ++ shape ++ "_" ++ op))
  return roots

end PlatformProof

