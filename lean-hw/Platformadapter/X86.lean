import Platformadapter.FacadeContext
import X86platform.Public
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let mut calls := X86Platform.calls
  for decl in [`slhdsa.slh.slh_keygen_internal,`slhdsa.slh_keygen_internal_spec,
               `slhdsa.slh.slh_sign_internal,`slhdsa.slh_sign_internal_spec,
               `slhdsa.slh.slh_verify_internal,`slhdsa.slh_verify_internal_spec] do
    calls := (decl,`X86Internal ++ decl) :: calls
  for decl in [`slhdsa.SegmentedApi.Program.slh.slh_sign,`slhdsa.SegmentedApi.sign_spec,
               `slhdsa.SegmentedApi.Program.slh.slh_verify,`slhdsa.SegmentedApi.verify_spec] do
    calls := (decl,`X86Message ++ decl) :: calls
  PlatformProof.replay `X86Facade calls
    (PlatformFacadeProof.roots.map (`FacadeContext.FacadeAdapter ++ ·))
