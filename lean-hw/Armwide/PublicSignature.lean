import Armwide.Signature
import Armwide.XmssKeygen
import Slhdsa.ApiTheorems
import Armplatform.AppleContext
open Lean Elab Command

namespace NativeArmApi

/- Rebuild both message-length branches of the named SDKs using the native
FORS and hypertree calls. All roots quantify over both CPU feature outcomes. -/
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  slhdsa.Armwide.Hypertree.replayFeatures `ArmSdk [
    (`AppleContext.slhdsa.slh.slh_sign_internal,`slhdsa.NativeArmSignature.slh.slh_sign_internal),
    (`AppleContext.slhdsa.slh.slh_verify_internal,`slhdsa.NativeArmSignature.slh.slh_verify_internal),
    (`AppleContext.slhdsa.slh_sign_internal_spec,`slhdsa.NativeArmSignature.slh_sign_internal_spec),
    (`AppleContext.slhdsa.slh_verify_internal_spec,`slhdsa.NativeArmSignature.slh_verify_internal_spec),
    (`AppleContext.slhdsa.fors.fors_sign,`slhdsa.NativeArmSignature.fors.fors_sign),
    (`AppleContext.slhdsa.fors.fors_pk_from_sig,`slhdsa.NativeArmSignature.fors.fors_pk_from_sig),
    (`slhdsa.ht.ht_sign,`slhdsa.NativeArmSignature.ht.ht_sign),
    (`slhdsa.ht.ht_verify,`slhdsa.NativeArmSignature.ht.ht_verify)]
    (ArmPlatformProof.contextRoots.map (`AppleContext.SegmentedSdk ++ ·))
    [`Armplatform,`Slhdsa,`Segmentedapi,`Segmented]

def profiles := #[`sha2_128s,`sha2_128f,`sha2_192s,`sha2_192f,`sha2_256s,`sha2_256f]

def internalRoots := ArmPlatformProof.internalRoots.map (`AppleInternal ++ ·)
def keyRoots := profiles.flatMap fun s =>
  #[`slh_keygen_internal_spec,`keygen_spec].map fun op => `slhdsa ++ s ++ op

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let replay := slhdsa.Armwide.Hypertree.replayFeatures
  replay `ArmInternal [
    (`AppleInternal.slhdsa.slh.slh_sign_internal,`slhdsa.NativeArmSignature.slh.slh_sign_internal),
    (`AppleInternal.slhdsa.slh.slh_verify_internal,`slhdsa.NativeArmSignature.slh.slh_verify_internal),
    (`AppleInternal.slhdsa.slh_sign_internal_spec,`slhdsa.NativeArmSignature.slh_sign_internal_spec),
    (`AppleInternal.slhdsa.slh_verify_internal_spec,`slhdsa.NativeArmSignature.slh_verify_internal_spec)]
    internalRoots [`Armplatform,`Slhdsa]
  replay `ArmKeys [
    (`slhdsa.slh.slh_keygen_internal,`slhdsa.Armwide.XmssLeaves.Generate.slh.slh_keygen_internal),
    (`slhdsa.slh_keygen_internal_spec,`slhdsa.Armwide.XmssLeaves.Generate.keygen_fips)]
    keyRoots [`Slhdsa]

def sessionRoots := profiles.flatMap fun s =>
  #[`complete_internal,`complete,`api_complete_sign,`api_complete_sign_deterministic].map fun op =>
    `slhdsa ++ s ++ op

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let mut bindings := []
  for s in profiles do
    for (owner,ops) in [
      (`ArmKeys, #[`slh_keygen_internal,`keygen]),
      (`ArmInternal.AppleInternal, #[`slh_sign_internal,`slh_verify_internal]),
      (`ArmSdk.AppleContext.SegmentedSdk, #[`slh_sign,`slh_verify,`sign,`sign_deterministic,`verify])] do
      for op in ops do
        let funName := `slhdsa.sets ++ s ++ op
        let thmName := `slhdsa ++ s ++ op.appendAfter "_spec"
        bindings := (funName,owner ++ funName) :: (thmName,owner ++ thmName) :: bindings
  slhdsa.Armwide.Hypertree.replayFeatures `ArmSession bindings sessionRoots [`Slhdsa]

end NativeArmApi
