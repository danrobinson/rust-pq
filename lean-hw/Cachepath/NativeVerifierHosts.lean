import Cachepath.NativeVerifier

namespace CacheopsRust.NativeVerifier
open Lean Meta Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let api := `SegmentedPublic.slhdsa.shake.api.verify
  let spec := `SegmentedPublic.slhdsa.Shake.api_verify_spec
  for (signer,verifier,combined,root,pairs) in [
      (`HostedAppleSession,`AppleVerifier,`AppleCachedVerification,`appleFull, ← Cachepath.NativeHashReplay.appleBindings),
      (`HostedLinuxSession,`LinuxVerifier,`LinuxCachedVerification,`linuxArmFull,
        Cachepath.NativeHashReplay.bindings `KspongeLRust `slhdsa.ShakeBatch.Linux),
      (`HostedX86Session,`X86Verifier,`X86CachedVerification,`linuxX86Full,
        Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)] do
    PlatformProof.replay verifier pairs #[`VerifierWithRecovery ++ spec] [`Cachepath,`Shakeopt]
    let names ← IO.mkRef (Std.HashMap.ofList [
      (`PortableSegmented ++ api,verifier ++ `VerifierWithRecovery ++ api),
      (`PortableSegmented ++ spec,verifier ++ `VerifierWithRecovery ++ spec)])
    let _ ← abstractCalls combined [`Cachepath] (signer ++ `CacheopsRust.NativeSession ++ root) names
  pure ()

end CacheopsRust.NativeVerifier
