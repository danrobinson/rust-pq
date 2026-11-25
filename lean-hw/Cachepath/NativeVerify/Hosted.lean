import Cachepath.NativeVerify.HostedRecovery

open Lean Elab Command in
set_option maxHeartbeats 0 in
set_option Elab.async false in
run_cmd liftCoreM do
  PlatformProof.replay `AppleNativeRecovery (← Cachepath.NativeHashReplay.appleBindings) #[`slhdsa.NativeVerify.appleRecovery] [`Cachepath,`Shakeopt,`Shakebatch]
  PlatformProof.replay `LinuxNativeRecovery (Cachepath.NativeHashReplay.bindings `KspongeLRust `slhdsa.ShakeBatch.Linux)
    #[`slhdsa.NativeVerify.linuxRecovery] [`Cachepath,`Shakeopt,`Shakebatch]
  PlatformProof.replay `X86NativeRecovery (Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)
    #[`slhdsa.NativeVerify.x86Recovery] [`Cachepath,`Shakeopt,`Shakebatch]


namespace CacheopsRust.NativeVerifier

open Lean Meta Elab Command in
set_option Elab.async false in
run_cmd liftTermElabM do
  let install (target : Name) (proof : Expr) : MetaM Unit := do
    addDecl <| .thmDecl { «name» := target, levelParams := [], type := ← inferType proof, value := proof }
  withLocalDeclD `sha3 (mkConst `Bool) fun sha3 => do
    let recovery := mkApp (mkConst `AppleNativeRecovery.slhdsa.NativeVerify.appleRecovery) sha3
    let proof := mkApp2 (mkConst `AppleCachedVerification.HostedAppleSession.CacheopsRust.NativeSession.appleFull) recovery sha3
    install `CacheopsRust.NativeVerifier.appleRoundTrip (← mkLambdaFVars #[sha3] proof)
    let verify := mkApp (mkConst `AppleVerifier.VerifierWithRecovery.SegmentedPublic.slhdsa.Shake.api_verify_spec) recovery
    install `CacheopsRust.NativeVerifier.appleVerify (← mkLambdaFVars #[sha3] verify)
  install `CacheopsRust.NativeVerifier.linuxArmRoundTrip (mkApp
    (mkConst `LinuxCachedVerification.HostedLinuxSession.CacheopsRust.NativeSession.linuxArmFull)
    (mkConst `LinuxNativeRecovery.slhdsa.NativeVerify.linuxRecovery))
  install `CacheopsRust.NativeVerifier.linuxX86RoundTrip (mkApp
    (mkConst `X86CachedVerification.HostedX86Session.CacheopsRust.NativeSession.linuxX86Full)
    (mkConst `X86NativeRecovery.slhdsa.NativeVerify.x86Recovery))
  install `CacheopsRust.NativeVerifier.linuxArmVerify (mkApp
    (mkConst `LinuxVerifier.VerifierWithRecovery.SegmentedPublic.slhdsa.Shake.api_verify_spec)
    (mkConst `LinuxNativeRecovery.slhdsa.NativeVerify.linuxRecovery))
  install `CacheopsRust.NativeVerifier.linuxX86Verify (mkApp
    (mkConst `X86Verifier.VerifierWithRecovery.SegmentedPublic.slhdsa.Shake.api_verify_spec)
    (mkConst `X86NativeRecovery.slhdsa.NativeVerify.x86Recovery))

end CacheopsRust.NativeVerifier
