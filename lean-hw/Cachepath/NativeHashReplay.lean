import Cachepath.NativeReuse
import Cachepath.NativeAppleSingle
import Shakebatch.NativeApi
open Lean Elab Command

namespace Cachepath.NativeHashReplay

def bindings (sponge proof : Name) : List (Name × Name) :=
  PlatformProof.spongeBindings proof sponge ++
    [(`slhdsa.shake256.Sponge.mk, sponge ++ `shake256.Sponge.mk),
     (`shake256.Sponge, sponge ++ `shake256.Sponge)]

def appleBindings : CoreM (List (Name × Name)) := do
  let env ← getEnv
  let mapped (n : Name) := if env.contains (`AppleSingleStream ++ n) then `AppleSingleStream ++ n else n
  let pairs := (bindings `KappleouterRust `slhdsa.ShakeBatch.Apple).map fun (old,new) => (old,mapped new)
  let stream := `ShakeForestApple.slhdsa.ShakeBatch.scalarStream
  let correct := `ShakeForestApple.slhdsa.ShakeBatch.scalarStreamCorrect
  return pairs ++ [(stream,mapped stream),(correct,mapped correct)]

private def host (target : Name) (substitutions : List (Name × Name)) (root reuse : Name) : CoreM Unit :=
  PlatformProof.replayWithContracts target substitutions
    [`CacheopsRust.Closed.FastSpec, `CacheopsRust.Closed.DispatchCorrect,
     `slhdsa.cache.builder.nativeShake.Subtree.Ops]
    #[root,reuse] [`Cacheops, `Cachepath, `Shakeopt]

set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  host `HostedLinuxSession (bindings `KspongeLRust `slhdsa.ShakeBatch.Linux) `CacheopsRust.NativeSession.linuxArmFull `CacheopsRust.NativeSession.linuxArm_reuse
  host `HostedX86Session (bindings `KxouterRust `slhdsa.ShakeBatch.X86) `CacheopsRust.NativeSession.linuxX86Full `CacheopsRust.NativeSession.linuxX86_reuse
  host `HostedAppleSession (← appleBindings) `CacheopsRust.NativeSession.appleFull `CacheopsRust.NativeSession.apple_reuse

end Cachepath.NativeHashReplay
