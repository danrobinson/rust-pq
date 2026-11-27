import Cachepath.ParallelFillHosted
import Cachepath.NativeHashReplay
import Cachepath.PlatformSha2Linux

open Lean Elab Command
namespace Cachepath.ParallelFillReplay

private def replay (host root : Name) (bindings : List (Name × Name)) : CoreM Unit :=
  PlatformProof.replayWithContracts host bindings
    [`CacheopsRust.Closed.FastSpec,`CacheopsRust.Closed.DispatchCorrect,
     `slhdsa.cache.builder.nativeShake.Subtree.Ops]
    #[root] [`Cacheops,`Cachepath,`Shakeopt]

set_option maxHeartbeats 0 in
set_option Elab.async false in
run_cmd liftCoreM do
  replay `AppleFill `CacheopsRust.NativeSession.apple_parallelBuild
    (ArmPlatformProof.armReplacements ++ (← NativeHashReplay.appleBindings))
  replay `LinuxArmFill `CacheopsRust.NativeSession.linuxArm_parallelBuild
    (ArmPlatformProof.armReplacements ++ NativeHashReplay.bindings `KspongeLRust `slhdsa.ShakeBatch.Linux)
  PlatformProof.replay `LinuxArmFill512 [
      (`slhdsa.sha512.compress,`ArmStreamRust.sha512.compress),
      (`slhdsa.S512.compress_spec,`slhdsa.PlatformStream.arm512_block)]
    #[`LinuxArmFill.CacheopsRust.NativeSession.linuxArm_parallelBuild] [`Cacheops,`Cachepath,`Shakeopt]
  replay `X86Fill `CacheopsRust.NativeSession.linuxX86_parallelBuild
    (X86Platform.calls ++ NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86)

end Cachepath.ParallelFillReplay
