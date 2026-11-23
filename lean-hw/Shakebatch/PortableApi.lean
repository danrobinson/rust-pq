import Shakeabs.Api
import Shakebatch.NativeApi

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `PortableShakeSDK
    (PlatformProof.spongeBindings `slhdsa.PlatformShake `ShakeAbsRust) PlatformProof.shakeApiRoots
