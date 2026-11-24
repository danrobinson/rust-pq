import Shakebatch.NativeFacade
import Shakebatch.AppleApi
open Lean Elab Command PlatformProof in
set_option maxHeartbeats 0 in
run_cmd liftCoreM <| replay `NativeShakeAppleFacade (shakeBindings `slhdsa.ShakeBatch.Apple `KappleouterRust) shakeFacadeRoots
