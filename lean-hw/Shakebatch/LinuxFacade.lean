import Shakebatch.NativeFacade
import Shakebatch.LinuxApi
open Lean Elab Command PlatformProof in
set_option maxHeartbeats 0 in
run_cmd liftCoreM <| replay `NativeShakeLinuxFacade (shakeBindings `slhdsa.ShakeBatch.Linux `KspongeLRust) shakeFacadeRoots
