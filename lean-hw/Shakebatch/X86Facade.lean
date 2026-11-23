import Shakebatch.NativeFacade
import Shakebatch.X86Api
open Lean Elab Command PlatformProof in
set_option maxHeartbeats 0 in
run_cmd liftCoreM <| replay `NativeShakeX86Facade (shakeBindings `slhdsa.ShakeBatch.X86 `KxouterRust) shakeFacadeRoots
