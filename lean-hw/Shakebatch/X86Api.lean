import Shakebatch.X86Wots
import Shakebatch.NativeApi
open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftCoreM <| PlatformProof.shakeApi `NativeShakeX86 `slhdsa.ShakeBatch.X86 `KxouterRust
