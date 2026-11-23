import Shakebatch.LinuxWots
import Shakebatch.NativeApi
open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftCoreM <| PlatformProof.shakeApi `NativeShakeLinux `slhdsa.ShakeBatch.Linux `KspongeLRust
