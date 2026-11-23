import Shakebatch.LinuxWots
import Shakebatch.NativeApi
open Lean Elab Command PlatformProof in
set_option maxHeartbeats 0 in
run_cmd liftCoreM <| shakeUnderRound `NativeShakeLinux `slhdsa.ShakeBatch.Linux `KspongeLRust `slhdsa.Kldisp.RoundCorrect shakeApiRoots
