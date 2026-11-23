import Shakebatch.LinuxApi
import Shakebatch.NativeFacade
open Lean Elab Command PlatformProof in
set_option maxHeartbeats 0 in
run_cmd liftCoreM <| shakeUnderRound `NativeShakeLinuxFacade `slhdsa.ShakeBatch.Linux `KspongeLRust `slhdsa.Kldisp.RoundCorrect shakeFacadeRoots
