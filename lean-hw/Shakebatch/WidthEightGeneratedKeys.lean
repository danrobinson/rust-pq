import Buffered.HostedKeygen
import Shakebatch.WidthEightKeygen
import Shakebatch.WidthEightOuterHosted

open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight
open ParallelKeygenHost

theorem apple_keys {N : Usize} (sha3 : Bool) (p : params.Params) (hp : PN p N)
    (threads : Nat) (pool : PoolOutcome) :
    ShNode.KeyPair (sourceEngine (.apple sha3) p) false threads pool (N:=N) p := by
  apply source_keys p hp (.apple sha3) false threads pool
  intro sk seed i z a _ lo hi room
  exact BufferedAppleKeys.slhdsa.Buffered.Host.apple_all sha3 p hp sk seed i z a lo hi room

theorem x86_keys {N : Usize} (p : params.Params) (hp : PN p N)
    (threads : Nat) (pool : PoolOutcome) :
    ShNode.KeyPair (sourceEngine .x86 p) true threads pool (N:=N) p := by
  apply source_keys p hp .x86 true threads pool
  intro sk seed i z a on lo hi room
  exact BufferedX86Keys.slhdsa.Buffered.Host.x86_all (Bool.and_eq_true_iff.mp on).2 p hp sk seed i z a lo hi room

end slhdsa.WidthEight
