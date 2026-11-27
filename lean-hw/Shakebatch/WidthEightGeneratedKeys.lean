import Buffered.HostedKeygen
import Shakebatch.WidthEightKeygen
import Shakebatch.WidthEightOuterHosted

open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight
open ParallelKeygenHost

theorem apple_nodes {N : Usize} (sha3 : Bool) (p : params.Params) (hp : PN p N) :
    AllNodes (.apple sha3) (N:=N) p := by
  intro sk seed i z a _ lo hi room
  exact BufferedAppleKeys.slhdsa.Buffered.Host.apple_all sha3 p hp sk seed i z a lo hi room

theorem apple_keys {N : Usize} (sha3 : Bool) (p : params.Params) (hp : PN p N)
    (threads : Nat) (pool : PoolOutcome) :
    ShNode.KeyPair (sourceEngine (.apple sha3) p) false threads pool (N:=N) p := by
  apply source_keys p hp (.apple sha3) false threads pool
  exact apple_nodes sha3 p hp

theorem x86_nodes {N : Usize} (p : params.Params) (hp : PN p N) :
    AllNodes .x86 (N:=N) p := by
  intro sk seed i z a on lo hi room
  exact BufferedX86Keys.slhdsa.Buffered.Host.x86_all (Bool.and_eq_true_iff.mp on).2 p hp sk seed i z a lo hi room

theorem x86_keys {N : Usize} (p : params.Params) (hp : PN p N)
    (threads : Nat) (pool : PoolOutcome) :
    ShNode.KeyPair (sourceEngine .x86 p) true threads pool (N:=N) p := by
  apply source_keys p hp .x86 true threads pool
  exact x86_nodes p hp

theorem apple_worker_node {N : Usize} (sha3 : Bool) (p : params.Params) (hp : PN p N)
    (sk : Array U8 N) (i z : U32) (seed : Array U8 N) (a : address.Adrs) (room : (i.val+1)*2^z.val≤512) :
    NodeResult p sk seed i z a ((sourceEngine (.apple sha3) p).node sk i z seed a) :=
  source_node p hp (.apple sha3) (apple_nodes sha3 p hp) sk i z seed a room

theorem x86_worker_node {N : Usize} (p : params.Params) (hp : PN p N)
    (sk : Array U8 N) (i z : U32) (seed : Array U8 N) (a : address.Adrs) (room : (i.val+1)*2^z.val≤512) :
    NodeResult p sk seed i z a ((sourceEngine .x86 p).node sk i z seed a) :=
  source_node p hp .x86 (x86_nodes p hp) sk i z seed a room

end slhdsa.WidthEight
