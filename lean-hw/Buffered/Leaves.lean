import Buffered.Program
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered
open ShakeBatch NativeVerify
set_option maxHeartbeats 2000000
set_option linter.concreteInstances false
variable [kernel : Kernel]

def LeafRows {N K : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (start : Nat) (rows : Array (Array U8 N) K) : Prop :=
  ∀ j < K.val, bytes rows.val[j]!.val =
    Spec.xmssNode (Shake.params p) (bytes sk.val) (start+j) 0 (bytes seed.val) (adrsS a)

def SmallLeaves {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) : Prop :=
  ∀ (K : Usize), (K=2#usize ∨ K=4#usize) → ∀ (first : U32), first.val+K.val≤512 →
    kernel.small K sk seed first a ⦃ rows => LeafRows p sk seed a first.val rows ⦄

def FullLeaves {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) : Prop :=
  ∀ (first : U32), first.val+8≤512 →
    kernel.leaves sk seed first a ⦃ rows => LeafRows p sk seed a first.val rows ⦄

end slhdsa.Buffered
