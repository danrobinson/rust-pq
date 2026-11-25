import Armwide.HashRouteProgram
import Armwide.Kernel
namespace slhdsa.Armwide.Transitions
open Spec.SHA256
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A tail or four-lane mixed-head step, or a shared-head step of length 1–15. -/
inductive Mode
  | mixed (countMinusOne : Fin 4)
  | shared (stepsMinusOne : Fin 15)
  deriving DecidableEq

def lanes : Mode → Nat
  | .mixed n => n.val+1
  | .shared _ => 4

private def hashRoute (m : Mode) (j : Fin (lanes m)) : HashTrace :=
  let start := match m with
    | .mixed n => #[0,1,3,6][n.val]!
    | .shared k => 10+4*k.val
  hashes[start+j.val]!

private def expected (m : Mode) (j : Nat) : HashTrace :=
  match m with
  | .mixed _ => ⟨j,[⟨j,j,j,0⟩]⟩
  | .shared k => ⟨j,(List.range (k.val+1)).map fun i => ⟨4,j,j,i⟩⟩

private theorem routed (m : Mode) (j : Fin (lanes m)) : hashRoute m j = expected m j := by
  cases m with
  | mixed n => exact (by decide : ∀ n, ∀ j, hashRoute (.mixed n) j = expected (.mixed n) j) n j
  | shared k => exact (by decide : ∀ k, ∀ j, hashRoute (.shared k) j = expected (.shared k) j) k j

/-- Hashing begins at the prepared SHA-256 chaining state. The message block is assembled
from the chosen head, addressed suffix, chain counter, and incoming digest. -/
structure Inputs where
  state : Fin 8 → Word
  block : Nat → Nat → Nat → Spec.Bytes → Fin 64 → Spec.Byte
  chains : Nat → Nat
  counters : Nat → Nat
  initial : Nat → Spec.Bytes

private def blockFor (r : Inputs) (op : HashCall) (x : Spec.Bytes) : Spec.Bytes :=
  List.ofFn (r.block op.head (r.chains op.chain) (r.counters op.counter + op.increment) x)

/-- Rounds 0–3 prepare the head. Rounds 4–63 consume the three suffix vectors and use
the width-specific feed-forward. The result represents both destination registers. -/
private def nativeHash (n : Nat) (r : Inputs) (op : HashCall) (x : Spec.Bytes) : Spec.Bytes :=
  let b := blockFor r op x
  let st := List.ofFn r.state
  let (m0,a1,e1) := Kernel.makeHead st b
  let (lo,hi) := Kernel.finishFromR4 (n != 16) st a1 e1 m0 (beV b 16) (beV b 32) (beV b 48)
  Kernel.storeN n lo hi

private def fipsHash (n : Nat) (r : Inputs) (op : HashCall) (x : Spec.Bytes) : Spec.Bytes :=
  ((compress (List.ofFn r.state) (blockFor r op x)).flatMap (fun w => Spec.toByte w.toNat 4)).take n

def registerDigest (n : Nat) (r : Inputs) (m : Mode) (j : Fin (lanes m)) : Spec.Bytes :=
  let p := hashRoute m j
  p.calls.foldl (fun x op => nativeHash n r op x) (r.initial p.origin)

/-- Arbitrary prepared state and blocks. Every active lane uses its own digest, chain and
counter; shared-head calls advance the same lane by exactly the requested number of rounds. -/
theorem register_digest_fips (n : Nat) (hn : n=16 ∨ n=24 ∨ n=32) (r : Inputs) (m : Mode)
    (j : Fin (lanes m)) :
    registerDigest n r m j =
      (expected m j).calls.foldl (fun x op => fipsHash n r op x) (r.initial j) := by
  have eq (op : HashCall) (x : Spec.Bytes) : nativeHash n r op x = fipsHash n r op x :=
    Kernel.finishFromR4_storeN_eq_fips n hn (List.ofFn r.state) (by simp)
      (blockFor r op x) (by simp [blockFor])
  simp only [registerDigest,routed,eq]
  cases m <;> rfl

end slhdsa.Armwide.Transitions
