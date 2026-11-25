import Armwide.FusedNative
import Armwide.SignOrder
import Slhdsa.Proofs.Wots

open Aeneas Aeneas.Std Result

namespace slhdsa.Armwide.Public

/-- Rust builds the shared F head by resetting the address type and restoring the keypair. -/
def hashAddress (a : Spec.Adrs) : Spec.Adrs := {a.setTypeAndClear Spec.WOTS_HASH with keypair := a.keypair}

def signRows (n : Nat) (state : List Spec.SHA256.Word) (sk : Spec.Bytes) (a : Spec.Adrs)
    (digits : Nat → Nat) (order : List Nat) :=
  let base := hashAddress a
  WotsRefill.signFusedUsing sk digits order (Transitions.four n state sk base digits)
    (Transitions.tail n state base)

def sha256.arm_wide.wots_sign_fused {N : Usize} (state : Array U32 8#usize)
    (sk : Array U8 N) (a : slhdsa.address.Adrs) (ds : Slice U32) (out : Slice U8) : Result (Slice U8) := do
  let sorted ← SignOrder.sha256.arm_wide.sign_order ds
  let order := (sorted.val.take ds.length).map (·.val)
  let rows := signRows N.val (wv state.val) (bytes sk.val) (slhdsa.adrsS a) (fun i => ds.val[i]!.val) order
  let result := (List.range ds.length).flatMap rows
  ok (Slice.from (out.val.setSlice! 0 (result.map UScalar.mk)) (by simpa using out.property))

abbrev wots.arm.wots_digits_stack := @ArmwideRust.wots.arm.wots_digits_stack

def wots.arm.sign
  {N : Std.Usize} (m : Array Std.U8 N) (sk_seed : Array Std.U8 N)
  (seed : hash.Seed N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let i ← 2#usize * N
  let len ← i + params.LEN2
  let digits ← wots.arm.wots_digits_stack m
  let i1 ← len * N
  let sig ← alloc.vec.from_elem core.clone.CloneU8 0#u8 i1
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) digits
      { «end» := len }
  let (s1, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut sig)
  let s2 ← sha256.arm_wide.wots_sign_fused seed.state sk_seed adrs s s1
  ok (deref_mut_back s2)

end slhdsa.Armwide.Public
