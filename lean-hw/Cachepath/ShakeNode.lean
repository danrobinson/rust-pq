import Cachepath.ShakeScalar

/-! The recursive cache node dispatcher, parameterized by hardware availability and
its two leaf providers. The extraction audit specializes these parameters back to Rust. -/
open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.ShakeNode

abbrev FastNode := ∀ {N : Usize}, Array U8 N → U32 → U32 → Array U8 N → address.Adrs →
  Result (Array U8 N)
abbrev LeafNode := ∀ {N : Usize}, Array U8 N → Array U8 N → address.Adrs → Result (Array U8 N)

def node (available : Usize → Result Bool) (fast : FastNode) (leaf : LeafNode)
  {N : Std.Usize} (sk : Array Std.U8 N) (i : Std.U32) (z : Std.U32)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let b ← available N
  if b
  then fast sk i z seed adrs
  else
    if z = 0#u32
    then
      let a ← address.Adrs.with_type adrs address.WOTS_HASH
      let a1 ← address.Adrs.with_keypair a i
      leaf sk seed a1
    else
      let i1 ← 2#u32 * i
      let i2 ← z - 1#u32
      let l ← node available fast leaf sk i1 i2 seed adrs
      let i3 ← i1 + 1#u32
      let r ← node available fast leaf sk i3 i2 seed adrs
      let a ← address.Adrs.with_type adrs address.TREE
      let a1 ← address.Adrs.with_word2 a z
      let a2 ← address.Adrs.with_word3 a1 i
      cache.shake_ops.thash_pair seed a2 l r
partial_fixpoint

private theorem node_by_flag (available : Usize → Result Bool) (fast : FastNode) (leaf : LeafNode)
    {N : Usize} (flag : Bool) (detect : available N = ok flag)
    (hfast : flag = true → ∀ (sk : Array U8 N) i z seed a, fast sk i z seed a =
      slhdsa.shake.xmss.xmss_node sk i z seed (toSlhAdrs a))
    (hleaf : ∀ (sk seed : Array U8 N) a, leaf sk seed a =
      slhdsa.shake.wots.wots_pk_gen sk seed (toSlhAdrs a))
    (sk : Array U8 N) (i z : U32) (seed : Array U8 N) (a : address.Adrs) :
    node available fast leaf sk i z seed a = cache.shake_ops.xmss_node sk i z seed a := by
  conv_lhs => rw [node.eq_def]
  simp only [detect, bind_ok]
  cases flag
  · change _ = slhdsa.shake.xmss.xmss_node sk i z seed (toSlhAdrs a)
    conv_rhs => rw [slhdsa.shake.xmss.xmss_node.eq_def]
    by_cases zero : z = 0#u32
    · simp only [zero, ↓reduceIte, Bool.false_eq_true, hleaf, address.Adrs.with_type,
        address.Adrs.with_keypair, slhdsa.address.Adrs.with_type, slhdsa.address.Adrs.with_keypair,
        address.WOTS_HASH, slhdsa.address.WOTS_HASH, bind_ok]
    · have hz : 1 ≤ z.val := by scalar_tac
      obtain ⟨next, sub, hn⟩ := spec_imp_exists (U32.sub_spec (x:=z) (y:=1#u32) hz)
      simp only [zero, ↓reduceIte, Bool.false_eq_true, sub, bind_ok,
        address.Adrs.with_type, address.Adrs.with_word2, address.Adrs.with_word3,
        slhdsa.address.Adrs.with_type, slhdsa.address.Adrs.with_word2, slhdsa.address.Adrs.with_word3,
        address.TREE, slhdsa.address.TREE]
      have subtree (idx : U32) := node_by_flag available fast leaf false detect hfast hleaf sk idx next seed a
      simp only [subtree]
      rfl
  · exact hfast rfl sk i z seed a
termination_by z.val
decreasing_by scalar_tac

/-- Either runtime decision produces the portable XMSS node under the two provider contracts. -/
theorem node_eq (available : Usize → Result Bool) (fast : FastNode) (leaf : LeafNode)
    {N : Usize} (flag : Bool) (detect : available N = ok flag)
    (hfast : ∀ (sk : Array U8 N) i z seed a, fast sk i z seed a =
      slhdsa.shake.xmss.xmss_node sk i z seed (toSlhAdrs a))
    (hleaf : ∀ (sk seed : Array U8 N) a, leaf sk seed a =
      slhdsa.shake.wots.wots_pk_gen sk seed (toSlhAdrs a))
    (sk : Array U8 N) (i z : U32) (seed : Array U8 N) (a : address.Adrs) :
    node available fast leaf sk i z seed a = cache.shake_ops.xmss_node sk i z seed a :=
  node_by_flag available fast leaf flag detect (fun _ => hfast) hleaf sk i z seed a

/-- The concrete scalar XMSS dispatcher uses the verified cache WOTS leaf at every height. -/
theorem scalar_node_eq (available : Usize → Result Bool) (fast : FastNode)
    {N : Usize} (size : N.val ≤ 32) (scalar : available N = ok false)
    (sk : Array U8 N) (i z : U32) (seed : Array U8 N) (a : address.Adrs) :
    node available fast
        (fun sk seed adrs => slhdsa.CacheScalar.cache.shake_ops.wots_pk_gen_portable sk seed (toSlhAdrs adrs))
        sk i z seed a = cache.shake_ops.xmss_node sk i z seed a :=
  node_by_flag available fast _ false scalar (by simp)
    (fun sk seed a => slhdsa.CacheScalar.wots_pk_gen_eq size sk seed (toSlhAdrs a)) sk i z seed a

end CacheopsRust.ShakeNode
