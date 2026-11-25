import Cachepath.ShakeClosed

/-! The portable target compiles away the runtime detector and all SIMD calls.
The extraction checker matches these five bodies directly. -/
open Aeneas Aeneas.Std Result slhdsa
namespace slhdsa.PortableCache
open slhdsa.CacheScalar

def cache.shake_ops.wots_sign
  {N : Std.Usize} (msg : Array Std.U8 N) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let digits ← wots.wots_digits msg
  let i := alloc.vec.Vec.len digits
  let i1 ← i * N
  let sig := alloc.vec.Vec.with_capacity Std.U8 i1
  let s := alloc.vec.Vec.deref digits
  let i2 ← core.slice.Slice.iter s
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) i2
  cache.shake_ops.wots_sign_loop iter sk seed adrs sig

theorem wots_sign_scalar : @cache.shake_ops.wots_sign = @CacheScalar.cache.shake_ops.wots_sign CacheopsRust.Closed.scalar.toAcceleration := by
  funext N a b c d
  have det : @Acceleration.available CacheopsRust.Closed.scalar.toAcceleration N = ok false := rfl
  simp only [cache.shake_ops.wots_sign, CacheScalar.cache.shake_ops.wots_sign, CacheScalar.cache.shake_ops.simd.available, det,
    lift, bind_ok, Bool.false_eq_true, ite_false]

def cache.shake_ops.wots_pk_from_sig
  {N : Std.Usize} (sig : Slice Std.U8) (msg : Array Std.U8 N)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let digits ← wots.wots_digits msg
  let a ← address.Adrs.with_type adrs address.WOTS_PK
  let a1 ← address.Adrs.with_keypair a adrs.keypair
  let pk ← cache.shake_ops.start seed a1
  let s := alloc.vec.Vec.deref digits
  let i ← core.slice.Slice.iter s
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) i
  let pk1 ←
    cache.shake_ops.wots_pk_from_sig_loop iter sig seed adrs.layer adrs.tree
      adrs.typ adrs.keypair adrs.word2 adrs.word3 pk
  cache.shake_ops.digest N pk1

theorem wots_pk_from_sig_scalar : @cache.shake_ops.wots_pk_from_sig = @CacheScalar.cache.shake_ops.wots_pk_from_sig CacheopsRust.Closed.scalar.toAcceleration := by
  funext N a b c d
  have det : @Acceleration.available CacheopsRust.Closed.scalar.toAcceleration N = ok false := rfl
  simp only [cache.shake_ops.wots_pk_from_sig, CacheScalar.cache.shake_ops.wots_pk_from_sig, CacheScalar.cache.shake_ops.simd.available, det,
    lift, bind_ok, Bool.false_eq_true, ite_false]

def cache.shake_ops.fors_sign
  {N : Std.Usize} (p : params.Params) (md : Slice Std.U8) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let i ← lift (UScalar.cast .Usize p.k)
  let indices ← util.base_2b md p.a i
  let i1 ← params.Params.fors_sig_bytes p
  let sig := alloc.vec.Vec.with_capacity Std.U8 i1
  let s := alloc.vec.Vec.deref indices
  let i2 ← core.slice.Slice.iter s
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) i2
  cache.shake_ops.fors_sign_loop0 iter p.a sk seed adrs sig

theorem fors_sign_scalar : @cache.shake_ops.fors_sign = @CacheScalar.cache.shake_ops.fors_sign CacheopsRust.Closed.scalar.toAcceleration := by
  funext N p a b c d
  have det : @Acceleration.available CacheopsRust.Closed.scalar.toAcceleration N = ok false := rfl
  simp only [cache.shake_ops.fors_sign, CacheScalar.cache.shake_ops.fors_sign, CacheScalar.cache.shake_ops.simd.available, det,
    lift, bind_ok, Bool.false_eq_true, ite_false]

def cache.shake_ops.fors_pk_from_sig
  {N : Std.Usize} (p : params.Params) (sig : Slice Std.U8) (md : Slice Std.U8)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let i ← lift (UScalar.cast .Usize p.k)
  let indices ← util.base_2b md p.a i
  let a ← address.Adrs.with_type adrs address.FORS_ROOTS
  let a1 ← address.Adrs.with_keypair a adrs.keypair
  let roots ← cache.shake_ops.start seed a1
  let s := alloc.vec.Vec.deref indices
  let i1 ← core.slice.Slice.iter s
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) i1
  let roots1 ←
    cache.shake_ops.fors_pk_from_sig_loop iter p.a sig seed adrs.layer
      adrs.tree adrs.typ adrs.keypair adrs.word2 adrs.word3 roots
  cache.shake_ops.digest N roots1

theorem fors_pk_from_sig_scalar : @cache.shake_ops.fors_pk_from_sig = @CacheScalar.cache.shake_ops.fors_pk_from_sig CacheopsRust.Closed.scalar.toAcceleration := by
  funext N p a b c d
  have det : @Acceleration.available CacheopsRust.Closed.scalar.toAcceleration N = ok false := rfl
  simp only [cache.shake_ops.fors_pk_from_sig, CacheScalar.cache.shake_ops.fors_pk_from_sig, CacheScalar.cache.shake_ops.simd.available, det,
    lift, bind_ok, Bool.false_eq_true, ite_false]

end slhdsa.PortableCache

namespace CacheopsRust.PortableCache
abbrev cache.shake_ops.wots_pk_gen_portable {N : Usize} (sk seed : Array U8 N) (a : address.Adrs) :=
  slhdsa.CacheScalar.cache.shake_ops.wots_pk_gen_portable sk seed (toSlhAdrs a)

def cache.shake_ops.xmss_node
  {N : Std.Usize} (sk : Array Std.U8 N) (i : Std.U32) (z : Std.U32)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  if z = 0#u32
  then
    let a ← address.Adrs.with_type adrs address.WOTS_HASH
    let a1 ← address.Adrs.with_keypair a i
    cache.shake_ops.wots_pk_gen_portable sk seed a1
  else
    let i1 ← 2#u32 * i
    let i2 ← z - 1#u32
    let l ← cache.shake_ops.xmss_node sk i1 i2 seed adrs
    let i3 ← i1 + 1#u32
    let r ← cache.shake_ops.xmss_node sk i3 i2 seed adrs
    let a ← address.Adrs.with_type adrs address.TREE
    let a1 ← address.Adrs.with_word2 a z
    let a2 ← address.Adrs.with_word3 a1 i
    cache.shake_ops.thash_pair seed a2 l r
partial_fixpoint

theorem node_scalar {N : Usize} (sk : Array U8 N) (i z : U32) (seed : Array U8 N) (a : address.Adrs) :
    cache.shake_ops.xmss_node sk i z seed a = @Closed.cache.shake_ops.xmss_node Closed.scalar N sk i z seed a := by
  conv_lhs => rw [cache.shake_ops.xmss_node.eq_def]
  conv_rhs => unfold Closed.cache.shake_ops.xmss_node; rw [ShakeNode.node.eq_def]
  have det : @slhdsa.CacheScalar.Acceleration.available Closed.scalar.toAcceleration N = ok false := rfl
  simp only [det,bind_ok, Bool.false_eq_true, ite_false]
  by_cases zero : z = 0#u32
  · simp only [zero,ite_true]
  · obtain ⟨next,sub,hn⟩ := spec_imp_exists (U32.sub_spec (x := z) (y := 1#u32) (by scalar_tac))
    simp only [zero,ite_false,sub,bind_ok]
    have ih (idx : U32) := node_scalar sk idx next seed a
    simp only [ih]
termination_by z.val
decreasing_by scalar_tac

end CacheopsRust.PortableCache
