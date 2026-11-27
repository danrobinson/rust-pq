import Cachepath.ShakeNode

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.Closed

/-- Runtime dispatch interfaces emitted by the cache signer extraction. -/
class Backend extends slhdsa.CacheScalar.Acceleration where
  subtree : ShakeNode.FastNode

/-- The scalar configuration never evaluates its hardware callbacks. -/
instance scalar : Backend where
  available := fun _ => ok false
  wots_sign := fun _ _ _ _ => fail .panic
  wots_pk_from_sig := fun _ _ _ _ => fail .panic
  fors_sign := fun _ _ _ _ _ => fail .panic
  fors_pk_from_sig := fun _ _ _ _ _ => fail .panic
  subtree := fun _ _ _ _ _ => fail .panic

/-- The five hardware calls, with exactly the digit/index slices produced by Rust.
The common caller is responsible for decoding, selecting, and sequencing them. -/
structure FastSpec (b : Backend) (N : Usize) : Prop where
  wotsSign : ∀ (m sk seed : Array U8 N) a,
    (do let d ← slhdsa.wots.wots_digits m
        b.wots_sign sk seed a (alloc.vec.Vec.deref d)) = shake.wots.wots_sign m sk seed a
  wotsRecover : ∀ sig (m seed : Array U8 N) a,
    (do let d ← slhdsa.wots.wots_digits m
        b.wots_pk_from_sig sig seed a (alloc.vec.Vec.deref d)) = shake.wots.wots_pk_from_sig sig m seed a
  forsSign : ∀ p (md : Slice U8) (sk seed : Array U8 N) a, PN p N →
    md.length = (p.k.val * p.a.val + 7) / 8 →
    (do let d ← slhdsa.util.base_2b md p.a (UScalar.cast .Usize p.k)
        b.fors_sign p (alloc.vec.Vec.deref d) sk seed a) = shake.fors.fors_sign p md sk seed a
  forsRecover : ∀ p (sig md : Slice U8) (seed : Array U8 N) a, PN p N →
    sig.length = p.k.val * (1+p.a.val) * N.val →
    md.length = (p.k.val * p.a.val + 7) / 8 →
    (do let d ← slhdsa.util.base_2b md p.a (UScalar.cast .Usize p.k)
        b.fors_pk_from_sig p (alloc.vec.Vec.deref d) sig seed a) = shake.fors.fors_pk_from_sig p sig md seed a
  subtree : ∀ (sk : Array U8 N) (i z : U32) seed a, z.val ≤ 9 → (i.val+1)*2^z.val ≤ 512 →
    b.subtree sk i z seed a =
    shake.xmss.xmss_node sk i z seed (toSlhAdrs a)

/-- Only an enabled accelerator owes its hardware contracts. -/
class DispatchCorrect (b : Backend) (N : Usize) : Prop where
  available : ∃ flag, b.available N = ok flag
  fast : b.available N = ok true → FastSpec b N

instance (N : Usize) : DispatchCorrect scalar N where
  available := ⟨false, rfl⟩
  fast := by intro h; change (ok false : Result Bool) = ok true at h; simp only [ok.injEq, Bool.false_eq_true] at h

end CacheopsRust.Closed
