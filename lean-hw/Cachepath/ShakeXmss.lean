import Cacheops.Funs
import Slhdsa.Proofs.ShakeXmss

/-! Equality of the extracted cache XMSS operations with the verified portable XMSS code.
The cache uses range iterators where the portable implementation uses explicit counters. -/
open Aeneas Aeneas.Std Result CacheopsRust
namespace slhdsa.cache.endtoend.shake

/-- Address encoding and the two ordered child absorptions match the portable hash. -/
theorem thash_pair_eq {N : Usize} (seed l r : Array U8 N) (a : CacheopsRust.address.Adrs) :
    CacheopsRust.cache.shake_ops.thash_pair seed a l r =
      slhdsa.shake.hash.thash_pair seed (toSlhAdrs a) l r := rfl

private theorem bind_same {α β : Type} (m : Result α) (f g : α → Result β)
    (h : ∀ x, f x = g x) : Bind.bind m f = Bind.bind m g := congrArg (Bind.bind m) (funext h)

private theorem sign_loop_eq {N : Usize} (p : CacheopsRust.params.Params) (sk seed : Array U8 N)
    (idx : U32) (a : CacheopsRust.address.Adrs) (it : core.ops.range.Range U32) (sig : alloc.vec.Vec U8)
    (stop : it.end = p.hp) : CacheopsRust.cache.shake_ops.xmss_sign_loop it sk idx seed a sig =
      slhdsa.shake.xmss.xmss_sign_loop (toSlhParams p) sk idx seed (toSlhAdrs a) sig it.start := by
  unfold CacheopsRust.cache.shake_ops.xmss_sign_loop slhdsa.shake.xmss.xmss_sign_loop
  conv_lhs => rw [loop.eq_def]
  conv_rhs => rw [loop.eq_def]
  simp only [CacheopsRust.cache.shake_ops.xmss_sign_loop.body, slhdsa.shake.xmss.xmss_sign_loop.body]
  by_cases more : it.start.val < it.end.val
  · obtain ⟨⟨o,nxt⟩,step,ho,hn,hen⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_some_spec it more)
    have lt : it.start < (toSlhParams p).hp := by change it.start.val < p.hp.val; rwa [← stop]
    have room : it.start.val + 1 ≤ U32.max := by
      have b : it.end.val ≤ U32.max := by scalar_tac
      omega
    obtain ⟨j,add,hj⟩ := spec_imp_exists (U32.add_spec (x:=it.start) (y:=1#u32) room)
    have jn : j=nxt.start := by scalar_tac
    subst o
    simp only [step, uncurry, bind_ok,lt,ite_true,Std.bind_assoc,add,jn]
    iterate 5 (apply bind_same; intro v)
    exact sign_loop_eq p sk seed idx a nxt _ (hen.trans stop)
  · obtain ⟨⟨o,nxt⟩,step,ho,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_none_spec it (by omega))
    have no : ¬it.start < (toSlhParams p).hp := by change ¬it.start.val < p.hp.val; rwa [← stop]
    subst o
    simp only [step, uncurry, bind_ok,no,ite_false]
termination_by it.end.val-it.start.val
decreasing_by rw [hen,hn]; omega

/-- The complete cached XMSS sign vector agrees byte-for-byte with portable XMSS. -/
theorem xmss_sign_eq {N : Usize} (p : CacheopsRust.params.Params) (m sk : Array U8 N) (idx : U32)
    (seed : Array U8 N) (a : CacheopsRust.address.Adrs) :
    CacheopsRust.cache.shake_ops.xmss_sign p m sk idx seed a =
      slhdsa.shake.xmss.xmss_sign (toSlhParams p) m sk idx seed (toSlhAdrs a) := by
  unfold CacheopsRust.cache.shake_ops.xmss_sign slhdsa.shake.xmss.xmss_sign
  simp only [CacheopsRust.address.Adrs.with_type,CacheopsRust.address.Adrs.with_keypair,
    address.Adrs.with_type,address.Adrs.with_keypair,CacheopsRust.address.WOTS_HASH,address.WOTS_HASH,bind_ok]
  apply bind_same; intro sig
  exact sign_loop_eq p sk seed idx a _ sig rfl

private theorem climb_loop_eq {N : Usize} (auth : Slice U8) (first : Usize)
    (seed : Array U8 N) (a : CacheopsRust.address.Adrs) (it : core.ops.range.Range U32)
    (node : Array U8 N) (idx : U32) :
    CacheopsRust.cache.shake_ops.climb_loop it node idx auth first seed a =
      slhdsa.shake.xmss.climb_loop auth first it.end seed (toSlhAdrs a) node idx it.start := by
  unfold CacheopsRust.cache.shake_ops.climb_loop slhdsa.shake.xmss.climb_loop
  conv_lhs => rw [loop.eq_def]
  conv_rhs => rw [loop.eq_def]
  simp only [CacheopsRust.cache.shake_ops.climb_loop.body, slhdsa.shake.xmss.climb_loop.body]
  by_cases more : it.start < it.end
  · obtain ⟨⟨o,nxt⟩,step,ho,hn,hen⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_some_spec it more)
    have room : it.start.val + 1 ≤ U32.max := by scalar_tac
    obtain ⟨j,add,hj⟩ := spec_imp_exists (U32.add_spec (x:=it.start) (y:=1#u32) room)
    have jn : j = nxt.start := by scalar_tac
    subst o
    simp only [step,uncurry,bind_ok,more,ite_true,Std.bind_assoc,add,jn,
      CacheopsRust.address.Adrs.with_word2,CacheopsRust.address.Adrs.with_word3,
      address.Adrs.with_word2,address.Adrs.with_word3]
    iterate 5 (apply bind_same; intro v)
    rename_i sibling parent
    split <;> simp only [Std.bind_assoc, bind_ok] <;> apply bind_same <;> intro child <;>
      simpa only [←hen, CacheopsRust.cache.shake_ops.climb_loop, slhdsa.shake.xmss.climb_loop,
        CacheopsRust.cache.shake_ops.climb_loop.body, slhdsa.shake.xmss.climb_loop.body,
        CacheopsRust.address.Adrs.with_word2,CacheopsRust.address.Adrs.with_word3,
        address.Adrs.with_word2,address.Adrs.with_word3,uncurry,Std.bind_assoc,bind_ok]
        using climb_loop_eq auth first seed a nxt child parent
  · obtain ⟨⟨o,nxt⟩,step,ho,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_none_spec it (by scalar_tac))
    subst o
    simp only [step,uncurry,bind_ok,more,ite_false]
termination_by it.end.val-it.start.val
decreasing_by all_goals change it.start.val < it.end.val at more; rw [hen, hn]; omega

/-- The shared SHAKE authentication-path routine agrees at every height and offset. -/
theorem climb_eq {N : Usize} (node : Array U8 N) (idx : U32) (auth : Slice U8) (first : Usize)
    (height : U32) (seed : Array U8 N) (a : CacheopsRust.address.Adrs) :
    CacheopsRust.cache.shake_ops.climb node idx auth first height seed a =
      slhdsa.shake.xmss.climb node idx auth first height seed (toSlhAdrs a) :=
  climb_loop_eq auth first seed a ⟨0#u32,height⟩ node idx

/-- The complete cached XMSS recovery agrees with portable XMSS on every input. -/
theorem xmss_pk_from_sig_eq {N : Usize} (p : CacheopsRust.params.Params) (idx : U32)
    (sig : Slice U8) (m seed : Array U8 N) (a : CacheopsRust.address.Adrs) :
    CacheopsRust.cache.shake_ops.xmss_pk_from_sig p idx sig m seed a =
      slhdsa.shake.xmss.xmss_pk_from_sig (toSlhParams p) idx sig m seed (toSlhAdrs a) := by
  unfold CacheopsRust.cache.shake_ops.xmss_pk_from_sig slhdsa.shake.xmss.xmss_pk_from_sig
  simp only [CacheopsRust.address.Adrs.with_type,CacheopsRust.address.Adrs.with_keypair,
    address.Adrs.with_type,address.Adrs.with_keypair,CacheopsRust.address.WOTS_HASH,address.WOTS_HASH,
    CacheopsRust.address.TREE,address.TREE,CacheopsRust.params.LEN2,params.LEN2,bind_ok]
  iterate 3 (apply bind_same; intro v)
  apply climb_loop_eq

end slhdsa.cache.endtoend.shake
