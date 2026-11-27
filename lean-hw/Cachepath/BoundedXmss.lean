import Cachepath.ShakeClosedProgram
open Aeneas Aeneas.Std Result ControlFlow slhdsa
namespace CacheopsRust.Closed
variable [backend : Backend]

theorem bounded_wots_eq {N : Usize} [correct : DispatchCorrect backend N] (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (m sk seed : Array U8 N) (a : CacheopsRust.address.Adrs) :
    cache.shake_ops.wots_sign m sk seed a = CacheopsRust.cache.shake_ops.wots_sign m sk seed a := by
  obtain ⟨flag, det⟩ := correct.available
  cases flag with
  | false => exact CacheScalar.wots_sign_eq _ hp det _ _ _ _
  | true =>
    simpa only [cache.shake_ops.wots_sign, CacheScalar.cache.shake_ops.wots_sign,
      CacheScalar.cache.shake_ops.simd.available, det, bind_ok, ite_true] using
      (correct.fast det).wotsSign m sk seed (toSlhAdrs a)

private theorem node_eq_at {N : Usize} [correct : DispatchCorrect backend N] (hn : N.val ≤ 32)
    (sk : Array U8 N) (i z : U32) (seed : Array U8 N) (a : CacheopsRust.address.Adrs)
    (small : z.val ≤ 9) (fits : (i.val+1)*2^z.val ≤ 512) :
    cache.shake_ops.xmss_node sk i z seed a = CacheopsRust.cache.shake_ops.xmss_node sk i z seed a := by
  obtain ⟨flag,det⟩ := correct.available
  cases flag with
  | false => exact ShakeNode.scalar_node_eq _ _ hn det _ _ _ _ _
  | true =>
    unfold cache.shake_ops.xmss_node
    rw [ShakeNode.node.eq_def]
    simp only [det,bind_ok,ite_true]
    exact (correct.fast det).subtree sk i z seed a small fits

private theorem bindEq {α β : Type} (r : Result α) (f g : α → Result β) (h : ∀ x, f x = g x) :
    (r >>= f) = (r >>= g) := congrArg (r >>= ·) (funext h)

private theorem bounded_loop {N : Usize} [DispatchCorrect backend N] (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N) (sk seed : Array U8 N) (idx : U32) (a : CacheopsRust.address.Adrs)
    (it : core.ops.range.Range U32) (sig : alloc.vec.Vec U8) (stop : it.end = p.hp)
    (bound : idx.val < 2^p.hp.val) :
    cache.shake_ops.xmss_sign_loop it sk idx seed a sig =
      CacheopsRust.cache.shake_ops.xmss_sign_loop it sk idx seed a sig := by
  unfold cache.shake_ops.xmss_sign_loop CacheopsRust.cache.shake_ops.xmss_sign_loop
  conv_lhs => rw [loop.eq_def]
  conv_rhs => rw [loop.eq_def]
  simp only [cache.shake_ops.xmss_sign_loop.body,CacheopsRust.cache.shake_ops.xmss_sign_loop.body]
  by_cases more : it.start.val < it.end.val
  · obtain ⟨⟨o,next⟩,run,item,inc,last⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_some_spec it more)
    have live : it.start.val < p.hp.val := stop ▸ more
    have maxH : p.hp.val ≤ 9 := hp.valid.hp_le
    obtain ⟨v,shift,num,_⟩ := spec_imp_exists (U32.ShiftRight_spec idx it.start (by scalar_tac))
    let sibling := v ^^^ 1#u32
    have hs : sibling.val = (idx.val / 2^it.start.val) ^^^ 1 := by
      simp [sibling,UScalar.val_xor,num,Nat.shiftRight_eq_div_pow]
    have pow : 2^(p.hp.val-it.start.val)*2^it.start.val = 2^p.hp.val := by
      rw [← Nat.pow_add,Nat.sub_add_cancel (by omega)]
    have q := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos it.start.val)).2 (pow.symm ▸ bound)
    have one : 1 < 2^(p.hp.val-it.start.val) := lt_of_lt_of_le (by decide : 1 < 2^1)
      (Nat.pow_le_pow_right (by decide) (by omega))
    have fits : (sibling.val+1)*2^it.start.val ≤ 512 := by
      rw [hs]
      exact (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (Nat.xor_lt_two_pow q one))).trans
        (pow ▸ Nat.pow_le_pow_right (by decide : 0 < 2) maxH)
    simp only [run,item,shift,bind_ok,lift,uncurry,Std.bind_assoc,
      node_eq_at hp.le32 sk sibling it.start seed a (by omega) fits]
    rw [node_eq_at hp.le32 sk (v ^^^ 1#u32) it.start seed a (by omega) fits]
    apply bindEq; intro value
    apply bindEq; intro nextSig
    simpa only [cache.shake_ops.xmss_sign_loop,CacheopsRust.cache.shake_ops.xmss_sign_loop,
      cache.shake_ops.xmss_sign_loop.body,CacheopsRust.cache.shake_ops.xmss_sign_loop.body,
      bind_ok,lift,uncurry,Std.bind_assoc] using bounded_loop p hp sk seed idx a next nextSig (last.trans stop) bound
  · obtain ⟨⟨o,next⟩,run,item,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_none_spec it (by omega))
    simp only [run,item,bind_ok,uncurry]
termination_by it.end.val-it.start.val
decreasing_by rw [last,inc]; omega

theorem bounded_xmss_sign_eq {N : Usize} [DispatchCorrect backend N] (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N) (m sk : Array U8 N) (idx : U32) (seed : Array U8 N)
    (a : CacheopsRust.address.Adrs) (bound : idx.val < 2^p.hp.val) :
    cache.shake_ops.xmss_sign p m sk idx seed a = CacheopsRust.cache.shake_ops.xmss_sign p m sk idx seed a := by
  unfold cache.shake_ops.xmss_sign CacheopsRust.cache.shake_ops.xmss_sign
  simp only [bounded_wots_eq p hp]
  iterate 3 (apply bindEq; intro _)
  exact bounded_loop p hp sk seed idx a _ _ rfl bound

end CacheopsRust.Closed
