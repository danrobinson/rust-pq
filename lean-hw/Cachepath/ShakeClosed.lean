import Cachepath.BoundedXmss
import Cachepath.ShakeEndToEnd

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.Closed

set_option linter.concreteInstances false
variable [backend : Backend]

private theorem xmss_recover_eq {N : Usize} [correct : DispatchCorrect backend N] (p : CacheopsRust.params.Params) (idx : U32)
    (sig : Slice U8) (m seed : Array U8 N) (a : CacheopsRust.address.Adrs) :
    cache.shake_ops.xmss_pk_from_sig p idx sig m seed a = CacheopsRust.cache.shake_ops.xmss_pk_from_sig p idx sig m seed a := by
  have recover (a : CacheopsRust.address.Adrs) : cache.shake_ops.wots_pk_from_sig sig m seed a =
      CacheopsRust.cache.shake_ops.wots_pk_from_sig sig m seed a := by
    obtain ⟨flag, det⟩ := correct.available
    cases flag with
    | false => exact CacheScalar.wots_recover_eq det _ _ _ _
    | true =>
      simpa only [cache.shake_ops.wots_pk_from_sig, CacheScalar.cache.shake_ops.wots_pk_from_sig,
        CacheScalar.cache.shake_ops.simd.available, det, bind_ok, ite_true] using
        (correct.fast det).wotsRecover sig m seed (toSlhAdrs a)
  simp only [cache.shake_ops.xmss_pk_from_sig,CacheopsRust.cache.shake_ops.xmss_pk_from_sig,recover]

omit backend in
private theorem bindSame {α β : Type} (x : Result α) (f g : α → Result β) (h : ∀ v, f v = g v) :
    (x >>= f) = (x >>= g) := congrArg (x >>= ·) (funext h)

private theorem hypertree_eq {N : Usize} [correct : DispatchCorrect backend N] (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (a : CacheopsRust.address.Adrs) (it : core.ops.range.Range U32) (sk seed : Array U8 N)
    (top : Slice (Array U8 N)) (hit : Option (Slice (Array U8 N))) (root : Array U8 N)
    (sig : alloc.vec.Vec U8) (tree : U64) (leaf : U32) (index : leaf.val < 2^p.hp.val) :
    cache.shake_ops.sign_from_digest_loop a it p.n p.h p.d p.hp p.a p.k p.m sk seed top hit root sig tree leaf =
      CacheopsRust.cache.shake_ops.sign_from_digest_loop a it p.n p.h p.d p.hp p.a p.k p.m sk seed top hit root sig tree leaf := by
  have height : p.hp.val ≤ 9 := hp.valid.hp_le
  have width : (1#u64 <<< p.hp) ⦃ v => v.val = 2^p.hp.val ⦄ := by
    step as ⟨v,hv⟩
    exact ht_shl_val v p.hp height hv
  obtain ⟨size,shift,sz⟩ := spec_imp_exists width
  have mask : (size - 1#u64) ⦃ v => v.val = 2^p.hp.val - 1 ⦄ := by
    have positive := Nat.two_pow_pos p.hp.val
    step as ⟨v,hv⟩
    omega
  obtain ⟨mask,sub,maskVal⟩ := spec_imp_exists mask
  have nextBound : (UScalar.cast .U32 (tree &&& mask)).val < 2^p.hp.val := by
    rw [ht_leaf_val tree mask _ p.hp height maskVal rfl]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold cache.shake_ops.sign_from_digest_loop CacheopsRust.cache.shake_ops.sign_from_digest_loop
  conv_lhs => rw [loop.eq_def]; arg 1; dsimp only; rw [cache.shake_ops.sign_from_digest_loop.body]
  conv_rhs => rw [loop.eq_def]; arg 1; dsimp only; rw [CacheopsRust.cache.shake_ops.sign_from_digest_loop.body]
  by_cases active : it.start.val < it.end.val
  · obtain ⟨⟨o,nxt⟩,read,ho,hn,he⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_some_spec it active)
    subst o
    simp only [read,uncurry,bind_ok,Std.bind_assoc,shift,sub,lift,bounded_wots_eq p hp,xmss_recover_eq p,
      bounded_xmss_sign_eq p hp _ _ leaf _ _ index]
    iterate 3 (apply bindSame; intro v)
    split
    · simp only [Std.bind_assoc,bind_ok]
      repeat' (apply bindSame; intro v)
      apply hypertree_eq p hp a nxt sk seed top _ _ _ _ _ nextBound
    · simp only [Std.bind_assoc]
      apply bindSame
      intro d
      split
      · cases hit <;> simp only [Std.bind_assoc,uncurry,bind_ok] <;>
          repeat' (apply bindSame; intro v)
        all_goals apply hypertree_eq p hp a nxt sk seed top _ _ _ _ _ nextBound
      · simp only [Std.bind_assoc,bind_ok]
        repeat' (apply bindSame; intro v)
        apply hypertree_eq p hp a nxt sk seed top _ _ _ _ _ nextBound
  · obtain ⟨⟨o,nxt⟩,read,ho,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_U32_none_spec it (by omega))
    subst o
    simp only [read,uncurry,bind_ok]
termination_by it.end.val-it.start.val
decreasing_by all_goals rw [he,hn]; omega

/-- Equality of complete executions with the serial assembly model, including all signing bytes. -/
theorem sign_from_digest_eq {N : Usize} [correct : DispatchCorrect backend N] (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (sk seed r : Array U8 N) (digest : Slice U8) (hdig : digest.length = p.m.val)
    (top : Slice (Array U8 N)) (hit : Option (Slice (Array U8 N))) :
    cache.shake_ops.sign_from_digest p sk seed r digest top hit =
      CacheopsRust.cache.shake_ops.sign_from_digest p sk seed r digest top hit := by
  obtain ⟨n,hsize,hlen,hm⟩ := spec_imp_exists (md_bytes_spec _ hp.valid)
  have len : CacheopsRust.params.Params.md_bytes p = ok n := hsize
  have hb : n.val ≤ digest.length := by
    have := hp.valid.m_eq
    rw [hdig]
    change n.val ≤ (paramsS (toSlhParams p)).m
    omega
  obtain ⟨md,hm,_,hs⟩ := spec_imp_exists (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    (α:=U8) ⟨0#usize,n⟩ digest (by scalar_tac) hb)
  have slice : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      digest ⟨0#usize,n⟩ = ok md := hm
  have hl : md.length = (p.k.val * p.a.val + 7) / 8 := by simpa [hlen] using hs
  have sign (a : CacheopsRust.address.Adrs) : cache.shake_ops.fors_sign p md sk seed a =
      CacheopsRust.cache.shake_ops.fors_sign p md sk seed a := by
    obtain ⟨flag, det⟩ := correct.available
    cases flag with
    | false => exact CacheScalar.fors_sign_eq _ hp det _ hl _ _ _
    | true =>
      simpa only [cache.shake_ops.fors_sign, CacheScalar.cache.shake_ops.fors_sign, lift,
        CacheScalar.cache.shake_ops.simd.available, det, bind_ok, ite_true] using
        (correct.fast det).forsSign (toSlhParams p) md sk seed (toSlhAdrs a) hp hl
  have recover (s : Slice U8) (a : CacheopsRust.address.Adrs) (sz : s.length = p.k.val*(1+p.a.val)*N.val) : cache.shake_ops.fors_pk_from_sig p s md seed a =
      CacheopsRust.cache.shake_ops.fors_pk_from_sig p s md seed a := by
    obtain ⟨flag, det⟩ := correct.available
    cases flag with
    | false => exact CacheScalar.fors_recover_eq det _ _ _ _ _
    | true =>
      simpa only [cache.shake_ops.fors_pk_from_sig, CacheScalar.cache.shake_ops.fors_pk_from_sig, lift,
        CacheScalar.cache.shake_ops.simd.available, det, bind_ok, ite_true] using
        (correct.fast det).forsRecover (toSlhParams p) s md seed (toSlhAdrs a) hp sz hl
  have afterSign {α : Type} (a : CacheopsRust.address.Adrs) (rest : alloc.vec.Vec U8 → Array U8 N → Result α) :
      (do let sig ← CacheopsRust.cache.shake_ops.fors_sign p md sk seed a
          let root ← cache.shake_ops.fors_pk_from_sig p sig.deref md seed a
          rest sig root) =
      (do let sig ← CacheopsRust.cache.shake_ops.fors_sign p md sk seed a
          let root ← CacheopsRust.cache.shake_ops.fors_pk_from_sig p sig.deref md seed a
          rest sig root) := by
    obtain ⟨sig,run,_,sz⟩ := spec_imp_exists (Shake.fors_sign_spec (toSlhParams p) hp md sk seed (toSlhAdrs a) hl)
    have built : CacheopsRust.cache.shake_ops.fors_sign p md sk seed a = ok sig := run
    rw [built]
    simp only [Bind.bind,bind_ok]
    rw [recover sig.deref a (by simpa only [slhdsa.cache.endtoend.vec_deref_len] using sz)]
  obtain ⟨leaf,decoded,_,index⟩ := spec_imp_exists (slhdsa.cache.endtoend.cache_digest_leaf_spec p digest hp.valid hdig)
  simp only [cache.shake_ops.sign_from_digest, CacheopsRust.cache.shake_ops.sign_from_digest,
    decoded, len, slice, bind_ok, sign, hypertree_eq p hp _ _ _ _ _ _ _ _ _ leaf index]
  iterate 5 (apply bindSame; intro _)
  apply afterSign

open slhdsa.cache.endtoend slhdsa.cache

/-- The cached signer, including lookup and runtime dispatch, produces the FIPS signature bytes
when the selected implementation satisfies its local primitive contracts. -/
theorem sign_from_digest_with_cache_dispatch_spec {N : Usize} [correct : DispatchCorrect backend N] (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N)
    (c : CacheopsRust.cache.TopTreeCache N)
    (sk_seed pk_seed r : Array U8 N) (digest : Slice U8)
    (hdig : digest.length = p.m.val)
    (hc : CacheValid c (Shake.params (toSlhParams p)) (bytes sk_seed.val) (bytes pk_seed.val)) :
    (do
      let tree_d2 ← CacheopsRust.cache.TopTreeCache.layer_d2_tree_index N p digest
      let d2_hit ← CacheopsRust.cache.TopTreeCache.lookup_d2 c tree_d2
      cache.shake_ops.sign_from_digest p sk_seed pk_seed r digest
        (alloc.vec.Vec.deref c.top_tree) d2_hit) ⦃ sig =>
      let P := Shake.params (toSlhParams p)
      let md := (bytes digest.val).take P.mdBytes
      let idxTree := Spec.digestTree P (bytes digest.val)
      let idxLeaf := Spec.digestLeaf P (bytes digest.val)
      let adrs := { { Spec.Adrs.zero with tree := idxTree }.setTypeAndClear
        Spec.FORS_TREE with keypair := idxLeaf }
      let sigFors := Spec.forsSign P md (bytes sk_seed.val) (bytes pk_seed.val) adrs
      let pkFors := Spec.forsPkFromSig P sigFors md (bytes pk_seed.val) adrs
      bytes sig.val = bytes r.val ++ sigFors ++
        Spec.htSign P pkFors (bytes sk_seed.val) (bytes pk_seed.val) idxTree idxLeaf ⦄ := by
  simp only [sign_from_digest_eq p hp sk_seed pk_seed r digest hdig]
  exact slhdsa.cache.endtoend.shake.sign_from_digest_with_cache_spec p hp c sk_seed pk_seed r digest hdig hc

section
omit backend
/-- The actual scalar cached signer, including the cache lookup, produces the FIPS signature bytes. -/
theorem sign_from_digest_with_cache_spec {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N)
    (c : CacheopsRust.cache.TopTreeCache N)
    (sk_seed pk_seed r : Array U8 N) (digest : Slice U8)
    (hdig : digest.length = p.m.val)
    (hc : CacheValid c (Shake.params (toSlhParams p)) (bytes sk_seed.val) (bytes pk_seed.val)) :
    (do
      let tree_d2 ← CacheopsRust.cache.TopTreeCache.layer_d2_tree_index N p digest
      let d2_hit ← CacheopsRust.cache.TopTreeCache.lookup_d2 c tree_d2
      @cache.shake_ops.sign_from_digest scalar N p sk_seed pk_seed r digest
        (alloc.vec.Vec.deref c.top_tree) d2_hit) ⦃ sig =>
      let P := Shake.params (toSlhParams p)
      let md := (bytes digest.val).take P.mdBytes
      let idxTree := Spec.digestTree P (bytes digest.val)
      let idxLeaf := Spec.digestLeaf P (bytes digest.val)
      let adrs := { { Spec.Adrs.zero with tree := idxTree }.setTypeAndClear
        Spec.FORS_TREE with keypair := idxLeaf }
      let sigFors := Spec.forsSign P md (bytes sk_seed.val) (bytes pk_seed.val) adrs
      let pkFors := Spec.forsPkFromSig P sigFors md (bytes pk_seed.val) adrs
      bytes sig.val = bytes r.val ++ sigFors ++
        Spec.htSign P pkFors (bytes sk_seed.val) (bytes pk_seed.val) idxTree idxLeaf ⦄ :=
  @sign_from_digest_with_cache_dispatch_spec scalar N _ p hp c sk_seed pk_seed r digest hdig hc

end
end CacheopsRust.Closed


namespace CacheopsRust.Closed.Audit
open Lean Elab Command

/-- Follow the executable definitions in the two cache namespaces. In particular,
proofs about a modeled leaf do not make that leaf part of the signer's call graph. -/
private partial def visit (env : Environment) (symbol : Name) : StateM NameSet Unit := do
  if (← get).contains symbol then return
  modify (·.insert symbol)
  if let some decl := env.find? symbol then
    if let some body := decl.value? then
      for dependency in body.getUsedConstants do
        if [`CacheopsRust, `slhdsa.CacheScalar].any (·.isPrefixOf dependency) then
          visit env dependency

run_cmd do
  let (_, used) := (visit (← getEnv) `CacheopsRust.Closed.cache.shake_ops.sign_from_digest).run {}
  for required in [`CacheopsRust.Closed.cache.shake_ops.sign_from_digest_loop,
      `CacheopsRust.Closed.cache.shake_ops.xmss_sign, `CacheopsRust.Closed.cache.shake_ops.xmss_pk_from_sig,
      `CacheopsRust.ShakeNode.node, `CacheopsRust.cache.shake_ops.climb_loop.body,
      `slhdsa.CacheScalar.cache.shake_ops.wots_pk_gen_portable, `slhdsa.CacheScalar.cache.shake_ops.wots_sign,
      `slhdsa.CacheScalar.cache.shake_ops.wots_pk_from_sig, `slhdsa.CacheScalar.cache.shake_ops.fors_sign,
      `slhdsa.CacheScalar.cache.shake_ops.fors_pk_from_sig] do
    unless used.contains required do throwError "scalar signer does not reach {required}"
  for modeled in [`CacheopsRust.cache.shake_ops.xmss_node, `CacheopsRust.cache.shake_ops.xmss_sign,
      `CacheopsRust.cache.shake_ops.xmss_pk_from_sig, `CacheopsRust.cache.shake_ops.wots_sign,
      `CacheopsRust.cache.shake_ops.wots_pk_from_sig, `CacheopsRust.cache.shake_ops.fors_sign,
      `CacheopsRust.cache.shake_ops.fors_pk_from_sig] do
    if used.contains modeled then throwError "scalar signer still calls the assembly model {modeled}"

end CacheopsRust.Closed.Audit
