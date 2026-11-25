import Cachepath.ShakeClosedProgram
import Cachepath.ShakeEndToEnd

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.Closed

set_option linter.concreteInstances false
variable [backend : Backend]

private theorem wots_eq {N : Usize} [correct : DispatchCorrect backend N] (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (m sk seed : Array U8 N) (a : CacheopsRust.address.Adrs) :
    cache.shake_ops.wots_sign m sk seed a = CacheopsRust.cache.shake_ops.wots_sign m sk seed a := by
  obtain ⟨flag, det⟩ := correct.available
  cases flag with
  | false => exact CacheScalar.wots_sign_eq _ hp det _ _ _ _
  | true =>
    simpa only [cache.shake_ops.wots_sign, CacheScalar.cache.shake_ops.wots_sign,
      CacheScalar.cache.shake_ops.simd.available, det, bind_ok, ite_true] using
      (correct.fast det).wotsSign m sk seed (toSlhAdrs a)

private theorem node_eq {N : Usize} [correct : DispatchCorrect backend N] (hn : N.val ≤ 32) (sk : Array U8 N) (i z : U32)
    (seed : Array U8 N) (a : CacheopsRust.address.Adrs) :
    cache.shake_ops.xmss_node sk i z seed a = CacheopsRust.cache.shake_ops.xmss_node sk i z seed a := by
  obtain ⟨flag, det⟩ := correct.available
  cases flag with
  | false => exact ShakeNode.scalar_node_eq _ _ hn det _ _ _ _ _
  | true =>
    exact ShakeNode.node_eq _ _ _ true det (correct.fast det).subtree
      (fun sk seed a => CacheScalar.wots_pk_gen_eq hn sk seed (toSlhAdrs a)) _ _ _ _ _

private theorem xmss_sign_eq {N : Usize} [correct : DispatchCorrect backend N] (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (m sk : Array U8 N) (idx : U32) (seed : Array U8 N) (a : CacheopsRust.address.Adrs) :
    cache.shake_ops.xmss_sign p m sk idx seed a = CacheopsRust.cache.shake_ops.xmss_sign p m sk idx seed a := by
  unfold cache.shake_ops.xmss_sign CacheopsRust.cache.shake_ops.xmss_sign
  simp only [wots_eq p hp, cache.shake_ops.xmss_sign_loop, CacheopsRust.cache.shake_ops.xmss_sign_loop,
    cache.shake_ops.xmss_sign_loop.body, CacheopsRust.cache.shake_ops.xmss_sign_loop.body, node_eq hp.le32]
  rfl

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

private theorem hypertree_eq {N : Usize} [correct : DispatchCorrect backend N] (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (a : CacheopsRust.address.Adrs) (it : core.ops.range.Range U32) (sk seed : Array U8 N)
    (top : Slice (Array U8 N)) (hit : Option (Slice (Array U8 N))) (root : Array U8 N)
    (sig : alloc.vec.Vec U8) (tree : U64) (leaf : U32) :
    cache.shake_ops.sign_from_digest_loop a it p.n p.h p.d p.hp p.a p.k p.m sk seed top hit root sig tree leaf =
      CacheopsRust.cache.shake_ops.sign_from_digest_loop a it p.n p.h p.d p.hp p.a p.k p.m sk seed top hit root sig tree leaf := by
  cases p
  simp only [cache.shake_ops.sign_from_digest_loop, CacheopsRust.cache.shake_ops.sign_from_digest_loop,
    cache.shake_ops.sign_from_digest_loop.body, CacheopsRust.cache.shake_ops.sign_from_digest_loop.body,
    wots_eq _ hp, xmss_sign_eq _ hp, xmss_recover_eq]
  rfl

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
  have recover (s : Slice U8) (a : CacheopsRust.address.Adrs) : cache.shake_ops.fors_pk_from_sig p s md seed a =
      CacheopsRust.cache.shake_ops.fors_pk_from_sig p s md seed a := by
    obtain ⟨flag, det⟩ := correct.available
    cases flag with
    | false => exact CacheScalar.fors_recover_eq det _ _ _ _ _
    | true =>
      simpa only [cache.shake_ops.fors_pk_from_sig, CacheScalar.cache.shake_ops.fors_pk_from_sig, lift,
        CacheScalar.cache.shake_ops.simd.available, det, bind_ok, ite_true] using
        (correct.fast det).forsRecover (toSlhParams p) s md seed (toSlhAdrs a) hp hl
  simp only [cache.shake_ops.sign_from_digest, CacheopsRust.cache.shake_ops.sign_from_digest,
    len, slice, bind_ok, sign, recover, hypertree_eq p hp]

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
