import Cachepath.PublicMutProgram

open Aeneas Aeneas.Std Result slhdsa slhdsa.cache slhdsa.cache.endtoend
namespace CacheopsRust.Public
set_option linter.concreteInstances false
variable [backend : Closed.Backend]

private def finish {N : Usize} (p : CacheopsRust.params.Params)
    (c : CacheopsRust.cache.TopTreeCache N) (k seed r : Array U8 N)
    (digest : Slice U8) (hit : Option (Slice (Array U8 N))) :=
  match c.family with
  | .Sha2 => do let sig ← CacheopsRust.cache.sha2_ops.sign_from_digest p k seed r digest c.top_tree.deref hit
                ok (some sig,c)
  | .Shake => do let sig ← Closed.cache.shake_ops.sign_from_digest p k seed r digest c.top_tree.deref hit
                 ok (some sig,c)

private theorem finish_eq {N : Usize} (p : CacheopsRust.params.Params)
    (c : CacheopsRust.cache.TopTreeCache N) (k seed r : Array U8 N)
    (digest : Slice U8) (hit : Option (Slice (Array U8 N))) :
    finish p c k seed r digest hit =
      (do let sig ← signFor c.family p k seed r digest c.top_tree.deref hit
          ok (some sig,c)) := by cases h : c.family <;> simp [finish,h,signFor] <;> rfl

private theorem messageFlow {N : Usize} [Builders N] (p : CacheopsRust.params.Params)
    (c : CacheopsRust.cache.TopTreeCache N) (m ctx sk : Slice U8) (rnd : Array U8 N)
    (hc : ¬ctx.len > 255#usize) (compat : cache.TopTreeCache.assert_compatible c p sk = ok ()) :
    cache.sign_cached_mut p m ctx sk rnd c =
    (do let k ← slhdsa.util.block N sk 0#usize
        let prf ← slhdsa.util.block N sk 1#usize
        let seed ← slhdsa.util.block N sk 2#usize
        let root ← slhdsa.util.block N sk 3#usize
        let (r,digest) ← digestFor c.family p prf seed root rnd ctx m
        let idx ← CacheopsRust.cache.TopTreeCache.layer_d2_tree_index N p digest.deref
        let (o,c') ← cache.TopTreeCache.lookup_or_populate_d2 c p k seed idx
        let hit ← if core.option.Option.is_some o then CacheopsRust.cache.TopTreeCache.lookup_d2 c' idx else ok none
        finish p c' k seed r digest.deref hit) := by
  cases c with
  | mk f h d s t l cap =>
    cases f <;> simp only [cache.sign_cached_mut,cache.TopTreeCache.sign_mut,hc,ite_false,compat,
      bind_tc_eq,Std.bind_assoc,bind_ok,digestFor,finish]
    all_goals rfl

/-- The builder obligation needed at each reachable miss. -/
def BuildersCorrect {N : Usize} [b : Builders N] (p : CacheopsRust.params.Params)
    (family : CacheopsRust.cache.HashFamily) :=
  ∀ (sk seed : Array U8 N) (idx : U64),
    CacheopsRust.cache.mutation.Builds (match family with | .Sha2 => b.sha2 | .Shake => b.shake)
      p (familyParams p family) sk seed idx

/-- Postcondition for repeated calls, including the updated cache used by the next call. -/
def MutPost {N : Usize} (p : CacheopsRust.params.Params) (c : CacheopsRust.cache.TopTreeCache N)
    (m ctx sk : Slice U8) (rnd : Spec.Bytes)
    (out : Option (alloc.vec.Vec U8) × CacheopsRust.cache.TopTreeCache N) : Prop :=
  let P := familyParams p c.family
  out.1.map (fun v => bytes v.val) = Spec.slhSign P (bytes m.val) (bytes ctx.val) (bytes sk.val) rnd ∧
  out.2.family = c.family ∧ out.2.layer_d2_capacity = c.layer_d2_capacity ∧
  CacheValid out.2 P (Spec.block P (bytes sk.val) 0) (Spec.block P (bytes sk.val) 2)

theorem sign_cached_mut_spec {N : Usize} [Closed.DispatchCorrect backend N] [b : Builders N]
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (c : CacheopsRust.cache.TopTreeCache N) (m ctx sk : Slice U8) (rnd : Array U8 N)
    (build : BuildersCorrect (N:=N) p c.family)
    (hs : sk.length = 4*N.val) (room : c.family = .Sha2 → Room m.length (msgSlack N.val + 257))
    (hk : Spec.KeyOk (familyParams p c.family) (bytes sk.val))
    (hc : CacheValid c (familyParams p c.family)
      (Spec.block (familyParams p c.family) (bytes sk.val) 0)
      (Spec.block (familyParams p c.family) (bytes sk.val) 2)) :
    cache.sign_cached_mut p m ctx sk rnd c ⦃ out => MutPost p c m ctx sk (bytes rnd.val) out ⦄ := by
  by_cases long : ctx.len > 255#usize
  · have bad : ctx.val.length > 255 := by scalar_tac
    simp [cache.sign_cached_mut,cache.TopTreeCache.sign_mut,long,MutPost,Spec.slhSign,bad,hc]
  have good : ctx.length ≤ 255 := by scalar_tac
  have good' : ¬(bytes ctx.val).length > 255 := by simp [bytes]; scalar_tac
  rw [messageFlow p c m ctx sk rnd long (compatible p hp c sk hs hk hc)]
  let* ⟨k,hk0⟩ ← block_spec
  let* ⟨prf,hk1⟩ ← block_spec
  let* ⟨seed,hk2⟩ ← block_spec
  let* ⟨root,hk3⟩ ← block_spec
  have blk (v : Array U8 N) (i : Nat) (hv : v.val = (sk.val.drop (i*N.val)).take N.val) :
      bytes v.val = Spec.block (familyParams p c.family) (bytes sk.val) i := by
    cases c.family <;> exact bytes_block_N _ hp _ _ _ hv
  have b0 := blk k 0 hk0
  have b1 := blk prf 1 hk1
  have b2 := blk seed 2 hk2
  have b3 := blk root 3 hk3
  have valid : CacheValid c (familyParams p c.family) (bytes k.val) (bytes seed.val) := by rwa [b0,b2]
  have dig : digestFor c.family p prf seed root rnd ctx m ⦃ rd =>
      DigestOk (familyParams p c.family) prf seed root rnd ctx m rd ⦄ := by
    cases hf : c.family
    · exact sha2_digest_spec p hp _ _ _ _ _ _ good (room hf)
    · exact shake_digest_spec p hp _ _ _ _ _ _ good
  obtain ⟨⟨r,digest⟩, erd, hr,hv,hl⟩ := spec_imp_exists dig
  rw [erd,bind_ok]
  have len : digest.deref.length = p.m.val := by
    rw [vec_deref_length]; cases hf : c.family <;> simp only [hf,familyParams] at hl <;> exact hl
  let* ⟨idx,hi⟩ ← layer_d2_tree_index_spec N p digest.deref hp.valid len
  have hd : p.d.val = (familyParams p c.family).d := by cases c.family <;> rfl
  have shift : p.hp.val < Usize.numBits := by
    have h : p.hp.val ≤ 9 := hp.valid.hp_le
    rcases System.Platform.numBits_eq with w | w <;> simp [Usize.numBits,w] <;> omega
  have post := CacheopsRust.cache.mutation.lookup_or_populate_safe b.sha2 b.shake c p
    (familyParams p c.family) k seed idx valid hd shift
    (fun h => by simpa only [h] using build k seed idx)
    (fun h => by simpa only [h] using build k seed idx)
  obtain ⟨⟨o,c'⟩,update,hvalid,hfamily,hcap,hmiss,hhit⟩ := spec_imp_exists post
  change cache.TopTreeCache.lookup_or_populate_d2 c p k seed idx = ok (o,c') at update
  rw [update,bind_ok]
  have current : CacheValid c' (familyParams p c'.family) (bytes k.val) (bytes seed.val) := hfamily ▸ hvalid
  have selected : (if core.option.Option.is_some o then CacheopsRust.cache.TopTreeCache.lookup_d2 c' idx else ok none)
      ⦃ hit => optionalLayer p c' k seed digest.deref hit ⦄ := by
    split
    · let* ⟨hit,hh⟩ ← lookup_d2_spec current idx
      intro tree eq
      rw [eq] at hh
      cases hf : c'.family <;> simp only [hf,familyParams,hi] at hh ⊢ <;> exact hh
    · simp [WP.spec_ok,optionalLayer]
  obtain ⟨hit,hselect,layer⟩ := spec_imp_exists selected
  simp only [uncurry, core.option.Option.is_some] at hselect ⊢
  rw [hselect,bind_ok]
  rw [finish_eq]
  have final := signFor_spec p hp c' m ctx sk rnd k prf seed root r digest hit good' current layer len
    (hfamily ▸ b0) (hfamily ▸ b1) (hfamily ▸ b2) (hfamily ▸ b3) (hfamily ▸ hr) (hfamily ▸ hv)
  let* ⟨sig,hsig⟩ ← final
  exact ⟨hfamily ▸ hsig, hfamily, hcap, b0 ▸ b2 ▸ hvalid⟩

theorem sign_deterministic_cached_mut_spec {N : Usize} [Closed.DispatchCorrect backend N] [Builders N]
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (c : CacheopsRust.cache.TopTreeCache N) (m ctx sk : Slice U8) (build : BuildersCorrect (N:=N) p c.family)
    (hs : sk.length = 4*N.val) (room : c.family = .Sha2 → Room m.length (msgSlack N.val + 257))
    (hk : Spec.KeyOk (familyParams p c.family) (bytes sk.val))
    (hc : CacheValid c (familyParams p c.family)
      (Spec.block (familyParams p c.family) (bytes sk.val) 0)
      (Spec.block (familyParams p c.family) (bytes sk.val) 2)) :
    cache.sign_deterministic_cached_mut p m ctx sk c ⦃ out => MutPost p c m ctx sk
      (Spec.block (familyParams p c.family) (bytes sk.val) 2) out ⦄ := by
  unfold cache.sign_deterministic_cached_mut cache.TopTreeCache.sign_deterministic_mut
  by_cases long : ctx.len > 255#usize
  · have bad : ctx.val.length > 255 := by scalar_tac
    simp [long,MutPost,Spec.slhSign,bad,hc]
  simp only [long,ite_false]
  have get : CacheopsRust.util.block N sk 2#usize = slhdsa.util.block N sk 2#usize := rfl
  rw [get]
  let* ⟨seed,hseed⟩ ← block_spec
  have hb : bytes seed.val = Spec.block (familyParams p c.family) (bytes sk.val) 2 := by
    cases c.family <;> exact bytes_block_N _ hp _ _ _ hseed
  exact hb ▸ sign_cached_mut_spec p hp c m ctx sk seed build hs room hk hc

end CacheopsRust.Public
