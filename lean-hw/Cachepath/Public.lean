import Cachepath.PublicDigest

open Aeneas Aeneas.Std Result slhdsa slhdsa.cache slhdsa.cache.endtoend
namespace CacheopsRust.Public

/-- The FIPS hash family selected when creating the cache. -/
def familyParams (p : CacheopsRust.params.Params) : CacheopsRust.cache.HashFamily → Spec.Params
  | .Sha2 => paramsS (toSlhParams p)
  | .Shake => Shake.params (toSlhParams p)

theorem compatible {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (c : CacheopsRust.cache.TopTreeCache N) (sk : Slice U8) (hs : sk.length = 4*N.val)
    (hk : Spec.KeyOk (familyParams p c.family) (bytes sk.val))
    (hc : CacheValid c (familyParams p c.family)
      (Spec.block (familyParams p c.family) (bytes sk.val) 0)
      (Spec.block (familyParams p c.family) (bytes sk.val) 2)) :
    cache.TopTreeCache.assert_compatible c p sk = ok () := by
  have hn : (familyParams p c.family).n = N.val := by cases c.family <;> exact hp.n
  have hhp : c.hp = p.hp := UScalar.eq_of_val_eq (by
    have := hc.hp_eq; cases h : c.family <;> simpa [h,familyParams,Shake.params,paramsS,toSlhParams] using this)
  have hd : c.d = p.d := UScalar.eq_of_val_eq (by
    have := hc.d_eq; cases h : c.family <;> simpa [h,familyParams,Shake.params,paramsS,toSlhParams] using this)
  have bound : 4*N.val ≤ Usize.max := by have := hp.le32; scalar_tac
  have heq : N = p.n := hp.n_eq.symm
  simp [cache.TopTreeCache.assert_compatible,heq,hhp,hd,
    (matches_key_valid_key c _ sk hn bound hs hk hc).2, bind_ok, massert]

def optionalLayer {N : Usize} (p : CacheopsRust.params.Params) (c : CacheopsRust.cache.TopTreeCache N)
    (sk seed : Array U8 N) (digest : Slice U8) (hit : Option (Slice (Array U8 N))) : Prop :=
  ∀ tree, hit = some tree → tree.length = treeSize p.hp.val ∧
    Built tree (familyParams p c.family) (bytes sk.val) (bytes seed.val)
      (layerAdrs (p.d.val - 2) (Spec.digestTree (familyParams p c.family) (bytes digest.val) >>>
        ((p.d.val - 2) * p.hp.val)))

private theorem layer_lookup {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (c : CacheopsRust.cache.TopTreeCache N) (sk seed : Array U8 N) (digest : Slice U8)
    (hl : digest.length = p.m.val)
    (hc : CacheValid c (familyParams p c.family) (bytes sk.val) (bytes seed.val)) :
    cache.TopTreeCache.lookup_digest_layer c p digest ⦃ hit => optionalLayer p c sk seed digest hit ⦄ := by
  unfold cache.TopTreeCache.lookup_digest_layer
  simp only [alloc.vec.Vec.is_empty, bind_tc_eq, bind_ok]
  split
  · simp [WP.spec_ok,optionalLayer]
  · let* ⟨idx,hi⟩ ← layer_d2_tree_index_spec N p digest hp.valid hl
    let* ⟨hit,hh⟩ ← lookup_d2_spec hc idx
    intro tree eq
    rw [eq] at hh
    cases hf : c.family <;> simp only [hf,familyParams,hi] at hh ⊢ <;> exact hh

def digestFor {N : Usize} (f : CacheopsRust.cache.HashFamily) :=
  match f with
  | .Sha2 => @cache.sha2_ops.pure_digest N
  | .Shake => @cache.shake_ops.pure_digest N

variable [backend : Closed.Backend]

def signFor {N : Usize} (f : CacheopsRust.cache.HashFamily) :=
  match f with
  | .Sha2 => @CacheopsRust.cache.sha2_ops.sign_from_digest N
  | .Shake => @Closed.cache.shake_ops.sign_from_digest backend N

private theorem messageFlow {N : Usize} (p : CacheopsRust.params.Params)
    (c : CacheopsRust.cache.TopTreeCache N) (m ctx sk : Slice U8) (rnd : Array U8 N)
    (hc : ¬ctx.len > 255#usize) (compat : cache.TopTreeCache.assert_compatible c p sk = ok ()) :
    cache.sign_cached p m ctx sk rnd c =
    (do let skSeed ← slhdsa.util.block N sk 0#usize
        let skPrf ← slhdsa.util.block N sk 1#usize
        let pkSeed ← slhdsa.util.block N sk 2#usize
        let pkRoot ← slhdsa.util.block N sk 3#usize
        let (r,digest) ← digestFor c.family p skPrf pkSeed pkRoot rnd ctx m
        let hit ← cache.TopTreeCache.lookup_digest_layer c p digest.deref
        let sig ← signFor c.family p skSeed pkSeed r digest.deref c.top_tree.deref hit
        ok (some sig)) := by
  cases c with
  | mk f h d s t l cap =>
    cases f <;> simp only [cache.sign_cached,cache.TopTreeCache.sign,hc,ite_false,compat,
      bind_tc_eq,Std.bind_assoc,bind_ok,digestFor,signFor]
    all_goals rfl

theorem signFor_spec {N : Usize} [Closed.DispatchCorrect backend N]
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (c : CacheopsRust.cache.TopTreeCache N) (m ctx sk : Slice U8)
    (rnd k prf seed root r : Array U8 N) (digest : alloc.vec.Vec U8) (hit : Option (Slice (Array U8 N)))
    (good' : ¬(bytes ctx.val).length > 255)
    (valid : CacheValid c (familyParams p c.family) (bytes k.val) (bytes seed.val))
    (hlayer : optionalLayer p c k seed digest.deref hit) (len : digest.deref.length = p.m.val)
    (b0 : bytes k.val = Spec.block (familyParams p c.family) (bytes sk.val) 0)
    (b1 : bytes prf.val = Spec.block (familyParams p c.family) (bytes sk.val) 1)
    (b2 : bytes seed.val = Spec.block (familyParams p c.family) (bytes sk.val) 2)
    (b3 : bytes root.val = Spec.block (familyParams p c.family) (bytes sk.val) 3)
    (hr : bytes r.val = Spec.PRFmsg (familyParams p c.family) (bytes prf.val) (bytes rnd.val)
        (Spec.withContext (bytes m.val) (bytes ctx.val)))
    (hv : bytes digest.val = Spec.Hmsg (familyParams p c.family) (bytes r.val) (bytes seed.val)
        (bytes root.val) (Spec.withContext (bytes m.val) (bytes ctx.val))) :
    signFor c.family p k seed r digest.deref c.top_tree.deref hit ⦃ sig =>
      some (bytes sig.val) = Spec.slhSign (familyParams p c.family) (bytes m.val)
        (bytes ctx.val) (bytes sk.val) (bytes rnd.val) ⦄ := by
  have htop := valid.top_built
  have hlen := valid.top_len
  unfold optionalLayer at hlayer
  cases hf : c.family
  all_goals simp only [hf,familyParams] at htop hlen hlayer hr hv b0 b1 b2 b3
  · apply WP.spec_mono (sign_from_digest_spec p hp k seed r digest.deref _ hit len
      (by rwa [vec_deref_length]) htop hlayer)
    intro s h
    simp only [Spec.slhSign,good',ite_false,Option.some.injEq,Spec.slhSignInternal]
    simpa only [familyParams,b0,b1,b2,b3,hr,vec_deref_val,hv] using h
  · simp only [signFor]
    rw [Closed.sign_from_digest_eq p hp _ _ _ _ len]
    apply WP.spec_mono (slhdsa.cache.endtoend.shake.sign_from_digest_spec p hp k seed r digest.deref _ hit len
      (by rwa [vec_deref_length]) htop hlayer)
    intro s h
    simp only [Spec.slhSign,good',ite_false,Option.some.injEq,Spec.slhSignInternal]
    simpa only [familyParams,b0,b1,b2,b3,hr,vec_deref_val,hv] using h

/-- Pure signing from the caller's message, context, randomness, key and cache. -/
theorem sign_cached_spec {N : Usize} [Closed.DispatchCorrect backend N] (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (c : CacheopsRust.cache.TopTreeCache N) (m ctx sk : Slice U8) (rnd : Array U8 N)
    (hs : sk.length = 4*N.val) (room : c.family = .Sha2 → Room m.length (msgSlack N.val + 257))
    (hk : Spec.KeyOk (familyParams p c.family) (bytes sk.val))
    (hc : CacheValid c (familyParams p c.family)
      (Spec.block (familyParams p c.family) (bytes sk.val) 0)
      (Spec.block (familyParams p c.family) (bytes sk.val) 2)) :
    cache.sign_cached p m ctx sk rnd c ⦃ sig => sig.map (fun v => bytes v.val) =
      Spec.slhSign (familyParams p c.family) (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes rnd.val) ⦄ := by
  by_cases long : ctx.len > 255#usize
  · have bad : (bytes ctx.val).length > 255 := by simp [bytes]; scalar_tac
    simp [cache.sign_cached,cache.TopTreeCache.sign,long,Spec.slhSign,bad] <;> scalar_tac
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
  let* ⟨hit,hlayer⟩ ← layer_lookup p hp c k seed digest.deref len valid
  have sig := signFor_spec p hp c m ctx sk rnd k prf seed root r digest hit good'
    valid hlayer len b0 b1 b2 b3 hr hv
  let* ⟨out,hout⟩ ← sig
  exact hout

/-- Deterministic mode runs the same public signer with PK.seed as its randomizer. -/
theorem sign_deterministic_cached_spec {N : Usize} [Closed.DispatchCorrect backend N]
    (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (c : CacheopsRust.cache.TopTreeCache N) (m ctx sk : Slice U8)
    (hs : sk.length = 4*N.val) (room : c.family = .Sha2 → Room m.length (msgSlack N.val + 257))
    (hk : Spec.KeyOk (familyParams p c.family) (bytes sk.val))
    (hc : CacheValid c (familyParams p c.family)
      (Spec.block (familyParams p c.family) (bytes sk.val) 0)
      (Spec.block (familyParams p c.family) (bytes sk.val) 2)) :
    cache.sign_deterministic_cached p m ctx sk c ⦃ sig => sig.map (fun v => bytes v.val) =
      Spec.slhSign (familyParams p c.family) (bytes m.val) (bytes ctx.val) (bytes sk.val)
        (Spec.block (familyParams p c.family) (bytes sk.val) 2) ⦄ := by
  unfold cache.sign_deterministic_cached cache.TopTreeCache.sign_deterministic
  by_cases long : ctx.len > 255#usize
  · simp [long,Spec.slhSign] <;> scalar_tac
  simp only [long,ite_false]
  have get : CacheopsRust.util.block N sk 2#usize = slhdsa.util.block N sk 2#usize := rfl
  rw [get]
  let* ⟨seed,hseed⟩ ← block_spec
  have hb : bytes seed.val = Spec.block (familyParams p c.family) (bytes sk.val) 2 := by
    cases c.family <;> exact bytes_block_N _ hp _ _ _ hseed
  exact hb ▸ sign_cached_spec p hp c m ctx sk seed hs room hk hc

end CacheopsRust.Public
