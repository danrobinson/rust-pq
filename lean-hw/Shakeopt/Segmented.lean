import Shakeopt.Seg.Funs
import Slhdsa.Proofs.ShakeSlh

open Aeneas Aeneas.Std Result

namespace Shakeopt.Segmented

open slhdsa
open slhdsa.Shake

/-- Pure Keccak sponge absorption concatenation homomorphism: feeding `a` then `b`
    is identical to feeding `a ++ b`. -/
theorem keccak_feed_append (s : Spec.Keccak.State × Nat) (a b : Spec.Bytes) :
    (a ++ b).foldl Spec.Keccak.feed s = b.foldl Spec.Keccak.feed (a.foldl Spec.Keccak.feed s) :=
  List.foldl_append

/-- Sequential `Sponge::absorb` satisfies the concatenation homomorphism: absorbing
    `a` then `b` into a sponge holding `x` produces a sponge holding `x ++ a ++ b`. -/
theorem sponge_absorb_append (s : slhdsa.shake256.Sponge) (x : Spec.Bytes)
    (hs : Absorbed s x) (a b : Slice U8) :
    (do let s1 ← slhdsa.shake256.Sponge.absorb s a
        slhdsa.shake256.Sponge.absorb s1 b)
      ⦃ out => Absorbed out (x ++ (bytes a.val ++ bytes b.val)) ⦄ := by
  let* ⟨ s1, hs1 ⟩ ← append_spec s x hs a
  simpa only [List.append_assoc] using append_spec s1 (x ++ bytes a.val) hs1 b

/-- Two-byte domain separator `[0, ctx.len() as u8]` concatenated with `ctx` and `msg`
    equals FIPS 205 `M' = toByte(0, 1) ‖ toByte(|ctx|, 1) ‖ ctx ‖ msg`. -/
private theorem withContext_eq_segments (ctx msg : Slice U8) (hc : ctx.length ≤ 255) :
    bytes [0#u8, UScalar.cast .U8 ctx.len] ++ bytes ctx.val ++ bytes msg.val =
      Spec.withContext (bytes msg.val) (bytes ctx.val) := by
  have hcast : (UScalar.cast .U8 ctx.len).val = ctx.length := by
    rw [UScalar.cast_val_eq]
    have hlen : ctx.len.val = ctx.length := rfl
    rw [hlen]
    exact Nat.mod_eq_of_lt (by change ctx.length < 256; omega)
  have hbyte : (UScalar.cast .U8 ctx.len).bv = BitVec.ofNat 8 (bytes ctx.val).length := by
    apply BitVec.eq_of_toNat_eq
    have hlen : ctx.val.length ≤ 255 := hc
    simp only [UScalar.bv_toNat, hcast, bytes, List.length_map, Slice.length]
    change ctx.val.length = ctx.val.length % 256
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simp only [Spec.withContext, Spec.toByte, bytes, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, hbyte]
  rfl

private theorem digest_seg_spec (N : Usize) (s : slhdsa.shake256.Sponge) (x : Spec.Bytes)
    (hs : Absorbed s x) :
    ShakeoptSeg.shake.hash.digest N s ⦃ out => bytes out.val = Spec.shake256 x N.val ⦄ := by
  exact digest_spec N s x hs

/-- Extracted `shake::hash::prf_msg_ctx` computes `SHAKE256(sk_prf ‖ opt_rand ‖ M', N)`
    without allocating `M'`. -/
@[step] theorem prf_msg_ctx_spec {N : Usize} (sk_prf opt_rand : Array U8 N)
    (ctx msg : Slice U8) (hc : ctx.length ≤ 255) :
    ShakeoptSeg.shake.hash.prf_msg_ctx sk_prf opt_rand ctx msg ⦃ out =>
      bytes out.val =
        Spec.shake256
          (bytes sk_prf.val ++ bytes opt_rand.val ++ Spec.withContext (bytes msg.val) (bytes ctx.val))
          N.val ⦄ := by
  unfold ShakeoptSeg.shake.hash.prf_msg_ctx
  simp only [lift, bind_ok]
  let* ⟨ s, hs ⟩ ← empty_spec
  let* ⟨ s1, h1 ⟩ ← append_spec s _ hs
  let* ⟨ s2, h2 ⟩ ← append_spec s1 _ h1
  let* ⟨ s3, h3 ⟩ ← append_spec s2 _ h2
  let* ⟨ s4, h4 ⟩ ← append_spec s3 _ h3
  let* ⟨ s5, h5 ⟩ ← append_spec s4 _ h4
  have hseg : [] ++ bytes sk_prf.to_slice.val ++ bytes opt_rand.to_slice.val ++
      bytes (Array.make 2#usize [0#u8, UScalar.cast .U8 ctx.len]).to_slice.val ++
      bytes ctx.val ++ bytes msg.val =
      bytes sk_prf.val ++ bytes opt_rand.val ++ Spec.withContext (bytes msg.val) (bytes ctx.val) := by
    simp only [List.nil_append, Array.val_to_slice, Array.make_val]
    rw [List.append_assoc, List.append_assoc, ← List.append_assoc (bytes [0#u8, _]),
      withContext_eq_segments ctx msg hc]
  rw [hseg] at h5
  exact digest_seg_spec N s5 _ h5

theorem prf_msg_ctx_params {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (sk_prf opt_rand : Array U8 N) (ctx msg : Slice U8) (hc : ctx.length ≤ 255) :
    ShakeoptSeg.shake.hash.prf_msg_ctx sk_prf opt_rand ctx msg ⦃ r =>
      bytes r.val =
        Spec.PRFmsg (Shake.params p) (bytes sk_prf.val) (bytes opt_rand.val)
          (Spec.withContext (bytes msg.val) (bytes ctx.val)) ⦄ := by
  simpa only [Shake.params, Spec.PRFmsg, paramsS_n, hp.n_eq] using
    prf_msg_ctx_spec sk_prf opt_rand ctx msg hc

/-- Segmented `prf_msg_ctx` agrees identically with contiguous `with_context` + `prf_msg`. -/
theorem prf_msg_ctx_eq_contiguous {N : Usize} (sk_prf opt_rand : Array U8 N)
    (ctx msg : Slice U8) (hc : ctx.length ≤ 255) (hm : msg.length + 257 ≤ Usize.max) :
    (do let a ← ShakeoptSeg.shake.hash.prf_msg_ctx sk_prf opt_rand ctx msg
        let mp ← slhdsa.shake.slh.with_context msg ctx
        let b ← slhdsa.shake.hash.prf_msg sk_prf opt_rand (alloc.vec.Vec.deref mp)
        ok (a, b))
      ⦃ ab => bytes ab.1.val = bytes ab.2.val ⦄ := by
  let* ⟨ a, ha ⟩ ← prf_msg_ctx_spec sk_prf opt_rand ctx msg hc
  let* ⟨ mp, hmp, _ ⟩ ← Shake.with_context_spec msg ctx hc hm
  let* ⟨ b, hb ⟩ ← Shake.prf_msg_spec sk_prf opt_rand (alloc.vec.Vec.deref mp)
  simp only [vec_deref_val] at hb
  rw [ha, hb, hmp]

/-- Extracted `shake::hash::h_msg_ctx` computes `SHAKE256(r ‖ pk_seed ‖ pk_root ‖ M', p.m)`
    without allocating `M'`. -/
@[step] theorem h_msg_ctx_spec {N : Usize} (p : _root_.slhdsa.params.Params)
    (r pk_seed pk_root : Array U8 N) (ctx msg : Slice U8) (hc : ctx.length ≤ 255) :
    ShakeoptSeg.shake.hash.h_msg_ctx p r pk_seed pk_root ctx msg ⦃ out =>
      bytes out.val =
        Spec.shake256
          (bytes r.val ++ bytes pk_seed.val ++ bytes pk_root.val ++
            Spec.withContext (bytes msg.val) (bytes ctx.val))
          p.m.val ⦄ := by
  unfold ShakeoptSeg.shake.hash.h_msg_ctx
  simp only [lift, bind_ok]
  let* ⟨ s, hs ⟩ ← empty_spec
  let* ⟨ s1, h1 ⟩ ← append_spec s _ hs
  let* ⟨ s2, h2 ⟩ ← append_spec s1 _ h1
  let* ⟨ s3, h3 ⟩ ← append_spec s2 _ h2
  let* ⟨ s4, h4 ⟩ ← append_spec s3 _ h3
  let* ⟨ s5, h5 ⟩ ← append_spec s4 _ h4
  let* ⟨ s6, h6 ⟩ ← append_spec s5 _ h5
  step*
  simp only [alloc.vec.Vec.deref_mut]
  let* ⟨ buf, hb ⟩ ← Keccak.finish_spec s6 out.slice h6.2
  change bytes buf.val = _
  change out.slice.length = p.m.val at out_post1
  have hseg : [] ++ bytes r.to_slice.val ++ bytes pk_seed.to_slice.val ++
      bytes pk_root.to_slice.val ++
      bytes (Array.make 2#usize [0#u8, UScalar.cast .U8 ctx.len]).to_slice.val ++
      bytes ctx.val ++ bytes msg.val =
      bytes r.val ++ bytes pk_seed.val ++ bytes pk_root.val ++
        Spec.withContext (bytes msg.val) (bytes ctx.val) := by
    simp only [List.nil_append, Array.val_to_slice, Array.make_val]
    rw [List.append_assoc, List.append_assoc, List.append_assoc,
      ← List.append_assoc (bytes [0#u8, _]), withContext_eq_segments ctx msg hc]
    simp only [List.append_assoc]
  rw [hseg] at h6
  simpa only [Spec.shake256, h6.1, out_post1] using hb

theorem h_msg_ctx_params {N : Usize} (p : _root_.slhdsa.params.Params)
    (r pk_seed pk_root : Array U8 N) (ctx msg : Slice U8) (hc : ctx.length ≤ 255) :
    ShakeoptSeg.shake.hash.h_msg_ctx p r pk_seed pk_root ctx msg ⦃ d =>
      bytes d.val =
        Spec.Hmsg (Shake.params p) (bytes r.val) (bytes pk_seed.val) (bytes pk_root.val)
          (Spec.withContext (bytes msg.val) (bytes ctx.val)) ∧
      d.length = p.m.val ⦄ := by
  apply WP.spec_mono (h_msg_ctx_spec p r pk_seed pk_root ctx msg hc)
  intro d hd
  exact ⟨hd, by simpa [alloc.vec.Vec.length] using congrArg List.length hd⟩

/-- Segmented `h_msg_ctx` agrees identically with contiguous `with_context` + `h_msg`. -/
theorem h_msg_ctx_eq_contiguous {N : Usize} (p : _root_.slhdsa.params.Params)
    (r pk_seed pk_root : Array U8 N) (ctx msg : Slice U8)
    (hc : ctx.length ≤ 255) (hm : msg.length + 257 ≤ Usize.max) :
    (do let a ← ShakeoptSeg.shake.hash.h_msg_ctx p r pk_seed pk_root ctx msg
        let mp ← slhdsa.shake.slh.with_context msg ctx
        let b ← slhdsa.shake.hash.h_msg p r pk_seed pk_root (alloc.vec.Vec.deref mp)
        ok (a, b))
      ⦃ ab => bytes ab.1.val = bytes ab.2.val ⦄ := by
  let* ⟨ a, ha ⟩ ← h_msg_ctx_spec p r pk_seed pk_root ctx msg hc
  let* ⟨ mp, hmp, _ ⟩ ← Shake.with_context_spec msg ctx hc hm
  let* ⟨ b, hb ⟩ ← Shake.h_msg_spec p r pk_seed pk_root (alloc.vec.Vec.deref mp)
  simp only [vec_deref_val] at hb
  rw [ha, hb, hmp]

private theorem seg_adrs_new_eq : ShakeoptSeg.address.Adrs.new = slhdsa.address.Adrs.new := rfl
private theorem seg_adrs_with_tree_eq :
    ShakeoptSeg.address.Adrs.with_tree = slhdsa.address.Adrs.with_tree := rfl
private theorem seg_adrs_with_type_eq :
    ShakeoptSeg.address.Adrs.with_type = slhdsa.address.Adrs.with_type := rfl
private theorem seg_adrs_with_keypair_eq :
    ShakeoptSeg.address.Adrs.with_keypair = slhdsa.address.Adrs.with_keypair := rfl
private theorem seg_fors_tree_eq : ShakeoptSeg.address.FORS_TREE = slhdsa.address.FORS_TREE := by
  simp only [global_simps]
private theorem seg_md_bytes_eq :
    ShakeoptSeg.params.Params.md_bytes = slhdsa.params.Params.md_bytes := rfl
private theorem seg_fors_sig_bytes_eq :
    ShakeoptSeg.params.Params.fors_sig_bytes = slhdsa.params.Params.fors_sig_bytes := rfl
private theorem seg_sig_bytes_eq :
    ShakeoptSeg.params.Params.sig_bytes = slhdsa.params.Params.sig_bytes := by
  funext p
  simp only [ShakeoptSeg.params.Params.sig_bytes, slhdsa.params.Params.sig_bytes,
    ShakeoptSeg.params.Params.fors_sig_bytes, slhdsa.params.Params.fors_sig_bytes,
    ShakeoptSeg.params.Params.xmss_sig_bytes, slhdsa.params.Params.xmss_sig_bytes,
    ShakeoptSeg.params.Params.len, slhdsa.params.Params.len, global_simps]

private theorem n_shape (p : _root_.slhdsa.params.Params) : (Shake.params p).n = (paramsS p).n := rfl
private theorem mdBytes_shape (p : _root_.slhdsa.params.Params) : (Shake.params p).mdBytes = (paramsS p).mdBytes := rfl
private theorem sigBytes_shape (p : _root_.slhdsa.params.Params) : (Shake.params p).sigBytes = (paramsS p).sigBytes := rfl
private theorem forsSigBytes_shape (p : _root_.slhdsa.params.Params) : (Shake.params p).forsSigBytes = (paramsS p).forsSigBytes := rfl
private theorem xmssSigBytes_shape (p : _root_.slhdsa.params.Params) : (Shake.params p).xmssSigBytes = (paramsS p).xmssSigBytes := rfl
private theorem block_shape (p : _root_.slhdsa.params.Params) : Spec.block (Shake.params p) = Spec.block (paramsS p) := rfl
private theorem digestTree_shape (p : _root_.slhdsa.params.Params) : Spec.digestTree (Shake.params p) = Spec.digestTree (paramsS p) := rfl
private theorem digestLeaf_shape (p : _root_.slhdsa.params.Params) : Spec.digestLeaf (Shake.params p) = Spec.digestLeaf (paramsS p) := rfl

set_option maxHeartbeats 2000000 in
/-- Extracted `shake::slh::shake_sign_ctx` matches FIPS 205 `slh_sign_internal`
    on `M' = withContext(m, ctx)` for arbitrary message length `m`. -/
@[step] theorem shake_sign_ctx_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (addrnd : Array U8 N)
    (hsk : sk.length = 4 * N.val) (hc : ctx.length ≤ 255) :
    ShakeoptSeg.shake.slh.shake_sign_ctx p m ctx sk addrnd ⦃ sig =>
      bytes sig.val =
        Spec.slhSignInternal (Shake.params p)
          (Spec.withContext (bytes m.val) (bytes ctx.val))
          (bytes sk.val) (bytes addrnd.val) ∧
      sig.length = (paramsS p).sigBytes ⦄ := by
  have hv := hp.valid
  have hn := hp.le32
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hp
  have hhl := ht_len_le p hp
  unfold ShakeoptSeg.shake.slh.shake_sign_ctx
  simp only [seg_adrs_new_eq, seg_adrs_with_tree_eq, seg_adrs_with_type_eq,
    seg_adrs_with_keypair_eq, seg_fors_tree_eq, seg_md_bytes_eq,
    ShakeoptSeg.shake.hash.seed_ctx, bind_ok]
  let* ⟨ sk_seed, sk_seed_post ⟩ ← block_spec
  let* ⟨ sk_prf, sk_prf_post ⟩ ← block_spec
  let* ⟨ pk_seed, pk_seed_post ⟩ ← block_spec
  let* ⟨ pk_root, pk_root_post ⟩ ← block_spec
  let* ⟨ r, r_post ⟩ ← prf_msg_ctx_params p hp sk_prf addrnd ctx m hc
  let* ⟨ digest, digest_post, digest_len ⟩ ← h_msg_ctx_params p r pk_seed pk_root ctx m hc
  let* ⟨ idx_tree, idx_tree_post, idx_tree_lt ⟩ ← Shake.digest_tree_spec
  let* ⟨ idx_leaf, idx_leaf_post, idx_leaf_lt ⟩ ← Shake.digest_leaf_spec
  let* ⟨ a, a_post ⟩ ← adrs_new_spec
  let* ⟨ a1, a1_post ⟩ ← with_tree_spec
  let* ⟨ a2, a2_post, a2_post1 ⟩ ← with_type_spec
  let* ⟨ adrs, adrs_post ⟩ ← with_keypair_spec
  let* ⟨ i, i_post, i_post1 ⟩ ← md_bytes_spec
  let* ⟨ md, md_post, md_len ⟩ ← alloc.vec.Vec.index_Range_spec
  let* ⟨ sig_fors, sig_fors_post, sig_fors_len ⟩ ← Shake.fors_sign_spec p hp md sk_seed pk_seed adrs
  let* ⟨ pk_fors, pk_fors_post ⟩ ← Shake.fors_pk_from_sig_spec p hp (alloc.vec.Vec.deref sig_fors) md pk_seed adrs
  let* ⟨ sig_ht, sig_ht_post, sig_ht_len ⟩ ← Shake.ht_sign_spec p hp pk_fors sk_seed pk_seed idx_tree idx_leaf idx_leaf_lt
  let* ⟨ s3, s3_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ sg0, sg0_post ⟩ ← extend_spec
  have hl0 : sg0.length = N.val := by
    simp only [alloc.vec.Vec.length]; rw [sg0_post, s3_post]; simp
  let* ⟨ sg1, sg1_post ⟩ ← extend_spec
  have hl1 : sg1.length = N.val + p.k.val * (1 + p.a.val) * N.val := by
    have : sg1.val.length = sg0.val.length + sig_fors.val.length := by rw [sg1_post]; simp
    simp only [alloc.vec.Vec.length] at hl0 sig_fors_len ⊢; omega
  let* ⟨ sg2, sg2_post ⟩ ← extend_spec
  have hb0 := bytes_block_N p hp sk sk_seed 0 sk_seed_post
  have hb1 := bytes_block_N p hp sk sk_prf 1 sk_prf_post
  have hb2 := bytes_block_N p hp sk pk_seed 2 pk_seed_post
  have hb3 := bytes_block_N p hp sk pk_root 3 pk_root_post
  have hadrs : adrsS adrs = { { Spec.Adrs.zero with tree := idx_tree.val }.setTypeAndClear
      Spec.FORS_TREE with keypair := idx_leaf.val } := by
    simp [adrsS, adrs_post, a2_post1, a1_post, a_post, Spec.Adrs.setTypeAndClear,
      Spec.Adrs.zero, Spec.FORS_TREE, global_simps]
  have hmd : bytes md.val = (bytes digest.val).take (paramsS p).mdBytes := by
    simp [md_post, List.slice, i_post1]
  have hsig : bytes sg2.val = bytes r.val ++ bytes sig_fors.val ++ bytes sig_ht.val := by
    simp [sg2_post, sg1_post, sg0_post, s3_post]
  simp only [vec_deref_val] at *
  constructor
  · simp only [Spec.slhSignInternal, block_shape, digestLeaf_shape, digestTree_shape, mdBytes_shape]
    rw [← hb0, ← hb1, ← hb2, ← hb3, ← r_post, ← digest_post, ← hmd, ← idx_tree_post,
      ← idx_leaf_post, ← hadrs, ← sig_fors_post, ← pk_fors_post, ← sig_ht_post, hsig]
  · rw [sigBytes_eq p hv, forsSigBytes_eq p hp, xmssSigBytes_eq p hp]
    have : sg2.val.length = sg1.val.length + sig_ht.val.length := by rw [sg2_post]; simp
    simp only [alloc.vec.Vec.length] at hl1 sig_ht_len ⊢
    simp only [hp.n_eq]
    omega

set_option maxHeartbeats 2000000 in
/-- Extracted `shake::slh::shake_verify_ctx` matches FIPS 205 `slh_verify_internal`
    on `M' = withContext(m, ctx)` for arbitrary message length `m`. -/
@[step] theorem shake_verify_ctx_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (m ctx sig pk : Slice U8) (hpk : pk.length = 2 * N.val) (hc : ctx.length ≤ 255) :
    ShakeoptSeg.shake.slh.shake_verify_ctx N p m ctx sig pk ⦃ b =>
      b = Spec.slhVerifyInternal (Shake.params p)
        (Spec.withContext (bytes m.val) (bytes ctx.val))
        (bytes sig.val) (bytes pk.val) ⦄ := by
  have hv := hp.valid
  have hn := hp.le32
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hp
  have hhl := ht_len_le p hp
  have hfe := forsSigBytes_eq p hp
  have hxe := xmssSigBytes_eq p hp
  unfold ShakeoptSeg.shake.slh.shake_verify_ctx
  simp only [seg_adrs_new_eq, seg_adrs_with_tree_eq, seg_adrs_with_type_eq,
    seg_adrs_with_keypair_eq, seg_fors_tree_eq, seg_md_bytes_eq,
    seg_fors_sig_bytes_eq, seg_sig_bytes_eq, ShakeoptSeg.shake.hash.seed_ctx, bind_ok]
  let* ⟨ sig_bytes, sig_bytes_post, sig_bytes_post1 ⟩ ← sig_bytes_spec
  split
  · rename_i hlen
    have : sig.val.length ≠ (paramsS p).sigBytes := by
      simp only [bne_iff_ne, ne_eq] at hlen
      intro h; apply hlen; scalar_tac
    simp [Spec.slhVerifyInternal, this, sigBytes_shape]
  · rename_i hlen
    have hlen' : sig.val.length = (paramsS p).sigBytes := by
      simp at hlen; scalar_tac
    have hsb : (paramsS p).sigBytes = N.val + p.k.val * (1 + p.a.val) * N.val +
        p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) := by
      rw [sigBytes_eq p hv, hfe, hxe]; simp [hp.n_eq]
    let* ⟨ i1, i1_post, i1_post1 ⟩ ← fors_sig_bytes_spec
    let* ⟨ fors_end, fors_end_post ⟩ ← Usize.add_spec
    let* ⟨ pk_seed, pk_seed_post ⟩ ← block_spec
    let* ⟨ pk_root, pk_root_post ⟩ ← block_spec
    let* ⟨ r, r_post ⟩ ← block_spec
    let* ⟨ digest, digest_post, digest_len ⟩ ← h_msg_ctx_params p r pk_seed pk_root ctx m hc
    let* ⟨ idx_tree, idx_tree_post, idx_tree_lt ⟩ ← Shake.digest_tree_spec
    let* ⟨ idx_leaf, idx_leaf_post, idx_leaf_lt ⟩ ← Shake.digest_leaf_spec
    let* ⟨ a, a_post ⟩ ← adrs_new_spec
    let* ⟨ a1, a1_post ⟩ ← with_tree_spec
    let* ⟨ a2, a2_post, a2_post1 ⟩ ← with_type_spec
    let* ⟨ adrs, adrs_post ⟩ ← with_keypair_spec
    let* ⟨ s2, s2_post, s2_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    let* ⟨ i2, i2_post, i2_post1 ⟩ ← md_bytes_spec
    let* ⟨ s3, s3_post, s3_len ⟩ ← alloc.vec.Vec.index_Range_spec
    let* ⟨ pk_fors, pk_fors_post ⟩ ← fors_verify_spec p hp s2 s3 pk_seed adrs
      (by rw [s2_len, fors_end_post, i1_post, hp.n_eq]; omega) (by rw [s3_len, i2_post]; omega)
      (by simp [adrs_post,a2_post1])
    let* ⟨ s4, s4_post, s4_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    let* ⟨ b, b_post ⟩ ← Shake.ht_verify_spec p hp pk_fors s4 pk_seed idx_tree idx_leaf pk_root
      (by rw [s4_len, sig_bytes_post1, fors_end_post, i1_post, hfe, hxe]; simp only [hp.n_eq]; omega)
      idx_leaf_lt
    have hb0 := bytes_block_N p hp pk pk_seed 0 pk_seed_post
    have hb1 := bytes_block_N p hp pk pk_root 1 pk_root_post
    have hadrs : adrsS adrs = { { Spec.Adrs.zero with tree := idx_tree.val }.setTypeAndClear
        Spec.FORS_TREE with keypair := idx_leaf.val } := by
      simp [adrsS, adrs_post, a2_post1, a1_post, a_post, Spec.Adrs.setTypeAndClear,
        Spec.Adrs.zero, Spec.FORS_TREE, global_simps]
    have hmd : bytes s3.val = (bytes digest.val).take (paramsS p).mdBytes := by
      simp [s3_post, List.slice, i2_post1]
    have h5 : bytes s2.val =
        ((bytes sig.val).drop (paramsS p).n).take (paramsS p).forsSigBytes := by
      simp [s2_post, List.slice, fors_end_post, i1_post1, hp.n_eq]
    have h9 : bytes s4.val = (bytes sig.val).drop ((paramsS p).n + (paramsS p).forsSigBytes) := by
      rw [s4_post]
      simp only [List.slice]
      rw [List.take_of_length_le (by simp only [List.length_drop, sig_bytes_post1]; omega)]
      simp [fors_end_post, i1_post1, hp.n_eq]
    have hr : bytes r.val = (bytes sig.val).take (paramsS p).n := by
      simp [r_post, hp.n_eq]
    simp only [vec_deref_val] at *
    simp only [Spec.slhVerifyInternal, block_shape, digestLeaf_shape, digestTree_shape,
      mdBytes_shape, sigBytes_shape, forsSigBytes_shape, n_shape]
    rw [← hb0, ← hb1, ← hr, ← digest_post, ← hmd, ← idx_tree_post,
      ← idx_leaf_post, ← hadrs, ← h5, ← pk_fors_post, ← h9, ← b_post]
    simp [hlen']

/-- Extracted `platform-sha2` `shake::slh::slh_sign` (Algorithm 22) matches `Spec.slhSign`
    for ALL messages of arbitrary length, dispatching non-empty messages through zero-copy
    `shake_sign_ctx` and empty messages through `with_context`. -/
theorem slh_sign_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val) :
    ShakeoptSeg.shake.slh.slh_sign p m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign (Shake.params p) (bytes m.val) (bytes ctx.val)
          (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold ShakeoptSeg.shake.slh.slh_sign
  by_cases hc : ctx.len > 255#usize
  · have : ctx.val.length > 255 := by scalar_tac
    simp [hc, Spec.slhSign, this]
  · have hc' : ctx.length ≤ 255 := by scalar_tac
    have hc'' : ¬ ctx.val.length > 255 := by scalar_tac
    simp only [hc, ite_false]
    step as ⟨ empty, hempty ⟩
    cases empty
    · simp only [Bool.false_eq_true, ↓reduceIte]
      let* ⟨ v, v_post, _ ⟩ ← shake_sign_ctx_spec p hp m ctx sk addrnd hsk hc'
      simp [Spec.slhSign, hc'', v_post]
    · simp only [↓reduceIte]
      have hm0 : m.length = 0 := by
        simpa [Slice.length] using hempty
      have hmroom : m.length + 257 ≤ Usize.max := by rw [hm0]; scalar_tac
      let* ⟨ mp, mp_post, _ ⟩ ← Shake.with_context_spec m ctx hc' hmroom
      let* ⟨ v, v_post, _ ⟩ ← Shake.slh_sign_internal_all_lengths p hp (alloc.vec.Vec.deref mp) sk addrnd hsk
      simp [Spec.slhSign, hc'', v_post, mp_post]

/-- Extracted `platform-sha2` `shake::slh::slh_verify` (Algorithm 24) matches `Spec.slhVerify`
    for ALL messages of arbitrary length, dispatching non-empty messages through zero-copy
    `shake_verify_ctx` and empty messages through `with_context`. -/
theorem slh_verify_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (m sig ctx pk : Slice U8) (hpk : pk.length = 2 * N.val) :
    ShakeoptSeg.shake.slh.slh_verify N p m sig ctx pk ⦃ b =>
      b = Spec.slhVerify (Shake.params p) (bytes m.val) (bytes sig.val)
        (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold ShakeoptSeg.shake.slh.slh_verify
  by_cases hc : ctx.len > 255#usize
  · have : ctx.val.length > 255 := by scalar_tac
    simp [hc, Spec.slhVerify, this]
  · have hc' : ctx.length ≤ 255 := by scalar_tac
    have hc'' : ¬ ctx.val.length > 255 := by scalar_tac
    simp only [hc, ite_false]
    step as ⟨ empty, hempty ⟩
    cases empty
    · simp only [Bool.false_eq_true, ↓reduceIte]
      let* ⟨ b, b_post ⟩ ← shake_verify_ctx_spec p hp m ctx sig pk hpk hc'
      simp [Spec.slhVerify, hc'', b_post]
    · simp only [↓reduceIte]
      have hm0 : m.length = 0 := by
        simpa [Slice.length] using hempty
      have hmroom : m.length + 257 ≤ Usize.max := by rw [hm0]; scalar_tac
      let* ⟨ mp, mp_post, _ ⟩ ← Shake.with_context_spec m ctx hc' hmroom
      let* ⟨ b, b_post ⟩ ← Shake.slh_verify_internal_all_lengths p hp (alloc.vec.Vec.deref mp) sig pk hpk
      simp [Spec.slhVerify, hc'', b_post, mp_post]

end Shakeopt.Segmented
