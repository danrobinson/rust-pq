import Slhdsa.Proofs.Slh
import Slhdsa.Proofs.ShakeHt
import Slhdsa.Proofs.ShakeFors
open Aeneas Aeneas.Std Result
namespace slhdsa.Shake

private theorem n_shape (p : _root_.slhdsa.params.Params) : (params p).n = (paramsS p).n := rfl
private theorem mdBytes_shape (p : _root_.slhdsa.params.Params) : (params p).mdBytes = (paramsS p).mdBytes := rfl
private theorem sigBytes_shape (p : _root_.slhdsa.params.Params) : (params p).sigBytes = (paramsS p).sigBytes := rfl
private theorem forsSigBytes_shape (p : _root_.slhdsa.params.Params) : (params p).forsSigBytes = (paramsS p).forsSigBytes := rfl
private theorem xmssSigBytes_shape (p : _root_.slhdsa.params.Params) : (params p).xmssSigBytes = (paramsS p).xmssSigBytes := rfl
private theorem block_shape (p : _root_.slhdsa.params.Params) : Spec.block (params p) = Spec.block (paramsS p) := rfl
private theorem digestTree_shape (p : _root_.slhdsa.params.Params) : Spec.digestTree (params p) = Spec.digestTree (paramsS p) := rfl
private theorem digestLeaf_shape (p : _root_.slhdsa.params.Params) : Spec.digestLeaf (params p) = Spec.digestLeaf (paramsS p) := rfl

theorem prf_msg_params {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (key opt : Array U8 N) (m : Slice U8) :
    shake.hash.prf_msg key opt m ⦃ r => bytes r.val =
      Spec.PRFmsg (params p) (bytes key.val) (bytes opt.val) (bytes m.val) ⦄ := by
  simpa only [params, Spec.PRFmsg, paramsS_n, hp.n_eq] using prf_msg_spec key opt m

theorem h_msg_params {N : Usize} (p : _root_.slhdsa.params.Params) (r pk root : Array U8 N) (m : Slice U8) :
    shake.hash.h_msg p r pk root m ⦃ d => bytes d.val =
      Spec.Hmsg (params p) (bytes r.val) (bytes pk.val) (bytes root.val) (bytes m.val) ∧ d.length = p.m.val ⦄ := by
  apply WP.spec_mono (h_msg_spec p r pk root m)
  intro d hd
  exact ⟨hd, by simpa [alloc.vec.Vec.length] using congrArg List.length hd⟩

@[step] theorem digest_tree_spec (p : _root_.slhdsa.params.Params) (digest : Slice U8) (hv : (paramsS p).Valid)
    (h : digest.length = p.m.val) :
    shake.slh.digest_tree p digest ⦃ r => r.val = Spec.digestTree (paramsS p) (bytes digest.val) ∧
      r.val < 2 ^ (p.h.val - p.hp.val) ⦄  :=
  slhdsa.digest_tree_spec p digest hv h

@[step] theorem digest_leaf_spec (p : _root_.slhdsa.params.Params) (digest : Slice U8) (hv : (paramsS p).Valid)
    (h : digest.length = p.m.val) :
    shake.slh.digest_leaf p digest ⦃ r => r.val = Spec.digestLeaf (paramsS p) (bytes digest.val) ∧
      r.val < 2 ^ p.hp.val ⦄  :=
  slhdsa.digest_leaf_spec p digest hv h

@[step] theorem with_context_spec (m ctx : Slice U8) (hc : ctx.length ≤ 255)
    (hm : m.length + 257 ≤ Usize.max) :
    shake.slh.with_context m ctx ⦃ r => bytes r.val = Spec.withContext (bytes m.val) (bytes ctx.val) ∧
      r.length = 2 + ctx.length + m.length ⦄  :=
  slhdsa.with_context_spec m ctx hc hm

@[step]
theorem slh_keygen_internal_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (sk_seed sk_prf pk_seed : Array U8 N) (sk pk : Slice U8)
    (hsk : sk.length = 4 * N.val) (hpk : pk.length = 2 * N.val) :
    shake.slh.slh_keygen_internal p sk_seed sk_prf pk_seed sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal (params p) (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) ∧
      r.1.length = 4 * N.val ∧ r.2.length = 2 * N.val ⦄ := by
  have hv := hp.valid
  have hn := hp.le32
  have hd := hv.d_ge
  simp only [paramsS_d] at hd
  have hhp := hv.hp_le
  simp only [paramsS_hp] at hhp
  have hpow : (0 + 1) * 2 ^ p.hp.val ≤ 2 ^ 32 := by
    have : 2 ^ p.hp.val ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp
    omega
  unfold shake.slh.slh_keygen_internal
  let* ⟨ a, a_post ⟩ ← adrs_new_spec
  let* ⟨ i, i_post ⟩ ← U32.sub_spec
  let* ⟨ adrs, adrs_post ⟩ ← with_layer_spec
  simp only [shake.hash.seed_ctx, bind_ok]
  let* ⟨ pk_root, pk_root_post ⟩ ← xmss_node_spec p hp sk_seed 0#u32 p.hp pk_seed adrs
    (by simpa using hpow)
  step*
  all_goals try (subst_vars; scalar_tac)
  have hl1 : sk_seed.val.length = N.val := by simp
  have hl2 : sk_prf.val.length = N.val := by simp
  have hl3 : pk_seed.val.length = N.val := by simp
  have hl4 : pk_root.val.length = N.val := by simp
  have hsk4 : (index_mut_back3 s11).val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val := by
    rw [s9_post2, s11_post, s10_post, s6_post2, s8_post, s7_post, s3_post2, s5_post, s4_post,
      s_post2, s2_post, s1_post]
    simp only [Array.val_to_slice]
    have hsk' : sk.val.length = 4 * N.val := hsk
    simp only [Slice.setSlice!_val]
    refine setSlice4 _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
    · rw [hl1]
    · rw [hl1, hl2, i1_post]; ring
    · rw [hl1, hl2, hl3, i2_post]; ring
    · rw [hl1, hl2, hl3, hl4, hsk']; ring
  have hpk2 : (index_mut_back5 s17).val = pk_seed.val ++ pk_root.val := by
    rw [s15_post2, s17_post, s16_post, s12_post2, s14_post, s13_post]
    simp only [Array.val_to_slice]
    have hpk' : pk.val.length = 2 * N.val := hpk
    simp only [Slice.setSlice!_val]
    refine setSlice2 _ _ _ _ ?_ ?_
    · rw [hl3]
    · rw [hl3, hl4, hpk']; ring
  have ha : adrsS adrs = { Spec.Adrs.zero with layer := p.d.val - 1 } := by
    simp [adrsS, adrs_post, a_post, Spec.Adrs.zero, i_post]
  refine ⟨?_, ?_, ?_⟩
  · simp [Spec.slhKeygenInternal, hsk4, hpk2, pk_root_post, ha, show (params p).hp = p.hp.val from rfl, show (params p).d = p.d.val from rfl]
  · simp only [Slice.length, hsk4, List.length_append]; omega
  · simp only [Slice.length, hpk2, List.length_append]; omega

set_option maxHeartbeats 2000000 in
@[step]
theorem slh_sign_internal_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m sk : Slice U8)
    (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val) (hm : Room m.length (msgSlack N.val)) :
    shake.slh.slh_sign_internal p m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal (params p) (bytes m.val) (bytes sk.val)
        (bytes addrnd.val) ∧
      sig.length = (paramsS p).sigBytes ⦄ := by
  have hv := hp.valid
  have hn := hp.le32
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hp
  have hhl := ht_len_le p hp
  unfold shake.slh.slh_sign_internal
  let* ⟨ sk_seed, sk_seed_post ⟩ ← block_spec
  let* ⟨ sk_prf, sk_prf_post ⟩ ← block_spec
  let* ⟨ pk_seed, pk_seed_post ⟩ ← block_spec
  let* ⟨ pk_root, pk_root_post ⟩ ← block_spec
  let* ⟨ r, r_post ⟩ ← prf_msg_params p hp
  let* ⟨ digest, digest_post, digest_len ⟩ ← h_msg_params p
  let* ⟨ idx_tree, idx_tree_post, idx_tree_lt ⟩ ← digest_tree_spec
  let* ⟨ idx_leaf, idx_leaf_post, idx_leaf_lt ⟩ ← digest_leaf_spec
  let* ⟨ a, a_post ⟩ ← adrs_new_spec
  let* ⟨ a1, a1_post ⟩ ← with_tree_spec
  let* ⟨ a2, a2_post, a2_post1 ⟩ ← with_type_spec
  let* ⟨ adrs, adrs_post ⟩ ← with_keypair_spec
  simp only [shake.hash.seed_ctx, bind_ok]
  let* ⟨ i, i_post, i_post1 ⟩ ← md_bytes_spec
  let* ⟨ md, md_post, md_len ⟩ ← alloc.vec.Vec.index_Range_spec
  let* ⟨ sig_fors, sig_fors_post, sig_fors_len ⟩ ← fors_sign_spec p hp md sk_seed pk_seed adrs
  let* ⟨ pk_fors, pk_fors_post ⟩ ← fors_pk_from_sig_spec p hp (alloc.vec.Vec.deref sig_fors) md pk_seed
    adrs
  let* ⟨ sig_ht, sig_ht_post, sig_ht_len ⟩ ← ht_sign_spec p hp pk_fors sk_seed pk_seed idx_tree
    idx_leaf idx_leaf_lt
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
  · simp only [Spec.slhSignInternal, block_shape, digestLeaf_shape, digestTree_shape, mdBytes_shape, sigBytes_shape, forsSigBytes_shape, xmssSigBytes_shape, n_shape]
    rw [← hb0, ← hb1, ← hb2, ← hb3, ← r_post, ← digest_post, ← hmd, ← idx_tree_post,
      ← idx_leaf_post, ← hadrs, ← sig_fors_post, ← pk_fors_post, ← sig_ht_post, hsig]
  · rw [sigBytes_eq p hv, forsSigBytes_eq p hp, xmssSigBytes_eq p hp]
    have : sg2.val.length = sg1.val.length + sig_ht.val.length := by rw [sg2_post]; simp
    simp only [alloc.vec.Vec.length] at hl1 sig_ht_len ⊢
    simp only [paramsS_n, paramsS_d, hp.n_eq]
    omega

set_option maxHeartbeats 2000000 in
/-- For every byte string `sig`, of any length. -/
@[step]
theorem slh_verify_internal_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m sig pk : Slice U8)
    (hpk : pk.length = 2 * N.val) (hm : Room m.length (msgSlack N.val)) :
    shake.slh.slh_verify_internal N p m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal (params p) (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  have hv := hp.valid
  have hn := hp.le32
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hp
  have hhl := ht_len_le p hp
  have hfe := forsSigBytes_eq p hp
  have hxe := xmssSigBytes_eq p hp
  unfold shake.slh.slh_verify_internal
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
    let* ⟨ digest, digest_post, digest_len ⟩ ← h_msg_params p
    let* ⟨ idx_tree, idx_tree_post, idx_tree_lt ⟩ ← digest_tree_spec
    let* ⟨ idx_leaf, idx_leaf_post, idx_leaf_lt ⟩ ← digest_leaf_spec
    let* ⟨ a, a_post ⟩ ← adrs_new_spec
    let* ⟨ a1, a1_post ⟩ ← with_tree_spec
    let* ⟨ a2, a2_post, a2_post1 ⟩ ← with_type_spec
    let* ⟨ adrs, adrs_post ⟩ ← with_keypair_spec
    simp only [shake.hash.seed_ctx, bind_ok]
    let* ⟨ s2, s2_post, s2_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    let* ⟨ i2, i2_post, i2_post1 ⟩ ← md_bytes_spec
    let* ⟨ s3, s3_post, s3_len ⟩ ← alloc.vec.Vec.index_Range_spec
    let* ⟨ pk_fors, pk_fors_post ⟩ ← fors_pk_from_sig_spec p hp s2 s3 pk_seed adrs
      (by rw [s2_len, fors_end_post, i1_post, hp.n_eq]; omega) (by rw [s3_len, i2_post]; omega)
    let* ⟨ s4, s4_post, s4_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    let* ⟨ b, b_post ⟩ ← ht_verify_spec p hp pk_fors s4 pk_seed idx_tree idx_leaf pk_root
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
    simp only [Spec.slhVerifyInternal, block_shape, digestLeaf_shape, digestTree_shape, mdBytes_shape, sigBytes_shape, forsSigBytes_shape, xmssSigBytes_shape, n_shape]
    rw [← hb0, ← hb1, ← hr, ← digest_post, ← hmd, ← idx_tree_post,
      ← idx_leaf_post, ← hadrs, ← h5, ← pk_fors_post, ← h9, ← b_post]
    simp [hlen']

@[step]
theorem slh_sign_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m ctx sk : Slice U8)
    (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    shake.slh.slh_sign p m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign (params p) (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold shake.slh.slh_sign
  by_cases hc : ctx.len > 255#usize
  · have : ctx.val.length > 255 := by scalar_tac
    simp [hc, Spec.slhSign, this]
  · have hc' : ctx.length ≤ 255 := by scalar_tac
    have hc'' : ¬ ctx.val.length > 255 := by scalar_tac
    simp only [hc, ite_false]
    have hR := hm
    simp only [Room] at hR
    let* ⟨ mp, mp_post, mp_len ⟩ ← with_context_spec
    let* ⟨ v, v_post, v_len ⟩ ← slh_sign_internal_spec p hp (alloc.vec.Vec.deref mp) sk addrnd hsk
      (room_ctx m N.val _ hm (by simp [mp_len]; omega))
    simp [Spec.slhSign, hc'', v_post, mp_post]

@[step]
theorem slh_verify_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m sig ctx pk : Slice U8)
    (hpk : pk.length = 2 * N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    shake.slh.slh_verify N p m sig ctx pk ⦃ b =>
      b = Spec.slhVerify (params p) (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold shake.slh.slh_verify
  by_cases hc : ctx.len > 255#usize
  · have : ctx.val.length > 255 := by scalar_tac
    simp [hc, Spec.slhVerify, this]
  · have hc' : ctx.length ≤ 255 := by scalar_tac
    have hc'' : ¬ ctx.val.length > 255 := by scalar_tac
    simp only [hc, ite_false]
    have hR := hm
    simp only [Room] at hR
    let* ⟨ mp, mp_post, mp_len ⟩ ← with_context_spec
    let* ⟨ b, b_post ⟩ ← slh_verify_internal_spec p hp (alloc.vec.Vec.deref mp) sig pk hpk
      (room_ctx m N.val _ hm (by simp [mp_len]; omega))
    simp [Spec.slhVerify, hc'', b_post, mp_post]

end slhdsa.Shake
