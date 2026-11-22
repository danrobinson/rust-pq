import Slhdsa.Proofs.Ht
import Slhdsa.Proofs.HashMsg
open Aeneas Aeneas.Std Result

/-! SLH-DSA key generation, signing and verification (FIPS 205 §9, §10),
for any valid parameter set. The key lengths are hypotheses here because the
generic Rust functions take slices; `Proofs/Sets.lean` discharges them for
the six typed instances. -/

namespace slhdsa

@[local step]
theorem extend_spec (v : alloc.vec.Vec U8) (s : Slice U8) (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  rw [dite_eq_left h]
  apply WP.spec_bind (@List.clone_spec _ core.clone.CloneU8.clone s.val (by intros; rfl))
  intro l hl
  simp [hl]

theorem and_mask_val (x m : U64) (n : Nat) (hm : m.val = 2 ^ n - 1) :
    (x &&& m).val = x.val % 2 ^ n := by
  rw [UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]

/-- `u64::MAX >> (64 - b)` is the mask of the low `b` bits. -/
theorem max_shr_val (b : Nat) (h1 : 1 ≤ b) (h2 : b ≤ 64) :
    (2 ^ 64 - 1) >>> (64 - b) = 2 ^ b - 1 := by
  have hq : 0 < 2 ^ (64 - b) := by positivity
  have he : 2 ^ 64 = 2 ^ b * 2 ^ (64 - b) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hb : 0 < 2 ^ b := by positivity
  rw [Nat.shiftRight_eq_div_pow, he]
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul]; have := Nat.le_mul_of_pos_left (2 ^ (64 - b)) hb; omega
  · have : 2 ^ b - 1 + 1 = 2 ^ b := by omega
    rw [this]; have := Nat.mul_pos hb hq; omega

@[step]
theorem digest_tree_spec (p : params.Params) (digest : Slice U8) (hv : (paramsS p).Valid)
    (h : digest.length = p.m.val) :
    slh.digest_tree p digest ⦃ r => r.val = Spec.digestTree (paramsS p) (bytes digest.val) ∧
      r.val < 2 ^ (p.h.val - p.hp.val) ⦄ := by
  have hm := hv.m_eq
  simp only [paramsS_m] at hm
  unfold slh.digest_tree
  step*
  · scalar_tac
  have hm5 : i5.val = 2 ^ i3.val - 1 := by
    rw [i5_post, i4_post]
    exact max_shr_val _ i3_post2 i3_post3
  rw [and_mask_val _ _ _ hm5, i2_post, s_post]
  refine ⟨?_, ?_⟩
  · simp [Spec.digestTree, List.slice, i1_post, ← lo_post1, ← i_post1, i3_post1]
  · rw [← i3_post]; exact Nat.mod_lt _ (by positivity)

@[step]
theorem digest_leaf_spec (p : params.Params) (digest : Slice U8) (hv : (paramsS p).Valid)
    (h : digest.length = p.m.val) :
    slh.digest_leaf p digest ⦃ r => r.val = Spec.digestLeaf (paramsS p) (bytes digest.val) ∧
      r.val < 2 ^ p.hp.val ⦄ := by
  have hm := hv.m_eq
  simp only [paramsS_m] at hm
  have hhp := hv.hp_le
  simp only [paramsS_hp] at hhp
  have hpow : 2 ^ p.hp.val ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp
  have hpos : 0 < 2 ^ p.hp.val := by positivity
  unfold slh.digest_leaf
  step*
  · scalar_tac
  have h5 : i5.val = 2 ^ p.hp.val := by
    rw [i5_post, Nat.one_shiftLeft]
    apply Nat.mod_eq_of_lt
    simp [U64.size, U64.numBits]; omega
  have hm6 : i6.val = 2 ^ p.hp.val - 1 := by rw [i6_post, h5]
  have h7 : i7.val = Spec.digestLeaf (paramsS p) (bytes digest.val) := by
    rw [i7_post, and_mask_val _ _ _ hm6, i4_post, s_post]
    simp [Spec.digestLeaf, List.slice, i3_post, lo_post, ← i_post1, ← i1_post1, ← i2_post1,
      h_div_d p hv]
  have h8 : i7.val < 2 ^ p.hp.val := by
    rw [i7_post, and_mask_val _ _ _ hm6]; exact Nat.mod_lt _ hpos
  have h9 : (UScalar.cast UScalarTy.U32 i7).val = i7.val := by
    simp [UScalar.cast_val_eq]; scalar_tac
  rw [h9]; exact ⟨h7, h8⟩

/-- Size of a FORS signature, bounded. -/
theorem fors_len_le {N : Usize} (p : params.Params) (hp : PN p N) :
    p.k.val * (1 + p.a.val) * N.val ≤ 16800 := by
  have hn := hp.le32
  have hk := hp.valid.k_le
  have ha := hp.valid.a_le
  simp only [paramsS_k, paramsS_a] at hk ha
  have h1 : 1 + p.a.val ≤ 15 := by omega
  calc p.k.val * (1 + p.a.val) * N.val ≤ 35 * 15 * 32 :=
        Nat.mul_le_mul (Nat.mul_le_mul hk h1) hn
    _ = 16800 := by norm_num

/-- Size of a hypertree signature, bounded. -/
theorem ht_len_le {N : Usize} (p : params.Params) (hp : PN p N) :
    p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) ≤ 53504 := by
  have hn := hp.le32
  have hd := hp.valid.d_le
  have hhp := hp.valid.hp_le
  simp only [paramsS_d, paramsS_hp] at hd hhp
  have h1 : 2 * N.val + 3 + p.hp.val ≤ 76 := by omega
  calc p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) ≤ 22 * (76 * 32) :=
        Nat.mul_le_mul hd (Nat.mul_le_mul h1 hn)
    _ = 53504 := by norm_num

theorem forsSigBytes_eq {N : Usize} (p : params.Params) (hp : PN p N) :
    (paramsS p).forsSigBytes = p.k.val * (1 + p.a.val) * N.val := by
  simp [Spec.Params.forsSigBytes, hp.n_eq]

theorem xmssSigBytes_eq {N : Usize} (p : params.Params) (hp : PN p N) :
    (paramsS p).xmssSigBytes = (2 * N.val + 3 + p.hp.val) * N.val := by
  simp [Spec.Params.xmssSigBytes, hp.len, hp.n_eq]

@[step]
theorem with_context_spec (m ctx : Slice U8) (hc : ctx.length ≤ 255)
    (hm : m.length + 257 ≤ Usize.max) :
    slh.with_context m ctx ⦃ r => bytes r.val = Spec.withContext (bytes m.val) (bytes ctx.val) ∧
      r.length = 2 + ctx.length + m.length ⦄ := by
  unfold slh.with_context
  step*
  · have : mp2.length = 2 + ctx.length := by
      simp [alloc.vec.Vec.length, mp2_post, mp1_post, mp_post]; scalar_tac
    scalar_tac
  · constructor
    · simp [r_post, mp2_post, mp1_post, mp_post, Spec.withContext, Spec.toByte, List.range,
        List.range.loop, i1_post]
      apply BitVec.eq_of_toNat_eq
      simp
    · simp [alloc.vec.Vec.length, r_post, mp2_post, mp1_post, mp_post]; scalar_tac

theorem setSlice_gen {α} (X Y s : List α) (i : Nat) (hi : i = X.length) (hs : s.length ≤ Y.length) :
    (X ++ Y).setSlice! i s = X ++ s ++ Y.drop s.length := by
  subst hi
  have hm : min s.length (X.length + Y.length - X.length) = s.length := by omega
  have hm2 : min s.length Y.length = s.length := by omega
  simp [List.setSlice!, hm, hm2, List.take_of_length_le, List.drop_append]

/-- Four pieces written over a slice that they fill. -/
theorem setSlice4 {α} (l A L R M : List α) (i j k : Nat) (hi : i = A.length)
    (hj : j = A.length + L.length) (hk : k = A.length + L.length + R.length)
    (hl : l.length = A.length + L.length + R.length + M.length) :
    ((((l.setSlice! 0 A).setSlice! i L).setSlice! j R).setSlice! k M) = A ++ L ++ R ++ M := by
  rw [show l = [] ++ l by simp, setSlice_gen [] l A 0 rfl (by omega), List.nil_append,
    setSlice_gen A _ L i hi (by simp; omega),
    setSlice_gen (A ++ L) _ R j (by simp [hj]) (by simp; omega),
    setSlice_gen (A ++ L ++ R) _ M k (by simp [hk]; omega) (by simp; omega)]
  have : (List.drop M.length (List.drop R.length (List.drop L.length (List.drop A.length l)))) = [] := by
    simp; omega
  rw [this]; simp

theorem setSlice2 {α} (l A L : List α) (i : Nat) (hi : i = A.length)
    (hl : l.length = A.length + L.length) :
    ((l.setSlice! 0 A).setSlice! i L) = A ++ L := by
  rw [show l = [] ++ l by simp, setSlice_gen [] l A 0 rfl (by omega), List.nil_append,
    setSlice_gen A _ L i hi (by simp; omega)]
  have : List.drop L.length (List.drop A.length l) = [] := by simp; omega
  rw [this]; simp

set_option maxHeartbeats 2000000 in
@[step]
theorem slh_keygen_internal_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (sk_seed sk_prf pk_seed : Array U8 N) (sk pk : Slice U8)
    (hsk : sk.length = 4 * N.val) (hpk : pk.length = 2 * N.val) :
    slh.slh_keygen_internal p sk_seed sk_prf pk_seed sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal (paramsS p) (bytes sk_seed.val) (bytes sk_prf.val)
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
  unfold slh.slh_keygen_internal
  let* ⟨ a, a_post ⟩ ← adrs_new_spec
  let* ⟨ i, i_post ⟩ ← U32.sub_spec
  let* ⟨ adrs, adrs_post ⟩ ← with_layer_spec
  let* ⟨ seed, seed_pk, seed_ok ⟩ ← seed_ctx_spec hp.nok
  let* ⟨ pk_root, pk_root_post ⟩ ← xmss_node_spec p hp sk_seed 0#u32 p.hp seed seed_ok adrs
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
  · simp [Spec.slhKeygenInternal, hsk4, hpk2, pk_root_post, ha, seed_pk]
  · simp only [Slice.length, hsk4, List.length_append]; omega
  · simp only [Slice.length, hpk2, List.length_append]; omega

theorem bytes_block_N {N : Usize} (p : params.Params) (hp : PN p N) (s : Slice U8) (r : Array U8 N)
    (i : Nat) (h : r.val = (s.val.drop (i * N.val)).take N.val) :
    bytes r.val = Spec.block (paramsS p) (bytes s.val) i :=
  bytes_block (paramsS p) s.val r.val i (by rw [h, hp.n])

set_option maxHeartbeats 2000000 in
@[step]
theorem slh_sign_internal_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Slice U8)
    (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val) (hm : Room m.length (msgSlack N.val)) :
    slh.slh_sign_internal p m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal (paramsS p) (bytes m.val) (bytes sk.val)
        (bytes addrnd.val) ∧
      sig.length = (paramsS p).sigBytes ⦄ := by
  have hv := hp.valid
  have hn := hp.le32
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hp
  have hhl := ht_len_le p hp
  unfold slh.slh_sign_internal
  let* ⟨ sk_seed, sk_seed_post ⟩ ← block_spec
  let* ⟨ sk_prf, sk_prf_post ⟩ ← block_spec
  let* ⟨ pk_seed, pk_seed_post ⟩ ← block_spec
  let* ⟨ pk_root, pk_root_post ⟩ ← block_spec
  let* ⟨ r, r_post ⟩ ← prf_msg_spec (paramsS p) hp.n hp.nok
  let* ⟨ digest, digest_post, digest_len ⟩ ← h_msg_spec p hv hp.n_eq
  let* ⟨ idx_tree, idx_tree_post, idx_tree_lt ⟩ ← digest_tree_spec
  let* ⟨ idx_leaf, idx_leaf_post, idx_leaf_lt ⟩ ← digest_leaf_spec
  let* ⟨ a, a_post ⟩ ← adrs_new_spec
  let* ⟨ a1, a1_post ⟩ ← with_tree_spec
  let* ⟨ a2, a2_post, a2_post1 ⟩ ← with_type_spec
  let* ⟨ adrs, adrs_post ⟩ ← with_keypair_spec
  let* ⟨ seed, seed_pk, seed_ok ⟩ ← seed_ctx_spec hp.nok
  let* ⟨ i, i_post, i_post1 ⟩ ← md_bytes_spec
  let* ⟨ md, md_post, md_len ⟩ ← alloc.vec.Vec.index_Range_spec
  let* ⟨ sig_fors, sig_fors_post, sig_fors_len ⟩ ← fors_sign_spec p hp md sk_seed seed seed_ok adrs
  let* ⟨ pk_fors, pk_fors_post ⟩ ← fors_pk_from_sig_spec p hp (alloc.vec.Vec.deref sig_fors) md seed
    seed_ok adrs
  let* ⟨ sig_ht, sig_ht_post, sig_ht_len ⟩ ← ht_sign_spec p hp pk_fors sk_seed seed seed_ok idx_tree
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
  rw [seed_pk] at sig_fors_post pk_fors_post sig_ht_post
  constructor
  · simp only [Spec.slhSignInternal]
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
theorem slh_verify_internal_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sig pk : Slice U8)
    (hpk : pk.length = 2 * N.val) (hm : Room m.length (msgSlack N.val)) :
    slh.slh_verify_internal N p m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal (paramsS p) (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  have hv := hp.valid
  have hn := hp.le32
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hp
  have hhl := ht_len_le p hp
  have hfe := forsSigBytes_eq p hp
  have hxe := xmssSigBytes_eq p hp
  unfold slh.slh_verify_internal
  let* ⟨ sig_bytes, sig_bytes_post, sig_bytes_post1 ⟩ ← sig_bytes_spec
  split
  · rename_i hlen
    have : sig.val.length ≠ (paramsS p).sigBytes := by
      simp only [bne_iff_ne, ne_eq] at hlen
      intro h; apply hlen; scalar_tac
    simp [Spec.slhVerifyInternal, this]
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
    let* ⟨ digest, digest_post, digest_len ⟩ ← h_msg_spec p hv hp.n_eq
    let* ⟨ idx_tree, idx_tree_post, idx_tree_lt ⟩ ← digest_tree_spec
    let* ⟨ idx_leaf, idx_leaf_post, idx_leaf_lt ⟩ ← digest_leaf_spec
    let* ⟨ a, a_post ⟩ ← adrs_new_spec
    let* ⟨ a1, a1_post ⟩ ← with_tree_spec
    let* ⟨ a2, a2_post, a2_post1 ⟩ ← with_type_spec
    let* ⟨ adrs, adrs_post ⟩ ← with_keypair_spec
    let* ⟨ seed, seed_pk, seed_ok ⟩ ← seed_ctx_spec hp.nok
    let* ⟨ s2, s2_post, s2_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    let* ⟨ i2, i2_post, i2_post1 ⟩ ← md_bytes_spec
    let* ⟨ s3, s3_post, s3_len ⟩ ← alloc.vec.Vec.index_Range_spec
    let* ⟨ pk_fors, pk_fors_post ⟩ ← fors_pk_from_sig_spec p hp s2 s3 seed seed_ok adrs
      (by rw [s2_len, fors_end_post, i1_post, hp.n_eq]; omega) (by rw [s3_len, i2_post]; omega)
    let* ⟨ s4, s4_post, s4_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    let* ⟨ b, b_post ⟩ ← ht_verify_spec p hp pk_fors s4 seed seed_ok idx_tree idx_leaf pk_root
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
    rw [seed_pk] at pk_fors_post b_post
    simp only [vec_deref_val] at *
    simp only [Spec.slhVerifyInternal]
    rw [if_neg (by simp [hlen']), ← hb0, ← hb1, ← hr, ← digest_post, ← hmd, ← idx_tree_post,
      ← idx_leaf_post, ← hadrs, ← h5, ← pk_fors_post, ← h9, ← b_post]

theorem room_ctx (m : Slice U8) (n : Nat) (L : Nat) (hm : Room m.length (msgSlack n + 257))
    (hL : L ≤ 257 + m.length) : Room L (msgSlack n) := by
  simp only [Room] at *; omega

@[step]
theorem slh_sign_spec {N : Usize} (p : params.Params) (hp : PN p N) (m ctx sk : Slice U8)
    (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    slh.slh_sign p m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign (paramsS p) (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold slh.slh_sign
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
theorem slh_verify_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sig ctx pk : Slice U8)
    (hpk : pk.length = 2 * N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    slh.slh_verify N p m sig ctx pk ⦃ b =>
      b = Spec.slhVerify (paramsS p) (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold slh.slh_verify
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

end slhdsa
