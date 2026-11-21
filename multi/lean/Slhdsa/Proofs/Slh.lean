import Slhdsa.Proofs.Fors
import Slhdsa.Proofs.Ht
open Aeneas Aeneas.Std Result

/-! SLH-DSA key generation, signing and verification (FIPS 205 §9, §10),
for any valid parameter set. The key and seed lengths are hypotheses here
because the generic Rust functions take slices; `Proofs/Sets.lean` discharges
them for the six typed instances. -/

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
theorem fors_len_le (p : params.Params) (hv : (paramsS p).Valid) :
    p.k.val * (1 + p.a.val) * p.n.val ≤ 16800 := by
  have hn : p.n.val ≤ 32 := by
    have := hv.n_cases; simp only [paramsS_n] at this; omega
  have hk := hv.k_le
  have ha := hv.a_le
  simp only [paramsS_k, paramsS_a] at hk ha
  have h1 : 1 + p.a.val ≤ 15 := by omega
  calc p.k.val * (1 + p.a.val) * p.n.val ≤ 35 * 15 * 32 :=
        Nat.mul_le_mul (Nat.mul_le_mul hk h1) hn
    _ = 16800 := by norm_num

/-- Size of a hypertree signature, bounded. -/
theorem ht_len_le (p : params.Params) (hv : (paramsS p).Valid) :
    p.d.val * ((2 * p.n.val + 3 + p.hp.val) * p.n.val) ≤ 53504 := by
  have hn : p.n.val ≤ 32 := by
    have := hv.n_cases; simp only [paramsS_n] at this; omega
  have hd := hv.d_le
  have hhp := hv.hp_le
  simp only [paramsS_d, paramsS_hp] at hd hhp
  have h1 : 2 * p.n.val + 3 + p.hp.val ≤ 76 := by omega
  calc p.d.val * ((2 * p.n.val + 3 + p.hp.val) * p.n.val) ≤ 22 * (76 * 32) :=
        Nat.mul_le_mul hd (Nat.mul_le_mul h1 hn)
    _ = 53504 := by norm_num

theorem forsSigBytes_eq (p : params.Params) :
    (paramsS p).forsSigBytes = p.k.val * (1 + p.a.val) * p.n.val := by
  simp [Spec.Params.forsSigBytes]

theorem xmssSigBytes_eq (p : params.Params) (hv : (paramsS p).Valid) :
    (paramsS p).xmssSigBytes = (2 * p.n.val + 3 + p.hp.val) * p.n.val := by
  simp [Spec.Params.xmssSigBytes, len_eq p hv]

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

@[step]
theorem slh_keygen_internal_spec (p : params.Params) (sk_seed sk_prf pk_seed : Slice U8)
    (hv : (paramsS p).Valid) (h1 : sk_seed.length = p.n.val) (h2 : sk_prf.length = p.n.val)
    (h3 : pk_seed.length = p.n.val) :
    slh.slh_keygen_internal p sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal (paramsS p) (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val) ∧
      r.1.length = 4 * p.n.val ∧ r.2.length = 2 * p.n.val ⦄ := by
  have hn : p.n.val ≤ 32 := by
    have := hv.n_cases; simp only [paramsS_n] at this; omega
  have hd := hv.d_ge
  simp only [paramsS_d] at hd
  have hhp := hv.hp_le
  simp only [paramsS_hp] at hhp
  have hpow : (0 + 1) * 2 ^ p.hp.val ≤ 2 ^ 32 := by
    have : 2 ^ p.hp.val ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp
    omega
  unfold slh.slh_keygen_internal
  step*
  have ha : adrsS adrs = { Spec.Adrs.zero with layer := p.d.val - 1 } := by
    simp [adrsS, adrs_post, a_post, Spec.Adrs.zero, i_post]
  refine ⟨?_, ?_, ?_⟩
  · simp [Spec.slhKeygenInternal, sk3_post, sk2_post, sk1_post, sk_post, pk1_post, pk_post,
      pk_root_post, ha]
  · simp [alloc.vec.Vec.length, sk3_post, sk2_post, sk1_post, sk_post] at *; scalar_tac
  · simp [alloc.vec.Vec.length, pk1_post, pk_post] at *; scalar_tac

@[step]
theorem slh_sign_internal_spec (p : params.Params) (m sk addrnd : Slice U8)
    (hv : (paramsS p).Valid) (hsk : sk.length = 4 * p.n.val) (hr : addrnd.length = p.n.val)
    (hm : Room m.length 304) :
    slh.slh_sign_internal p m sk addrnd ⦃ sig =>
      bytes sig.val = Spec.slhSignInternal (paramsS p) (bytes m.val) (bytes sk.val)
        (bytes addrnd.val) ∧
      sig.length = (paramsS p).sigBytes ⦄ := by
  have hn : p.n.val ≤ 32 := by
    have := hv.n_cases; simp only [paramsS_n] at this; omega
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hv
  have hhl := ht_len_le p hv
  unfold slh.slh_sign_internal
  step*
  · have : sig.length = p.n.val := by
      simp [alloc.vec.Vec.length, sig_post] at *; scalar_tac
    have : sig_fors.deref.length = sig_fors.length := vec_deref_length sig_fors
    scalar_tac
  · have : sig1.length = p.n.val + p.k.val * (1 + p.a.val) * p.n.val := by
      simp [alloc.vec.Vec.length, sig1_post, sig_post] at *; scalar_tac
    have : sig_ht.deref.length = sig_ht.length := vec_deref_length sig_ht
    scalar_tac
  · rename_i sig0 _ sig0_post _
    have hb0 := bytes_block p sk.val sk_seed.val 0 sk_seed_post
    have hb1 := bytes_block p sk.val sk_prf.val 1 sk_prf_post
    have hb2 := bytes_block p sk.val pk_seed.val 2 pk_seed_post
    have hb3 := bytes_block p sk.val pk_root.val 3 pk_root_post
    have hadrs : adrsS adrs = { { Spec.Adrs.zero with tree := idx_tree.val }.setTypeAndClear
        Spec.FORS_TREE with keypair := idx_leaf.val } := by
      simp [adrsS, adrs_post, a2_post1, a1_post, a_post, Spec.Adrs.setTypeAndClear,
        Spec.Adrs.zero, Spec.FORS_TREE, global_simps]
    have hmd : bytes md.val = (bytes digest.val).take (paramsS p).mdBytes := by
      simp [md_post, List.slice, i_post1]
    have hlen : sig.val.length = r.val.length + sig_fors.val.length + sig_ht.val.length := by
      simp [sig_post, sig1_post, sig0_post]; omega
    have hsig : bytes sig.val = bytes r.val ++ bytes sig_fors.val ++ bytes sig_ht.val := by
      simp [sig_post, sig1_post, sig0_post]
    simp only [vec_deref_val] at *
    constructor
    · simp only [Spec.slhSignInternal]
      rw [← hb0, ← hb1, ← hb2, ← hb3, ← r_post, ← digest_post, ← hmd, ← idx_tree_post,
        ← idx_leaf_post, ← hadrs, ← sig_fors_post, ← pk_fors_post, ← sig_ht_post, hsig]
    · rw [sigBytes_eq p hv, forsSigBytes_eq, xmssSigBytes_eq p hv]
      simp only [alloc.vec.Vec.length] at *
      omega

/-- For every byte string `sig`, of any length. -/
@[step]
theorem slh_verify_internal_spec (p : params.Params) (m sig pk : Slice U8)
    (hv : (paramsS p).Valid) (hpk : pk.length = 2 * p.n.val) (hm : Room m.length 304) :
    slh.slh_verify_internal p m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal (paramsS p) (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  have hn : p.n.val ≤ 32 := by
    have := hv.n_cases; simp only [paramsS_n] at this; omega
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hv
  have hhl := ht_len_le p hv
  have hfe := forsSigBytes_eq p
  have hxe := xmssSigBytes_eq p hv
  unfold slh.slh_verify_internal
  step*
  · rename_i hlen
    have : sig.val.length ≠ (paramsS p).sigBytes := by
      simp only [bne_iff_ne, ne_eq] at hlen
      intro h; apply hlen; scalar_tac
    simp [Spec.slhVerifyInternal, this]
  · rw [s5_post1, fors_end_post, i1_post]; omega
  · rw [s9_post1, sig_bytes_post1, fors_end_post, i1_post1, hxe]; omega
  · have hlen' : sig.val.length = (paramsS p).sigBytes := by
      have hlen := ‹¬(sig.len != sig_bytes) = true›
      simp at hlen; scalar_tac
    have hb0 := bytes_block p pk.val pk_seed.val 0 pk_seed_post
    have hb1 := bytes_block p pk.val pk_root.val 1 pk_root_post
    have hadrs : adrsS adrs = { { Spec.Adrs.zero with tree := idx_tree.val }.setTypeAndClear
        Spec.FORS_TREE with keypair := idx_leaf.val } := by
      simp [adrsS, adrs_post, a2_post1, a1_post, a_post, Spec.Adrs.setTypeAndClear,
        Spec.Adrs.zero, Spec.FORS_TREE, global_simps]
    have hmd : bytes s6.val = (bytes digest.val).take (paramsS p).mdBytes := by
      simp [s6_post, List.slice, i2_post1]
    have h5 : bytes s5.val =
        ((bytes sig.val).drop p.n.val).take (paramsS p).forsSigBytes := by
      simp [s5_post, List.slice, fors_end_post, i1_post1]
    have h9 : bytes s9.val = (bytes sig.val).drop (p.n.val + (paramsS p).forsSigBytes) := by
      rw [s9_post]
      simp only [List.slice]
      rw [List.take_of_length_le (by simp only [List.length_drop]; scalar_tac)]
      simp [fors_end_post, i1_post1]
    have hr : bytes r.val = (bytes sig.val).take p.n.val := by
      simp [r_post]
    simp only [vec_deref_val] at *
    simp only [Spec.slhVerifyInternal, paramsS_n]
    rw [ite_eq_right (by simp [hlen']), ← hb0, ← hb1, ← hr, ← digest_post, ← hmd, ← idx_tree_post,
      ← idx_leaf_post, ← hadrs, ← h5, ← pk_fors_post, ← h9, ← b_post]

@[step]
theorem slh_sign_spec (p : params.Params) (m ctx sk addrnd : Slice U8)
    (hv : (paramsS p).Valid) (hsk : sk.length = 4 * p.n.val) (hr : addrnd.length = p.n.val)
    (hm : Room m.length 561) :
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
    step*
    · simp only [Room] at *
      have h1 : mp.deref.length = mp.length := vec_deref_length mp
      scalar_tac
    · simp [Spec.slhSign, *]

@[step]
theorem slh_verify_spec (p : params.Params) (m sig ctx pk : Slice U8)
    (hv : (paramsS p).Valid) (hpk : pk.length = 2 * p.n.val) (hm : Room m.length 561) :
    slh.slh_verify p m sig ctx pk ⦃ b =>
      b = Spec.slhVerify (paramsS p) (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val) ⦄ := by
  unfold slh.slh_verify
  by_cases hc : ctx.len > 255#usize
  · have : ctx.val.length > 255 := by scalar_tac
    simp [hc, Spec.slhVerify, this]
  · have hc' : ctx.length ≤ 255 := by scalar_tac
    have hc'' : ¬ ctx.val.length > 255 := by scalar_tac
    simp only [hc, ite_false]
    step*
    · simp only [Room] at *
      have h1 : mp.deref.length = mp.length := vec_deref_length mp
      scalar_tac
    · simp [Spec.slhVerify, *]

end slhdsa
