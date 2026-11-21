import Slhdsa.Proofs.Ht
import Slhdsa.Proofs.Fors
open Aeneas Aeneas.Std Result

/-! SLH-DSA key generation, signing and verification. -/

namespace slhdsa

@[local step]
theorem extend_spec (v : alloc.vec.Vec U8) (s : Slice U8) (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  rw [dif_pos h]
  apply WP.spec_bind (@List.clone_spec _ core.clone.CloneU8.clone s.val (by intros; rfl))
  intro l hl
  simp [hl]

theorem and_mask_val (x m : U64) (n : Nat) (hm : m.val = 2 ^ n - 1) :
    (x &&& m).val = x.val % 2 ^ n := by
  rw [UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]

theorem setSlice!_eq {α} (s s' : List α) (i : Nat) (h : i + s'.length ≤ s.length) :
    s.setSlice! i s' = s.take i ++ s' ++ s.drop (i + s'.length) := by
  have : min s'.length (s.length - i) = s'.length := by omega
  simp [List.setSlice!, this]

theorem take_setSlice! {α} (l s' pre : List α) (i : Nat) (hpre : l.take i = pre)
    (hi : i + s'.length ≤ l.length) :
    (l.setSlice! i s').take (i + s'.length) = pre ++ s' := by
  have hlen : (l.take i ++ s').length = i + s'.length := by simp; omega
  rw [setSlice!_eq _ _ _ hi, ← hpre]
  exact List.take_left' (l₁ := l.take i ++ s') (l₂ := l.drop (i + s'.length)) hlen

@[step]
theorem digest_tree_spec (digest : Slice U8) (h : digest.length = 30) :
    slh.digest_tree digest ⦃ r => r.val = Spec.digestTree (bytes digest.val) ∧ r.val < 2 ^ 54 ⦄ := by
  unfold slh.digest_tree
  step*
  · simp [global_simps]; scalar_tac
  · simp [global_simps] at *; scalar_tac
  · simp [global_simps] at *; scalar_tac
  · have hm : i3.val = 2 ^ 54 - 1 := by
      rw [i3_post, i2_post]; simp [U64.size, U64.numBits]
    rw [and_mask_val _ _ 54 hm, i1_post, s_post]
    refine ⟨?_, Nat.mod_lt _ (by decide)⟩
    simp [Spec.digestTree, Spec.mdBytes, Spec.treeBytes, Spec.h, Spec.d, Spec.k, Spec.a,
      List.slice, global_simps, i_post]

@[step]
theorem digest_leaf_spec (digest : Slice U8) (h : digest.length = 30) :
    slh.digest_leaf digest ⦃ r => r.val = Spec.digestLeaf (bytes digest.val) ∧ r.val < 2 ^ 9 ⦄ := by
  unfold slh.digest_leaf
  step*
  · simp [global_simps]; scalar_tac
  · simp [global_simps] at *; scalar_tac
  · simp [global_simps] at *; scalar_tac
  · simp [global_simps] at *; scalar_tac
  · simp [global_simps]
  · simp [global_simps, U64.size, U64.numBits] at *; scalar_tac
  · have hm : i4.val = 2 ^ 9 - 1 := by
      rw [i4_post, i3_post]; simp [U64.size, U64.numBits, global_simps]
    have h5 : i5.val = Spec.digestLeaf (bytes digest.val) := by
      rw [i5_post, and_mask_val _ _ 9 hm, i2_post, s_post]
      simp [Spec.digestLeaf, Spec.mdBytes, Spec.treeBytes, Spec.leafBytes, Spec.h, Spec.d, Spec.k,
        Spec.a, List.slice, global_simps, i_post, i1_post]
    have h6 : i5.val < 2 ^ 9 := by
      rw [i5_post, and_mask_val _ _ 9 hm]; exact Nat.mod_lt _ (by decide)
    have h7 : (UScalar.cast UScalarTy.U32 i5).val = i5.val := by
      simp [UScalar.cast_val_eq]; scalar_tac
    rw [h7]; exact ⟨h5, h6⟩

@[step]
theorem with_context_spec (m ctx : Slice U8) (hc : ctx.length ≤ 255) (hm : m.length + 257 ≤ Usize.max) :
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
theorem slh_keygen_internal_spec (sk_seed sk_prf pk_seed : Array U8 16#usize) :
    slh.slh_keygen_internal sk_seed sk_prf pk_seed ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) ⦄ := by
  unfold slh.slh_keygen_internal
  simp only [global_simps]
  step*
  have hi1 : i1.val = 32 := by scalar_tac
  have hi2 : i2.val = 48 := by scalar_tac
  subst s2_post s1_post s5_post s4_post s8_post s7_post s11_post s10_post s14_post s13_post
    s17_post s16_post
  have e1 : (index_mut_back sk_seed.to_slice).val.take 16 = sk_seed.val := by
    have := take_setSlice! (Array.repeat 64#usize 0#u8).val sk_seed.val [] 0 (by simp) (by simp)
    simpa [s_post2] using this
  have e2 : (index_mut_back1 sk_prf.to_slice).val.take 32 = sk_seed.val ++ sk_prf.val := by
    have := take_setSlice! (index_mut_back sk_seed.to_slice).val sk_prf.val _ 16 e1 (by simp)
    simpa [s3_post2] using this
  have e3 : (index_mut_back2 pk_seed.to_slice).val.take 48 =
      sk_seed.val ++ sk_prf.val ++ pk_seed.val := by
    have := take_setSlice! (index_mut_back1 sk_prf.to_slice).val pk_seed.val _ 32 e2 (by simp)
    simpa [s6_post2, hi1] using this
  have e4 : (index_mut_back3 pk_root.to_slice).val =
      sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val := by
    have := take_setSlice! (index_mut_back2 pk_seed.to_slice).val pk_root.val _ 48 e3 (by simp)
    rw [List.take_of_length_le (by simp)] at this
    simpa [s9_post2, hi2] using this
  have f1 : (index_mut_back4 pk_seed.to_slice).val.take 16 = pk_seed.val := by
    have := take_setSlice! (Array.repeat 32#usize 0#u8).val pk_seed.val [] 0 (by simp) (by simp)
    simpa [s12_post2] using this
  have f2 : (index_mut_back5 pk_root.to_slice).val = pk_seed.val ++ pk_root.val := by
    have := take_setSlice! (index_mut_back4 pk_seed.to_slice).val pk_root.val _ 16 f1 (by simp)
    rw [List.take_of_length_le (by simp)] at this
    simpa [s15_post2] using this
  have ha : adrsS adrs = { Spec.Adrs.zero with layer := Spec.d - 1 } := by
    simp [adrsS, adrs_post, a_post, Spec.Adrs.zero, Spec.d, i_post]
  simp [e4, f2, Spec.slhKeygenInternal, pk_root_post, ha, Spec.hp]

@[step]
theorem slh_sign_internal_spec (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 152) :
    slh.slh_sign_internal m sk addrnd ⦃ r =>
      bytes r.val = Spec.slhSignInternal (bytes m.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold slh.slh_sign_internal
  simp only [global_simps]
  step*
  · simp only [Room] at *; omega
  · simp [alloc.vec.Vec.length, alloc.vec.Vec.deref, sig_post, s8_post] at *; scalar_tac
  · simp [alloc.vec.Vec.length, alloc.vec.Vec.deref, sig1_post, sig_post, s8_post] at *; scalar_tac
  · have hadrs : adrsS adrs = { { Spec.Adrs.zero with tree := idx_tree.val }.setTypeAndClear
        Spec.FORS_TREE with keypair := idx_leaf.val } := by
      simp [adrsS, adrs_post, a2_post1, a1_post, a_post, Spec.Adrs.setTypeAndClear,
        Spec.Adrs.zero, Spec.FORS_TREE]
    have hmd : bytes s6.val = (bytes digest.val).take Spec.mdBytes := by
      simp [s6_post, List.slice, Spec.mdBytes, Spec.k, Spec.a]
    have hr : ∃ r0 : Array U8 16#usize,
        bytes r0.val = Spec.PRFmsg (bytes sk_prf.val) (bytes addrnd.val) (bytes m.val) ∧
        bytes digest.val = Spec.Hmsg (bytes r0.val) (bytes pk_seed.val) (bytes pk_root.val)
          (bytes m.val) ∧ sig.val = (alloc.vec.Vec.new U8).val ++ r0.val :=
      ⟨_, by with_reducible assumption, digest_post, by rw [sig_post, s8_post, Array.val_to_slice]⟩
    obtain ⟨r0, hr, digest_post, sig_post⟩ := hr
    have hdf : (alloc.vec.Vec.deref sig_fors).val = sig_fors.val := by simp [alloc.vec.Vec.deref]
    have hdh : (alloc.vec.Vec.deref sig_ht).val = sig_ht.val := by simp [alloc.vec.Vec.deref]
    subst s_post s1_post s2_post s3_post s4_post s5_post
    simp only [Array.val_to_slice, hdf, hdh] at *
    simp only [Spec.slhSignInternal]
    rw [← sk_seed_post1, ← sk_prf_post1, ← pk_seed_post1, ← pk_root_post1, ← hr, ← digest_post,
      ← hmd, ← idx_tree_post, ← idx_leaf_post, ← hadrs, ← sig_fors_post, ← pk_fors_post,
      ← sig_ht_post, r_post, sig1_post, sig_post]
    simp

@[step]
theorem slh_verify_internal_spec (m sig : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 152) :
    slh.slh_verify_internal m sig pk ⦃ b =>
      b = Spec.slhVerifyInternal (bytes m.val) (bytes sig.val) (bytes pk.val) ⦄ := by
  unfold slh.slh_verify_internal
  simp only [global_simps]
  have hsb : Spec.sigBytes = 7856 := by decide
  have hfb : Spec.forsSigBytes = 2912 := by decide
  step*
  · rename_i hlen
    have : sig.val.length ≠ 7856 := by
      simp only [bne_iff_ne, ne_eq] at hlen
      intro h; apply hlen; scalar_tac
    simp [Spec.slhVerifyInternal, hsb, this]
  · simp only [Room] at *; omega
  · have hlen' : sig.val.length = 7856 := by
      have hlen := ‹¬(sig.len != 7856#usize) = true›
      simp at hlen; scalar_tac
    have hadrs : adrsS adrs = { { Spec.Adrs.zero with tree := idx_tree.val }.setTypeAndClear
        Spec.FORS_TREE with keypair := idx_leaf.val } := by
      simp [adrsS, adrs_post, a2_post1, a1_post, a_post, Spec.Adrs.setTypeAndClear,
        Spec.Adrs.zero, Spec.FORS_TREE]
    have hmd : bytes s5.val = (bytes digest.val).take Spec.mdBytes := by
      simp [s5_post, List.slice, Spec.mdBytes, Spec.k, Spec.a]
    have h4 : bytes s4.val = ((bytes sig.val).drop Spec.n).take Spec.forsSigBytes := by
      simp [s4_post, List.slice, i1_post, hfb, Spec.n]
    have h6 : bytes s6.val = (bytes sig.val).drop (Spec.n + Spec.forsSigBytes) := by
      simp [s6_post, List.slice, i1_post, hfb, Spec.n]
      omega
    have hr : bytes r.val = (bytes sig.val).take Spec.n := by
      rw [r_post1]; simp [Spec.block]
    subst s_post s1_post s2_post s3_post
    simp only [Array.val_to_slice] at *
    simp only [Spec.slhVerifyInternal]
    rw [if_neg (by simp [hsb, hlen']), ← pk_seed_post1, ← pk_root_post1, ← hr, ← digest_post,
      ← hmd, ← idx_tree_post, ← idx_leaf_post, ← hadrs, ← h4, ← pk_fors_post, ← h6, ← b_post]

theorem slh_sign_spec (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    slh.slh_sign m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold slh.slh_sign
  by_cases hc : ctx.len > 255#usize
  · have : ctx.val.length > 255 := by scalar_tac
    simp [hc, Spec.slhSign, this]
  · have hc' : ctx.length ≤ 255 := by scalar_tac
    have hc'' : ¬ ctx.val.length > 255 := by scalar_tac
    simp only [hc, ite_false]
    step*
    · have h1 : mp.deref.length = mp.length := by
        simp [alloc.vec.Vec.deref, Slice.length, alloc.vec.Vec.length]
      simp only [Room] at *; scalar_tac
    · simp [Spec.slhSign, hc'', *, alloc.vec.Vec.deref]

theorem slh_verify_spec (m sig ctx : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 409) :
    slh.slh_verify m sig ctx pk ⦃ b =>
      b = Spec.slhVerify (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold slh.slh_verify
  by_cases hc : ctx.len > 255#usize
  · have : ctx.val.length > 255 := by scalar_tac
    simp [hc, Spec.slhVerify, this]
  · have hc' : ctx.length ≤ 255 := by scalar_tac
    have hc'' : ¬ ctx.val.length > 255 := by scalar_tac
    simp only [hc, ite_false]
    step*
    · have h1 : mp.deref.length = mp.length := by
        simp [alloc.vec.Vec.deref, Slice.length, alloc.vec.Vec.length]
      simp only [Room] at *; scalar_tac
    · simp [Spec.slhVerify, hc'', *, alloc.vec.Vec.deref]

end slhdsa
