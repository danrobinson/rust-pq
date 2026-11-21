import Slhdsa.Proofs.Wots
open Aeneas Aeneas.Std Result

/-! XMSS. -/

namespace slhdsa

/-- Appending a byte slice to a byte vector. -/
private theorem xmss_extend_u8_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (l := s.val) (by intro x _; rfl))
  intro l' hl'
  simp [hl']

attribute [local step] xmss_extend_u8_spec

@[step]
theorem hash2_spec (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) (l r : Array U8 16#usize) :
    xmss.hash2 pk a l r ⦃ x =>
      bytes x.val = Spec.H (bytes pk.pk_seed.val) (adrsS a) (bytes l.val ++ bytes r.val) ⦄ := by
  unfold xmss.hash2
  simp only [global_simps]
  step*
  have hb1 : (index_mut_back s2).val = [] ++ l.val ++ List.replicate 16 0#u8 := by
    rw [s_post2, s2_post, s1_post, Array.val_to_slice,
      show (Array.repeat 32#usize 0#u8).val = [] ++ List.replicate 16 0#u8 ++ List.replicate 16 0#u8
        by simp]
    exact setSlice!_mid _ _ _ _ _ rfl (by simp)
  have hb2 : (index_mut_back1 s5).val = l.val ++ r.val ++ [] := by
    rw [s3_post2, s5_post, s4_post, Array.val_to_slice, hb1, List.nil_append,
      show l.val ++ List.replicate 16 0#u8 = l.val ++ List.replicate 16 0#u8 ++ [] by simp]
    exact setSlice!_mid _ _ _ _ _ (by simp [params.N]) (by simp)
  simp [Spec.H, x_post, s6_post, hb2]

private theorem xmss_node_aux (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) (n : Nat) :
    ∀ (i z : U32), z.val = n → (i.val + 1) * 2 ^ n ≤ 2 ^ 32 →
    xmss.xmss_node sk i z pk a ⦃ r =>
      bytes r.val = Spec.xmssNode (bytes sk.val) i.val n (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  induction n with
  | zero =>
    intro i z hz h
    unfold xmss.xmss_node
    have hz0 : z = 0#u32 := by scalar_tac
    simp only [hz0, ↓reduceIte]
    step*
    simp [*, Spec.xmssNode, adrsS, Spec.Adrs.setTypeAndClear, Spec.WOTS_HASH, address.WOTS_HASH]
  | succ n ih =>
    intro i z hz h
    unfold xmss.xmss_node
    have hz0 : ¬ z = 0#u32 := by scalar_tac
    simp only [hz0, ↓reduceIte]
    have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide)
    have he : (2 * i.val + 2) * 2 ^ n = (i.val + 1) * 2 ^ (n + 1) := by ring
    have h1 : (2 * i.val + 1 + 1) * 2 ^ n ≤ 2 ^ 32 := by rw [← he] at h; exact h
    have h0 : (2 * i.val + 1) * 2 ^ n ≤ 2 ^ 32 :=
      le_trans (Nat.mul_le_mul_right _ (by omega)) h1
    have hb : 2 * i.val + 2 ≤ 2 ^ 32 := le_trans (Nat.le_mul_of_pos_right _ hpos) h1
    step*
    simp [*, Spec.xmssNode, adrsS, Spec.Adrs.setTypeAndClear, Spec.TREE, address.TREE]

@[step]
theorem xmss_node_spec (sk : Array U8 16#usize) (i z : U32) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (h : (i.val + 1) * 2 ^ z.val ≤ 2 ^ 32) :
    xmss.xmss_node sk i z pk a ⦃ r =>
      bytes r.val = Spec.xmssNode (bytes sk.val) i.val z.val (bytes pk.pk_seed.val) (adrsS a) ⦄ :=
  xmss_node_aux sk pk hpk a z.val i z rfl h

private theorem xmss_sign_loop_spec (sk : Array U8 16#usize) (idx : U32) (pk : hash.Seed) (hpk : SeedOk pk)
    (a : address.Adrs) (sig : alloc.vec.Vec U8) (j : U32) (wsig : Spec.Bytes)
    (hidx : idx.val < 2 ^ 9) (hj : j.val ≤ 9)
    (hlen : sig.length = 560 + 16 * j.val)
    (hinv : bytes sig.val = wsig ++ (List.range j.val).flatMap fun j =>
      Spec.xmssNode (bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j (bytes pk.pk_seed.val) (adrsS a)) :
    xmss.xmss_sign_loop sk idx pk a sig j ⦃ r =>
      bytes r.val = wsig ++ (List.range 9).flatMap (fun j =>
        Spec.xmssNode (bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j (bytes pk.pk_seed.val) (adrsS a)) ∧
      r.length = 704 ⦄ := by
  unfold xmss.xmss_sign_loop
  apply loop.spec_decr_nat (measure := fun (p : alloc.vec.Vec U8 × U32) => 9 - p.2.val)
    (inv := fun p => p.2.val ≤ 9 ∧ p.1.length = 560 + 16 * p.2.val ∧
      bytes p.1.val = wsig ++ (List.range p.2.val).flatMap fun j =>
        Spec.xmssNode (bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j (bytes pk.pk_seed.val) (adrsS a))
  · rintro ⟨sig, j⟩ ⟨hj, hlen, hinv⟩
    simp only [xmss.xmss_sign_loop.body]
    simp only at hj hlen hinv
    simp only [step_simps]
    spec_split
    · rename_i hlt
      have hj9 : j.val < 9 := by simp [params.HP] at hlt; scalar_tac
      let* ⟨ i, i_post, i_post1 ⟩ ← U32.ShiftRight_spec
      let* ⟨ k, k_post, k_post1 ⟩ ← UScalar.xor_spec
      have hk : k.val = (idx.val / 2 ^ j.val) ^^^ 1 := by
        rw [k_post]; simp [i_post, Nat.shiftRight_eq_div_pow]
      have hkb : k.val < 2 ^ 9 := by
        rw [hk]
        exact Nat.xor_lt_two_pow (lt_of_le_of_lt (Nat.div_le_self _ _) hidx) (by decide)
      let* ⟨ node, node_post ⟩ ← xmss_node_spec
      · calc (k.val + 1) * 2 ^ j.val ≤ 2 ^ 9 * 2 ^ 8 :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega))
          _ ≤ 2 ^ 32 := by norm_num
      let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ sig1, sig1_post ⟩ ← xmss_extend_u8_spec
      let* ⟨ j1, j1_post ⟩ ← U32.add_spec
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp [alloc.vec.Vec.length, sig1_post, s_post] at hlen ⊢; scalar_tac
      · simp [sig1_post, s_post, hinv, j1_post, List.range_succ, node_post, hk]
    · rename_i hge
      have hj9 : j.val = 9 := by simp [params.HP] at hge; scalar_tac
      simp only [step_simps]
      refine ⟨?_, by scalar_tac⟩
      rw [hinv, hj9]
  · exact ⟨hj, hlen, hinv⟩

@[step]
theorem xmss_sign_spec (m sk : Array U8 16#usize) (idx : U32) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (h : idx.val < 2 ^ 9) :
    xmss.xmss_sign m sk idx pk a ⦃ r =>
      bytes r.val = Spec.xmssSign (bytes m.val) (bytes sk.val) idx.val (bytes pk.pk_seed.val) (adrsS a) ∧
      r.length = 704 ⦄ := by
  unfold xmss.xmss_sign
  let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
  let* ⟨ a2, a2_post ⟩ ← with_keypair_spec
  let* ⟨ sig, sig_post, sig_len ⟩ ← wots_sign_spec
  apply WP.spec_mono
  · exact xmss_sign_loop_spec sk idx pk hpk a sig 0#u32 (bytes sig.val) h
      (by scalar_tac) (by scalar_tac) (by simp)
  · rintro r ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1, sig_post]
    simp [Spec.xmssSign, Spec.hp, a2_post, a1_post1, adrsS, Spec.Adrs.setTypeAndClear,
      Spec.WOTS_HASH, address.WOTS_HASH]

/-- One level of `Spec.climb`. -/
private def climbStep (leaf : Nat) (auth pk : Spec.Bytes) (adrs : Spec.Adrs)
    (st : Spec.Bytes × Nat) (j : Nat) : Spec.Bytes × Nat :=
  if (leaf / 2 ^ j) % 2 = 0 then
    (Spec.H pk { adrs with word2 := j + 1, word3 := st.2 / 2 } (st.1 ++ Spec.block auth j), st.2 / 2)
  else
    (Spec.H pk { adrs with word2 := j + 1, word3 := (st.2 - 1) / 2 } (Spec.block auth j ++ st.1),
      (st.2 - 1) / 2)

private theorem climb_eq (node : Spec.Bytes) (leaf ti : Nat) (auth : Spec.Bytes) (height : Nat)
    (pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.climb node leaf ti auth height pk adrs =
      ((List.range height).foldl (climbStep leaf auth pk adrs) (node, ti)).1 := by
  unfold Spec.climb
  congr 2

private theorem block_drop_take (s : Spec.Bytes) (f h k : Nat) (hk : k < h) :
    Spec.block ((s.drop (f * 16)).take (h * 16)) k = Spec.block s (f + k) := by
  simp only [Spec.block, Spec.n, List.drop_take, List.take_take, List.drop_drop]
  have h1 : min 16 (h * 16 - k * 16) = 16 := by omega
  have h2 : f * 16 + k * 16 = (f + k) * 16 := by ring
  rw [h1, h2]

private theorem climb_loop_spec (auth : Slice U8) (first : Usize) (height : U32)
    (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) (node : Array U8 16#usize) (index k : U32)
    (c leaf : Nat) (N0 : Spec.Bytes) (T0 : Nat)
    (hlen : (first.val + height.val) * 16 ≤ auth.length) (hh : height.val ≤ 31)
    (hk : k.val ≤ height.val)
    (hidx : index.val = c * 2 ^ (height.val - k.val) + leaf / 2 ^ k.val)
    (hinv : (bytes node.val, index.val) = (List.range k.val).foldl
      (climbStep leaf (((bytes auth.val).drop (first.val * 16)).take (height.val * 16))
        (bytes pk.pk_seed.val) (adrsS a)) (N0, T0)) :
    xmss.climb_loop auth first height pk a node index k ⦃ r =>
      bytes r.val = ((List.range height.val).foldl
        (climbStep leaf (((bytes auth.val).drop (first.val * 16)).take (height.val * 16))
          (bytes pk.pk_seed.val) (adrsS a)) (N0, T0)).1 ⦄ := by
  unfold xmss.climb_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Array U8 16#usize × U32 × U32) => height.val - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ height.val ∧
      p.2.1.val = c * 2 ^ (height.val - p.2.2.val) + leaf / 2 ^ p.2.2.val ∧
      (bytes p.1.val, p.2.1.val) = (List.range p.2.2.val).foldl
        (climbStep leaf (((bytes auth.val).drop (first.val * 16)).take (height.val * 16))
          (bytes pk.pk_seed.val) (adrsS a)) (N0, T0))
  · clear hk hidx hinv node index k
    rintro ⟨node, index, k⟩ ⟨hk, hidx, hinv⟩
    simp only [xmss.climb_loop.body]
    simp only at hk hidx hinv
    simp only [step_simps]
    spec_split
    · rename_i hlt
      have hklt : k.val < height.val := by scalar_tac
      let* ⟨ i, i_post ⟩ ← UScalar.cast.step_spec
      have hi : i.val = k.val := by rw [i_post]; scalar_tac
      let* ⟨ i1, i1_post ⟩ ← Usize.add_spec
      let* ⟨ sibling, sibling_post, sibling_post1 ⟩ ← block_spec
      let* ⟨ parent, parent_post, parent_post1 ⟩ ← U32.ShiftRight_IScalar_spec
      let* ⟨ i2, i2_post ⟩ ← U32.add_spec
      let* ⟨ a1, a1_post ⟩ ← with_word2_spec
      let* ⟨ a2, a2_post ⟩ ← with_word3_spec
      let* ⟨ i3, i3_post, i3_post1 ⟩ ← UScalar.and_spec
      have hpar : parent.val = index.val / 2 := by
        rw [parent_post]; simp [Nat.shiftRight_eq_div_pow]
      have hi3 : i3.val = index.val % 2 := by
        rw [i3_post]; simp [Nat.and_one_is_mod]
      have hpow : 2 ^ (height.val - k.val) = 2 * 2 ^ (height.val - (k.val + 1)) := by
        have : height.val - k.val = (height.val - (k.val + 1)) + 1 := by omega
        rw [this, pow_succ]; ring
      have hidx' : index.val = 2 * (c * 2 ^ (height.val - (k.val + 1))) + leaf / 2 ^ k.val := by
        rw [hidx, hpow]; ring
      have hmod : index.val % 2 = (leaf / 2 ^ k.val) % 2 := by
        rw [hidx']; omega
      have hdiv : index.val / 2 = c * 2 ^ (height.val - (k.val + 1)) + leaf / 2 ^ (k.val + 1) := by
        rw [hidx', pow_succ, ← Nat.div_div_eq_div_mul]; omega
      have hsib : bytes sibling.val = Spec.block
          (((bytes auth.val).drop (first.val * 16)).take (height.val * 16)) k.val := by
        rw [sibling_post1, block_drop_take _ _ _ _ hklt, i1_post, hi]
      have hadrs : adrsS a2 = { adrsS a with word2 := k.val + 1, word3 := index.val / 2 } := by
        simp [adrsS, a2_post, a1_post, i2_post, hpar]
      by_cases h3 : i3 = 0#u32
      · simp only [h3, ↓reduceIte]
        have heven : (leaf / 2 ^ k.val) % 2 = 0 := by
          rw [← hmod, ← hi3, h3]; rfl
        let* ⟨ node1, node1_post ⟩ ← hash2_spec
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · rw [i2_post, hpar, hdiv]
        · rw [i2_post, List.range_succ, List.foldl_append, ← hinv]
          simp [climbStep, heven, node1_post, hadrs, hsib, hpar]
      · simp only [h3, ↓reduceIte]
        have hodd : ¬ (leaf / 2 ^ k.val) % 2 = 0 := by
          rw [← hmod, ← hi3]; intro h0; apply h3; scalar_tac
        have hsub : (index.val - 1) / 2 = index.val / 2 := by omega
        let* ⟨ node1, node1_post ⟩ ← hash2_spec
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · rw [i2_post, hpar, hdiv]
        · rw [i2_post, List.range_succ, List.foldl_append, ← hinv]
          simp [climbStep, hodd, node1_post, hadrs, hsib, hpar, hsub]
    · rename_i hge
      have hkh : k.val = height.val := by scalar_tac
      simp only [step_simps]
      have h1 := congrArg Prod.fst hinv
      rw [hkh] at h1
      exact h1
  · exact ⟨hk, hidx, hinv⟩

/-- `idx` is the tree index in the address; `leaf` is the index within the
tree being climbed, which agrees with `idx` on its low `height` bits. -/
@[step]
theorem climb_spec (node : Array U8 16#usize) (idx : U32) (auth : Slice U8) (first : Usize) (height : U32)
    (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) (c leaf : Nat)
    (hlen : (first.val + height.val) * 16 ≤ auth.length) (hh : height.val ≤ 31)
    (hidx : idx.val = c * 2 ^ height.val + leaf) (hleaf : leaf < 2 ^ height.val) :
    xmss.climb node idx auth first height pk a ⦃ r =>
      bytes r.val = Spec.climb (bytes node.val) leaf idx.val
        (((bytes auth.val).drop (first.val * 16)).take (height.val * 16)) height.val
        (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  unfold xmss.climb
  apply WP.spec_mono
  · exact climb_loop_spec auth first height pk hpk a node idx 0#u32 c leaf (bytes node.val) idx.val
      hlen hh (by scalar_tac) (by simpa using hidx) (by simp)
  · intro r h
    rw [climb_eq]; exact h

private theorem block_take (s : Spec.Bytes) (i : Nat) (hi : i < 35) :
    Spec.block (s.take 560) i = Spec.block s i := by
  simp only [Spec.block, Spec.n, List.drop_take, List.take_take]
  have h1 : min 16 (560 - i * 16) = 16 := by omega
  rw [h1]

/-- `wots_pkFromSig` reads only the first `len · n` bytes of its signature argument. -/
private theorem wotsPkFromSig_take (s msg pk : Spec.Bytes) (ad : Spec.Adrs) :
    Spec.wotsPkFromSig (s.take 560) msg pk ad = Spec.wotsPkFromSig s msg pk ad := by
  unfold Spec.wotsPkFromSig
  refine congrArg (Spec.T pk (Spec.wotsPkAdrs ad)) ?_
  apply List.flatMap_congr
  intro i hi
  rw [block_take s i (by simpa [Spec.len] using hi)]

@[step]
theorem xmss_pk_from_sig_spec (idx : U32) (sig : Slice U8) (m : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (h : sig.length = 704) (hidx : idx.val < 2 ^ 9) :
    xmss.xmss_pk_from_sig idx sig m pk a ⦃ r =>
      bytes r.val = Spec.xmssPkFromSig idx.val (bytes sig.val) (bytes m.val) (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  unfold xmss.xmss_pk_from_sig
  let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
  let* ⟨ a2, a2_post ⟩ ← with_keypair_spec
  let* ⟨ node, node_post ⟩ ← wots_pk_from_sig_spec
  let* ⟨ a3, a3_post, a3_post1 ⟩ ← with_type_spec
  apply WP.spec_mono
  · exact climb_spec node idx sig params.LEN params.HP pk hpk a3 0 idx.val
      (by simp [params.LEN, params.HP]; scalar_tac) (by simp [params.HP])
      (by simp) (by simpa [params.HP] using hidx)
  · intro r hr
    rw [hr, node_post, a3_post]
    simp [Spec.xmssPkFromSig, Spec.len, Spec.n, Spec.hp, params.LEN, params.HP,
      wotsPkFromSig_take, a2_post, a1_post1, adrsS, Spec.Adrs.setTypeAndClear,
      Spec.WOTS_HASH, address.WOTS_HASH, Spec.TREE, address.TREE]

end slhdsa
