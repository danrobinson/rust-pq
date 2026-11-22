import Slhdsa.Proofs.Fors
open Aeneas Aeneas.Std Result

/-! The hypertree (FIPS 205 §7), for any valid parameter set. -/

namespace slhdsa

/-- Appending a slice of bytes to a vector of bytes. -/
@[local step]
theorem ht_extend_from_slice_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r =>
      r.val = v.val ++ s.val ∧ r.length = v.length + s.length ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (by intros; simp [liftFun1]))
  intro l hl
  simp [hl]

theorem ht_and_mask_val (x m : U64) (n : Nat) (hm : m.val = 2 ^ n - 1) :
    (x &&& m).val = x.val % 2 ^ n := by
  rw [UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]

/-- Size bound of one XMSS signature. -/
theorem ht_xs_le {N : Usize} (p : params.Params) (hp : PN p N) :
    (2 * N.val + 3 + p.hp.val) * N.val ≤ 2432 := by
  have hn := hp.nok
  have hhp := hp.valid.hp_le
  simp only [paramsS_hp] at hhp
  rcases hn with hn | hn | hn <;> rw [hn] <;> omega

theorem ht_shl_val (i : U64) (hp : U32) (hhp : hp.val ≤ 9)
    (hi : i.val = 1 <<< hp.val % U64.size) : i.val = 2 ^ hp.val := by
  have hpow : 2 ^ hp.val ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp
  rw [hi, Nat.one_shiftLeft]
  apply Nat.mod_eq_of_lt
  simp [U64.size, U64.numBits]; omega

/-- The mask step on the tree index: `leaf = tree & (2^hp - 1)`. -/
theorem ht_leaf_val (tree i1 i2 : U64) (hp : U32) (hhp : hp.val ≤ 9)
    (hi1 : i1.val = 2 ^ hp.val - 1) (hi2 : i2.val = (tree &&& i1).val) :
    (UScalar.cast UScalarTy.U32 i2).val = tree.val % 2 ^ hp.val := by
  have hpow : 2 ^ hp.val ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp
  have h4 : i2.val = tree.val % 2 ^ hp.val := by rw [hi2, ht_and_mask_val _ _ _ hi1]
  have h5 : tree.val % 2 ^ hp.val < 2 ^ hp.val := Nat.mod_lt _ (by positivity)
  rw [UScalar.cast_val_eq, h4]
  simp [UScalarTy.numBits]
  omega

theorem ht_bytes_injective : Function.Injective bytes := by
  apply List.map_injective_iff.mpr
  intro a b h
  exact UScalar.eq_equiv_bv_eq a b |>.mpr h

theorem ht_allM_eq_spec (l1 l2 : List U8) (h : l1.length = l2.length) :
    List.allM (fun (x : U8 × U8) => (ok (decide (x.1.val = x.2.val)) : Result Bool)) (List.zip l1 l2)
      = ok (decide (l1 = l2)) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> first | rfl | simp at h
  | cons x xs ih =>
    cases l2 with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, List.allM]
      by_cases hxy : x = y
      · subst hxy
        simp [ih ys h]
      · have : ¬ x.val = y.val := fun hv => hxy (by scalar_tac)
        simp [hxy, this]
        rfl

@[step]
theorem ht_array_eq_spec {N : Usize} (a b : Array U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b ⦃ r => r = decide (a.val = b.val) ⦄ := by
  unfold core.array.equality.PartialEqArray.eq
  simp
  rw [ht_allM_eq_spec _ _ (by simp)]
  simp

/-- One layer of `Spec.htVerify`. -/
def htVerifyStep (p : Spec.Params) (sig pk : Spec.Bytes) (st : Spec.Bytes × Nat × Nat) (j : Nat) :
    Spec.Bytes × Nat × Nat :=
  (Spec.xmssPkFromSig p st.2.2 ((sig.drop (j * p.xmssSigBytes)).take p.xmssSigBytes) st.1 pk
      { Spec.Adrs.zero with layer := j, tree := st.2.1 },
    st.2.1 >>> p.hp, st.2.1 % 2 ^ p.hp)

theorem htVerify_eq (p : Spec.Params) (m sig pk : Spec.Bytes) (t l : Nat) (root : Spec.Bytes) :
    Spec.htVerify p m sig pk t l root =
      (((List.range p.d).foldl (htVerifyStep p sig pk) (m, t, l)).1 == root) := by
  rfl

theorem ht_verify_loop_spec {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (seed : hash.Seed N) (hs : SeedOk seed) (xs : Usize) (m0 : Spec.Bytes)
    (node : Array U8 N) (tree : U64) (leaf : U32) (j : U32) (t0 l0 : Nat)
    (hxs : xs.val = (2 * N.val + 3 + p.hp.val) * N.val)
    (hxs' : xs.val = (paramsS p).xmssSigBytes)
    (h : sig.length = p.d.val * xs.val) (hj : j.val ≤ p.d.val) (hl : leaf.val < 2 ^ p.hp.val)
    (hinv : (bytes node.val, tree.val, leaf.val) =
      (List.range j.val).foldl (htVerifyStep (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val))
        (m0, t0, l0)) :
    ht.ht_verify_loop p sig seed xs node tree leaf j ⦃ r =>
      ∃ t l, (bytes r.val, t, l) =
        (List.range p.d.val).foldl (htVerifyStep (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val))
          (m0, t0, l0) ⦄ := by
  have hv := hp.valid
  have hd : p.d.val ≤ 22 := by simpa using hv.d_le
  have hhp : p.hp.val ≤ 9 := by simpa using hv.hp_le
  have hxsb : xs.val ≤ 2432 := by rw [hxs]; exact ht_xs_le p hp
  unfold ht.ht_verify_loop
  apply loop.spec_decr_nat
    (measure := fun (q : Array U8 N × U64 × U32 × U32) => p.d.val - q.2.2.2.val)
    (inv := fun q => q.2.2.2.val ≤ p.d.val ∧ q.2.2.1.val < 2 ^ p.hp.val ∧
      (bytes q.1.val, q.2.1.val, q.2.2.1.val) =
        (List.range q.2.2.2.val).foldl (htVerifyStep (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val))
          (m0, t0, l0))
  · rintro ⟨node, tree, leaf, j⟩ ⟨hj, hl, hinv⟩
    simp only [ht.ht_verify_loop.body]
    simp only at hj hl hinv
    by_cases hjd : j < p.d
    · simp only [hjd, ite_true]
      have hjd' : j.val < p.d.val := by scalar_tac
      have hb1 : j.val * xs.val ≤ 22 * 2432 := Nat.mul_le_mul (by omega) hxsb
      have hb2 : j.val * xs.val + xs.val ≤ p.d.val * xs.val := by
        have : (j.val + 1) * xs.val ≤ p.d.val * xs.val := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul] at this; omega
      step
      step
      step
      step
      step
      step
      step
      have hsl : s.length = (2 * N.val + 3 + p.hp.val) * N.val := by
        rw [s_post1, i1_post, ← hxs]; omega
      step with xmss_pk_from_sig_spec p hp leaf s node seed hs adrs hsl hl as ⟨node1, node1_post⟩
      have hlt : p.hp.val < 64 := by omega
      step as ⟨i2, i2_post, i2_bv⟩
      have h2 : i2.val = 2 ^ p.hp.val := ht_shl_val i2 p.hp hhp i2_post
      have hpos : 0 < 2 ^ p.hp.val := by positivity
      step as ⟨i3, i3_post⟩
      step as ⟨i4, i4_post⟩
      step as ⟨leaf1, leaf1_post⟩
      step as ⟨tree1, tree1_post, tree1_bv⟩
      step as ⟨j1, j1_post⟩
      have h5 : leaf1.val = tree.val % 2 ^ p.hp.val := by
        rw [leaf1_post]
        exact ht_leaf_val tree i3 i4 p.hp hhp (by omega) i4_post
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [h5]; exact Nat.mod_lt _ (by positivity)
      · rw [j1_post, List.range_succ, List.foldl_append, ← hinv]
        simp only [List.foldl_cons, List.foldl_nil, htVerifyStep]
        have hs' : bytes s.val = List.take (paramsS p).xmssSigBytes
            (List.drop (j.val * (paramsS p).xmssSigBytes) (bytes sig.val)) := by
          rw [s_post, ← hxs']
          simp [List.slice, i1_post, off_post, i_post]
        have ha : adrsS adrs = { Spec.Adrs.zero with layer := j.val, tree := tree.val } := by
          simp [adrsS, adrs_post, a1_post, a_post, Spec.Adrs.zero]
        simp only [paramsS_hp]
        rw [node1_post, hs', ha, h5, tree1_post]
    · simp only [hjd, ite_false]
      have : j.val = p.d.val := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨_, _, by rw [← this]; exact hinv⟩
  · exact ⟨hj, hl, hinv⟩

@[step]
theorem ht_verify_spec {N : Usize} (p : params.Params) (hp : PN p N) (m : Array U8 N) (sig : Slice U8)
    (seed : hash.Seed N) (hs : SeedOk seed) (idx_tree : U64) (idx_leaf : U32) (pk_root : Array U8 N)
    (h : sig.length = p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val))
    (hl : idx_leaf.val < 2 ^ p.hp.val) :
    ht.ht_verify p m sig seed idx_tree idx_leaf pk_root ⦃ b =>
      b = Spec.htVerify (paramsS p) (bytes m.val) (bytes sig.val) (bytes seed.pk_seed.val) idx_tree.val
        idx_leaf.val (bytes pk_root.val) ⦄ := by
  have hv := hp.valid
  unfold ht.ht_verify
  let* ⟨xs, hxs, hxs'⟩ ← xmss_sig_bytes_spec p hv
  have hxs2 : xs.val = (2 * N.val + 3 + p.hp.val) * N.val := by rw [hxs, hp.n_eq]
  let* ⟨node1, t, l, hnode1⟩ ← ht_verify_loop_spec p hp sig seed hs xs (bytes m.val) m idx_tree idx_leaf
    0#u32 idx_tree.val idx_leaf.val hxs2 hxs' (by rw [h, hxs2]) (by simp) hl (by simp)
  step*
  rw [htVerify_eq]
  simp only [paramsS_d]
  rw [← hnode1, b_post]
  by_cases hn : node1.val = pk_root.val
  · simp [hn]
  · have : bytes node1.val ≠ bytes pk_root.val := fun hb => hn (ht_bytes_injective hb)
    simp [hn, this]

/-- One layer of `Spec.htSign`. -/
def htSignStep (p : Spec.Params) (sk pk : Spec.Bytes) (st : Spec.Bytes × Spec.Bytes × Nat × Nat)
    (j : Nat) : Spec.Bytes × Spec.Bytes × Nat × Nat :=
  (st.1 ++ Spec.xmssSign p st.2.1 sk st.2.2.2 pk { Spec.Adrs.zero with layer := j, tree := st.2.2.1 },
    Spec.xmssPkFromSig p st.2.2.2
      (Spec.xmssSign p st.2.1 sk st.2.2.2 pk { Spec.Adrs.zero with layer := j, tree := st.2.2.1 })
      st.2.1 pk { Spec.Adrs.zero with layer := j, tree := st.2.2.1 },
    st.2.2.1 >>> p.hp, st.2.2.1 % 2 ^ p.hp)

theorem htSign_eq (p : Spec.Params) (m sk pk : Spec.Bytes) (t l : Nat) :
    Spec.htSign p m sk pk t l = ((List.range p.d).foldl (htSignStep p sk pk) ([], m, t, l)).1 := by
  rfl

theorem ht_sign_loop_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (m0 : Spec.Bytes)
    (sig : alloc.vec.Vec U8) (root : Array U8 N) (tree : U64) (leaf : U32) (j : U32) (t0 l0 : Nat)
    (hj : j.val ≤ p.d.val) (hl : leaf.val < 2 ^ p.hp.val)
    (hlen : sig.length = (2 * N.val + 3 + p.hp.val) * N.val * j.val)
    (hinv : (bytes sig.val, bytes root.val, tree.val, leaf.val) =
      (List.range j.val).foldl (htSignStep (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val))
        ([], m0, t0, l0)) :
    ht.ht_sign_loop p sk seed sig root tree leaf j ⦃ r =>
      r.length = p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) ∧ bytes r.val =
        ((List.range p.d.val).foldl (htSignStep (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val))
          ([], m0, t0, l0)).1 ⦄ := by
  have hv := hp.valid
  have hd : p.d.val ≤ 22 := by simpa using hv.d_le
  have hhp : p.hp.val ≤ 9 := by simpa using hv.hp_le
  have hxsb := ht_xs_le p hp
  generalize hX : (2 * N.val + 3 + p.hp.val) * N.val = X at *
  unfold ht.ht_sign_loop
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × Array U8 N × U64 × U32 × U32) =>
      p.d.val - q.2.2.2.2.val)
    (inv := fun q => q.2.2.2.2.val ≤ p.d.val ∧ q.2.2.2.1.val < 2 ^ p.hp.val ∧
      q.1.length = X * q.2.2.2.2.val ∧
      (bytes q.1.val, bytes q.2.1.val, q.2.2.1.val, q.2.2.2.1.val) =
        (List.range q.2.2.2.2.val).foldl (htSignStep (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val))
          ([], m0, t0, l0))
  · rintro ⟨sig, root, tree, leaf, j⟩ ⟨hj, hl, hlen, hinv⟩
    simp only [ht.ht_sign_loop.body]
    simp only at hj hl hlen hinv
    by_cases hjd : j < p.d
    · simp only [hjd, ite_true]
      have hjd' : j.val < p.d.val := by scalar_tac
      have hb1 : X * j.val ≤ 2432 * 22 := Nat.mul_le_mul hxsb (by omega)
      step
      step
      step
      step with xmss_sign_spec p hp root sk leaf seed hs adrs hl as ⟨s1, s1_post, s1_len⟩
      rw [hX] at s1_len
      step with xmss_pk_from_sig_spec p hp leaf (alloc.vec.Vec.deref s1) root seed hs
        adrs (by simp [s1_len, hX]) hl as ⟨root1, root1_post⟩
      step with ht_extend_from_slice_spec sig (alloc.vec.Vec.deref s1) (by simp; scalar_tac)
        as ⟨sig1, sig1_post, sig1_len⟩
      have hlt : p.hp.val < 64 := by omega
      step as ⟨i, i_post, i_bv⟩
      have h2 : i.val = 2 ^ p.hp.val := ht_shl_val i p.hp hhp i_post
      have hpos : 0 < 2 ^ p.hp.val := by positivity
      step as ⟨i1, i1_post⟩
      step as ⟨i2, i2_post⟩
      step as ⟨leaf1, leaf1_post⟩
      step as ⟨tree1, tree1_post, tree1_bv⟩
      step as ⟨j1, j1_post⟩
      have h5 : leaf1.val = tree.val % 2 ^ p.hp.val := by
        rw [leaf1_post]
        exact ht_leaf_val tree i1 i2 p.hp hhp (by omega) i2_post
      have ha : adrsS adrs = { Spec.Adrs.zero with layer := j.val, tree := tree.val } := by
        simp [adrsS, adrs_post, a1_post, a_post, Spec.Adrs.zero]
      refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · rw [h5]; exact Nat.mod_lt _ hpos
      · simp only [sig1_len, vec_deref_length, hlen, s1_len, j1_post]; ring
      · rw [j1_post, List.range_succ, List.foldl_append, ← hinv]
        simp only [List.foldl_cons, List.foldl_nil, htSignStep, paramsS_hp]
        rw [sig1_post, root1_post, bytes_append, vec_deref_val, s1_post,
          ha, h5, tree1_post]
    · simp only [hjd, ite_false]
      have : j.val = p.d.val := by scalar_tac
      simp only [WP.spec_ok]
      subst hX
      refine ⟨?_, by rw [← this]; rw [← hinv]⟩
      rw [hlen, this, Nat.mul_comm]
  · exact ⟨hj, hl, hlen, hinv⟩

@[step]
theorem ht_sign_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (idx_tree : U64) (idx_leaf : U32)
    (hl : idx_leaf.val < 2 ^ p.hp.val) :
    ht.ht_sign p m sk seed idx_tree idx_leaf ⦃ r =>
      bytes r.val = Spec.htSign (paramsS p) (bytes m.val) (bytes sk.val) (bytes seed.pk_seed.val)
        idx_tree.val idx_leaf.val ∧
      r.length = p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) ⦄ := by
  unfold ht.ht_sign
  apply WP.spec_mono
  · exact ht_sign_loop_spec p hp sk seed hs (bytes m.val) (alloc.vec.Vec.new U8) m idx_tree idx_leaf 0#u32
      idx_tree.val idx_leaf.val (by simp) hl (by simp) (by simp)
  · intro r ⟨h1, h2⟩
    exact ⟨by rw [htSign_eq]; exact h2, h1⟩

end slhdsa
