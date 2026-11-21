import Slhdsa.Proofs.Xmss
open Aeneas Aeneas.Std Result

/-! The hypertree. -/

namespace slhdsa

@[local simp, local scalar_tac_simps] theorem ht_D_eq : params.D = 7#u32 := by simp [global_simps]
@[local simp, local scalar_tac_simps] theorem ht_HP_eq : params.HP = 9#u32 := by simp [global_simps]
@[local simp, local scalar_tac_simps] theorem ht_XMSS_SIG_BYTES_eq : params.XMSS_SIG_BYTES = 704#usize := by
  simp [global_simps]

/-- One layer of `Spec.htVerify`. -/
def htVerifyStep (sig pk : Spec.Bytes) (st : Spec.Bytes × Nat × Nat) (j : Nat) :
    Spec.Bytes × Nat × Nat :=
  (Spec.xmssPkFromSig st.2.2 ((sig.drop (j * Spec.xmssSigBytes)).take Spec.xmssSigBytes) st.1 pk
      { Spec.Adrs.zero with layer := j, tree := st.2.1 },
    st.2.1 >>> Spec.hp, st.2.1 % 2 ^ Spec.hp)

theorem ht_verify_loop_spec (sig : Slice U8) (pk : Array U8 16#usize) (m : Array U8 16#usize)
    (node : Array U8 16#usize) (tree : U64) (leaf : U32) (j : U32) (t0 l0 : Nat)
    (h : sig.length = 4928) (hj : j.val ≤ 7) (hl : leaf.val < 2 ^ 9)
    (hinv : (bytes node.val, tree.val, leaf.val) =
      (List.range j.val).foldl (htVerifyStep (bytes sig.val) (bytes pk.val)) (bytes m.val, t0, l0)) :
    ht.ht_verify_loop sig pk node tree leaf j ⦃ r =>
      ∃ t l, (bytes r.val, t, l) =
        (List.range 7).foldl (htVerifyStep (bytes sig.val) (bytes pk.val)) (bytes m.val, t0, l0) ⦄ := by
  unfold ht.ht_verify_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Array U8 16#usize × U64 × U32 × U32) => 7 - p.2.2.2.val)
    (inv := fun p => p.2.2.2.val ≤ 7 ∧ p.2.2.1.val < 2 ^ 9 ∧
      (bytes p.1.val, p.2.1.val, p.2.2.1.val) =
        (List.range p.2.2.2.val).foldl (htVerifyStep (bytes sig.val) (bytes pk.val)) (bytes m.val, t0, l0))
  · rintro ⟨node, tree, leaf, j⟩ ⟨hj, hl, hinv⟩
    simp only [ht.ht_verify_loop.body]
    simp only at hj hl hinv
    step*
    have h2 : i2.val = 512 := by simp [i2_post, U64.size, U64.numBits]
    have h3 : i3.val = 511 := by scalar_tac
    have h4 : i4.val = tree.val % 2 ^ 9 := by
      rw [i4_post, UScalar.val_and, h3]
      exact Nat.and_two_pow_sub_one_eq_mod _ 9
    have h5 : leaf1.val = tree.val % 2 ^ 9 := by
      rw [leaf1_post, UScalar.cast_val_eq, h4]
      simp [UScalarTy.numBits]
      omega
    refine ⟨by scalar_tac, by omega, ?_, by scalar_tac⟩
    rw [j1_post, List.range_succ, List.foldl_append, ← hinv]
    simp only [List.foldl_cons, List.foldl_nil, htVerifyStep]
    have hs : bytes s.val =
        List.take Spec.xmssSigBytes (List.drop (j.val * Spec.xmssSigBytes) (bytes sig.val)) := by
      rw [s_post]
      simp [List.slice, Spec.xmssSigBytes, Spec.len, Spec.hp, Spec.n, i1_post, off_post, i_post]
    have ha : adrsS adrs = { Spec.Adrs.zero with layer := j.val, tree := tree.val } := by
      simp [adrsS, adrs_post, a1_post, a_post, Spec.Adrs.zero]
    rw [node1_post, hs, ha, h5, tree1_post]
    simp [Spec.hp]
  · exact ⟨hj, hl, hinv⟩

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
theorem ht_array_eq_spec (a b : Array U8 16#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b ⦃ r => r = decide (a.val = b.val) ⦄ := by
  unfold core.array.equality.PartialEqArray.eq
  simp
  rw [ht_allM_eq_spec _ _ (by simp)]
  simp

theorem htVerify_eq (m sig pk : Spec.Bytes) (t l : Nat) (root : Spec.Bytes) :
    Spec.htVerify m sig pk t l root =
      (((List.range 7).foldl (htVerifyStep sig pk) (m, t, l)).1 == root) := by
  rfl

@[step]
theorem ht_verify_spec (m : Array U8 16#usize) (sig : Slice U8) (pk : Array U8 16#usize) (idx_tree : U64) (idx_leaf : U32)
    (pk_root : Array U8 16#usize) (h : sig.length = 4928) (hl : idx_leaf.val < 2 ^ 9) :
    ht.ht_verify m sig pk idx_tree idx_leaf pk_root ⦃ b =>
      b = Spec.htVerify (bytes m.val) (bytes sig.val) (bytes pk.val) idx_tree.val idx_leaf.val
        (bytes pk_root.val) ⦄ := by
  unfold ht.ht_verify
  step with ht_verify_loop_spec sig pk m m idx_tree idx_leaf 0#u32 idx_tree.val idx_leaf.val h (by simp) hl (by simp) as ⟨node, t, l, hnode⟩
  step*
  rw [htVerify_eq, ← hnode, b_post]
  by_cases hn : node.val = pk_root.val
  · simp [hn]
  · have : bytes node.val ≠ bytes pk_root.val := fun hb => hn (ht_bytes_injective hb)
    simp [hn, this]

@[local step]
theorem ht_extend_from_slice_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (l := s.val) (by intros; simp [liftFun1]))
  intro l' hl'
  simp [hl']

/-- One layer of `Spec.htSign`. -/
def htSignStep (sk pk : Spec.Bytes) (st : Spec.Bytes × Spec.Bytes × Nat × Nat) (j : Nat) :
    Spec.Bytes × Spec.Bytes × Nat × Nat :=
  (st.1 ++ Spec.xmssSign st.2.1 sk st.2.2.2 pk { Spec.Adrs.zero with layer := j, tree := st.2.2.1 },
    Spec.xmssPkFromSig st.2.2.2
      (Spec.xmssSign st.2.1 sk st.2.2.2 pk { Spec.Adrs.zero with layer := j, tree := st.2.2.1 })
      st.2.1 pk { Spec.Adrs.zero with layer := j, tree := st.2.2.1 },
    st.2.2.1 >>> Spec.hp, st.2.2.1 % 2 ^ Spec.hp)

theorem htSign_eq (m sk pk : Spec.Bytes) (t l : Nat) :
    Spec.htSign m sk pk t l = ((List.range 7).foldl (htSignStep sk pk) ([], m, t, l)).1 := by
  rfl

theorem ht_sign_loop_spec (sk pk m : Array U8 16#usize) (sig : alloc.vec.Vec U8)
    (root : Array U8 16#usize) (tree : U64) (leaf : U32) (j : U32) (t0 l0 : Nat)
    (hj : j.val ≤ 7) (hl : leaf.val < 2 ^ 9) (hlen : sig.length = 704 * j.val)
    (hinv : (bytes sig.val, bytes root.val, tree.val, leaf.val) =
      (List.range j.val).foldl (htSignStep (bytes sk.val) (bytes pk.val)) ([], bytes m.val, t0, l0)) :
    ht.ht_sign_loop sk pk sig root tree leaf j ⦃ r =>
      r.length = 4928 ∧ bytes r.val =
        ((List.range 7).foldl (htSignStep (bytes sk.val) (bytes pk.val)) ([], bytes m.val, t0, l0)).1 ⦄ := by
  unfold ht.ht_sign_loop
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec U8 × Array U8 16#usize × U64 × U32 × U32) => 7 - p.2.2.2.2.val)
    (inv := fun p => p.2.2.2.2.val ≤ 7 ∧ p.2.2.2.1.val < 2 ^ 9 ∧ p.1.length = 704 * p.2.2.2.2.val ∧
      (bytes p.1.val, bytes p.2.1.val, p.2.2.1.val, p.2.2.2.1.val) =
        (List.range p.2.2.2.2.val).foldl (htSignStep (bytes sk.val) (bytes pk.val)) ([], bytes m.val, t0, l0))
  · rintro ⟨sig, root, tree, leaf, j⟩ ⟨hj, hl, hlen, hinv⟩
    simp only [ht.ht_sign_loop.body]
    simp only at hj hl hlen hinv
    step*
    · have h2 : i.val = 512 := by simp [i_post, U64.size, U64.numBits]
      have h3 : i1.val = 511 := by scalar_tac
      have h4 : i2.val = tree.val % 2 ^ 9 := by
        rw [i2_post, UScalar.val_and, h3]
        exact Nat.and_two_pow_sub_one_eq_mod _ 9
      have h5 : leaf1.val = tree.val % 2 ^ 9 := by
        rw [leaf1_post, UScalar.cast_val_eq, h4]
        simp [UScalarTy.numBits]
        omega
      have ha : adrsS adrs = { Spec.Adrs.zero with layer := j.val, tree := tree.val } := by
        simp [adrsS, adrs_post, a1_post, a_post, Spec.Adrs.zero]
      have hd : s.deref.val = s.val := by simp [alloc.vec.Vec.deref]
      refine ⟨by scalar_tac, by omega, ?_, ?_, by scalar_tac⟩
      · simp [sig1_post, hd, hlen, s_post1, j1_post]; ring
      · rw [j1_post, List.range_succ, List.foldl_append, ← hinv]
        simp only [List.foldl_cons, List.foldl_nil, htSignStep]
        rw [sig1_post, root1_post, hd, bytes_append, s_post, ha, h5, tree1_post]
        simp [Spec.hp]
  · exact ⟨hj, hl, hlen, hinv⟩

@[step]
theorem ht_sign_spec (m sk pk : Array U8 16#usize) (idx_tree : U64) (idx_leaf : U32) (hl : idx_leaf.val < 2 ^ 9) :
    ht.ht_sign m sk pk idx_tree idx_leaf ⦃ r =>
      bytes r.val = Spec.htSign (bytes m.val) (bytes sk.val) (bytes pk.val) idx_tree.val idx_leaf.val ∧
      r.length = 4928 ⦄ := by
  unfold ht.ht_sign
  apply WP.spec_mono
  · exact ht_sign_loop_spec sk pk m (alloc.vec.Vec.new U8) m idx_tree idx_leaf 0#u32
      idx_tree.val idx_leaf.val (by simp) hl (by simp) (by simp)
  · intro r ⟨h1, h2⟩
    exact ⟨by rw [htSign_eq]; exact h2, h1⟩

end slhdsa
