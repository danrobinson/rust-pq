import Slhdsa.Proofs.Slh
import Spec.Checked
open Aeneas Aeneas.Std Result

/-! The checked signer: `fors_pk_gen`, `ht_sign_checked`,
`slh_sign_internal_checked` and `slh_sign_checked` compute the functions of
`Spec/Checked.lean`. -/

namespace slhdsa

@[local simp, local scalar_tac_simps] theorem chk_A_eq : params.A = 12#u32 := by simp [global_simps]
@[local simp, local scalar_tac_simps] theorem chk_K_eq : params.K = 14#u32 := by simp [global_simps]
@[local simp, local scalar_tac_simps] theorem chk_D_eq : params.D = 7#u32 := by simp [global_simps]
@[local simp, local scalar_tac_simps] theorem chk_HP_eq : params.HP = 9#u32 := by simp [global_simps]
@[local simp] theorem chk_FORS_ROOTS_eq : address.FORS_ROOTS = 4#u32 := by simp [global_simps]

@[local step]
theorem chk_extend_from_slice_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (l := s.val) (by intros; simp [liftFun1]))
  intro l' hl'
  simp [hl']

/-! ## `fors_pk_gen` -/

theorem fors_pk_gen_loop_spec (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk)
    (a : address.Adrs) (roots : alloc.vec.Vec U8) (i : U32) (hi : i.val ≤ 14)
    (hlen : roots.length = 16 * i.val)
    (hinv : bytes roots.val = (List.range i.val).flatMap
      (fun t => Spec.forsNode (bytes sk.val) t 12 (bytes pk.pk_seed.val) (adrsS a))) :
    fors.fors_pk_gen_loop sk pk a roots i ⦃ r =>
      bytes r.val = (List.range 14).flatMap
        (fun t => Spec.forsNode (bytes sk.val) t 12 (bytes pk.pk_seed.val) (adrsS a)) ∧
      r.length = 224 ⦄ := by
  unfold fors.fors_pk_gen_loop
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec U8 × U32) => 14 - p.2.val)
    (inv := fun p => p.2.val ≤ 14 ∧ p.1.length = 16 * p.2.val ∧
      bytes p.1.val = (List.range p.2.val).flatMap
        (fun t => Spec.forsNode (bytes sk.val) t 12 (bytes pk.pk_seed.val) (adrsS a)))
  · rintro ⟨roots, i⟩ ⟨hi, hlen, hinv⟩
    simp only [fors.fors_pk_gen_loop.body]
    simp only at hi hlen hinv
    split
    · rename_i hlt
      have hlt' : i.val < 14 := by scalar_tac
      step with fors_node_spec sk i params.A pk hpk a (by simp; omega) as ⟨root, root_post⟩
      step*
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp [alloc.vec.Vec.length, roots1_post, s_post] at hlen ⊢; scalar_tac
      · rw [roots1_post, s_post, Array.val_to_slice, bytes_append, hinv, root_post, i1_post,
          List.range_succ, List.flatMap_append]
        simp
    · have h14 : i.val = 14 := by scalar_tac
      simp only [step_simps]
      rw [h14] at hinv hlen
      exact ⟨hinv, hlen⟩
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem fors_pk_gen_spec (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk)
    (a : address.Adrs) :
    fors.fors_pk_gen sk pk a ⦃ r =>
      bytes r.val = Spec.forsPkGen (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  unfold fors.fors_pk_gen
  let* ⟨ roots, roots_post, roots_len ⟩ ← fors_pk_gen_loop_spec sk pk hpk a (alloc.vec.Vec.new U8)
    0#u32 (by simp) (by simp) (by simp)
  step as ⟨a0, a0_post, a0_eq⟩
  step as ⟨a1, a1_post⟩
  step with thash_spec pk hpk a1 roots.deref (by simp [alloc.vec.Vec.deref]; scalar_tac) as ⟨r, r_post⟩
  have hd : roots.deref.val = roots.val := by simp [alloc.vec.Vec.deref]
  rw [r_post, hd, roots_post]
  simp [Spec.forsPkGen, Spec.T, Spec.k, Spec.a, adrsS, a1_post, a0_eq, Spec.Adrs.setTypeAndClear,
    Spec.FORS_ROOTS]

/-! ## `ht_sign_checked` -/

theorem bytes_beq (x y : Array U8 16#usize) : (bytes x.val == bytes y.val) = decide (x.val = y.val) := by
  by_cases h : x.val = y.val
  · simp [h]
  · have : bytes x.val ≠ bytes y.val := fun hb => h (ht_bytes_injective hb)
    simp [h, this]

theorem ht_sign_checked_loop_spec (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk)
    (root : Array U8 16#usize) (sig : alloc.vec.Vec U8) (msgA msgB : Array U8 16#usize) (ok1 : Bool)
    (tree : U64) (leaf : U32) (j : U32) (C0 : Spec.Bytes × Spec.Bytes × Spec.Bytes × Bool × Nat × Nat)
    (hj : j.val ≤ 7) (hl : leaf.val < 2 ^ 9) (hlen : sig.length = 704 * j.val)
    (hinv : (bytes sig.val, bytes msgA.val, bytes msgB.val, ok1, tree.val, leaf.val) =
      (List.range j.val).foldl (Spec.htCheckedStep (bytes sk.val) (bytes pk.pk_seed.val) (bytes root.val)) C0) :
    ht.ht_sign_checked_loop sk pk root sig msgA msgB ok1 tree leaf j ⦃ r =>
      r.1.length = 4928 ∧ (bytes r.1.val, r.2) =
        (((List.range 7).foldl (Spec.htCheckedStep (bytes sk.val) (bytes pk.pk_seed.val) (bytes root.val)) C0).1,
         ((List.range 7).foldl (Spec.htCheckedStep (bytes sk.val) (bytes pk.pk_seed.val) (bytes root.val)) C0).2.2.2.1) ⦄ := by
  unfold ht.ht_sign_checked_loop
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec U8 × Array U8 16#usize × Array U8 16#usize × Bool × U64 × U32 × U32) =>
      7 - p.2.2.2.2.2.2.val)
    (inv := fun p => p.2.2.2.2.2.2.val ≤ 7 ∧ p.2.2.2.2.2.1.val < 2 ^ 9 ∧ p.1.length = 704 * p.2.2.2.2.2.2.val ∧
      (bytes p.1.val, bytes p.2.1.val, bytes p.2.2.1.val, p.2.2.2.1, p.2.2.2.2.1.val, p.2.2.2.2.2.1.val) =
        (List.range p.2.2.2.2.2.2.val).foldl
          (Spec.htCheckedStep (bytes sk.val) (bytes pk.pk_seed.val) (bytes root.val)) C0)
  · rintro ⟨sig, msgA, msgB, ok1, tree, leaf, j⟩ ⟨hj, hl, hlen, hinv⟩
    simp only [ht.ht_sign_checked_loop.body]
    simp only at hj hl hlen hinv
    split
    · rename_i hlt
      have hlt' : j.val < 7 := by scalar_tac
      step*
      have hrb : (if i < params.D then xmss.xmss_node sk 0#u32 params.HP pk adrs else ok root) ⦃ rb =>
          bytes rb.val = if j.val + 1 < 7 then
            Spec.xmssNode (bytes sk.val) 0 9 (bytes pk.pk_seed.val) (adrsS adrs) else bytes root.val ⦄ := by
        split
        · rename_i hi
          have : j.val + 1 < 7 := by scalar_tac
          simp only [this, ↓reduceIte]
          apply WP.spec_mono (xmss_node_spec sk 0#u32 params.HP pk hpk adrs (by simp))
          intro r hr
          rw [hr]
          simp
        · rename_i hi
          have : ¬ j.val + 1 < 7 := by scalar_tac
          simp [this]
      step with hrb as ⟨root_b, root_b_post⟩
      step as ⟨b, b_post⟩
      have hok : (if b = true then ok ok1 else ok false : Result Bool) = ok (ok1 && b) := by
        cases b <;> simp
      rw [hok]
      step*
      have h2 : i1.val = 512 := by simp [i1_post, U64.size, U64.numBits]
      have h3 : i2.val = 511 := by scalar_tac
      have h4 : i3.val = tree.val % 2 ^ 9 := by
        rw [i3_post, UScalar.val_and, h3]
        exact Nat.and_two_pow_sub_one_eq_mod _ 9
      have h5 : leaf1.val = tree.val % 2 ^ 9 := by
        rw [leaf1_post, UScalar.cast_val_eq, h4]
        simp [UScalarTy.numBits]
        omega
      have ha : adrsS adrs = { Spec.Adrs.zero with layer := j.val, tree := tree.val } := by
        simp [adrsS, adrs_post, a1_post, a_post, Spec.Adrs.zero]
      have hd : s.deref.val = s.val := by simp [alloc.vec.Vec.deref]
      refine ⟨by scalar_tac, by omega, ?_, ?_, by scalar_tac⟩
      · simp [alloc.vec.Vec.length, sig1_post, hd, hlen, s_post1, i_post] at hlen ⊢
        ring
      · rw [i_post, List.range_succ, List.foldl_append, ← hinv]
        simp only [List.foldl_cons, List.foldl_nil, Spec.htCheckedStep]
        rw [b_post, ← bytes_beq]
        simp only [sig1_post, hd, bytes_append, s_post, root_a_post, root_b_post, ha, h5, tree1_post]
        simp [Spec.hp, Spec.d]
        exact ⟨rfl, rfl⟩
    · have h7 : j.val = 7 := by scalar_tac
      simp only [step_simps]
      rw [h7] at hinv hlen
      rw [← hinv]
      exact ⟨by scalar_tac, rfl, rfl⟩
  · exact ⟨hj, hl, hlen, hinv⟩

theorem htSignChecked_eq (mA mB sk p : Spec.Bytes) (t l : Nat) (root : Spec.Bytes) :
    Spec.htSignChecked mA mB sk p t l root =
      (((List.range Spec.d).foldl (Spec.htCheckedStep sk p root) ([], mA, mB, mA == mB, t, l)).1,
       ((List.range Spec.d).foldl (Spec.htCheckedStep sk p root) ([], mA, mB, mA == mB, t, l)).2.2.2.1) := by
  unfold Spec.htSignChecked
  generalize List.foldl _ _ _ = C
  obtain ⟨_, _, _, _, _, _⟩ := C
  rfl

@[step]
theorem ht_sign_checked_spec (mA mB sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk)
    (idx_tree : U64) (idx_leaf : U32) (root : Array U8 16#usize) (hl : idx_leaf.val < 2 ^ 9) :
    ht.ht_sign_checked mA mB sk pk idx_tree idx_leaf root ⦃ r =>
      (bytes r.1.val, r.2) = Spec.htSignChecked (bytes mA.val) (bytes mB.val) (bytes sk.val)
        (bytes pk.pk_seed.val) idx_tree.val idx_leaf.val (bytes root.val) ∧ r.1.length = 4928 ⦄ := by
  unfold ht.ht_sign_checked
  step as ⟨b, b_post⟩
  have hok : (if b = true then ok true else ok false : Result Bool) = ok b := by cases b <;> rfl
  rw [hok]
  step with ht_sign_checked_loop_spec sk pk hpk root (alloc.vec.Vec.new U8) mA mB b idx_tree idx_leaf 0#u32
      ([], bytes mA.val, bytes mB.val, bytes mA.val == bytes mB.val, idx_tree.val, idx_leaf.val)
      (by simp) hl (by simp) (by simp [b_post, bytes_beq]) as ⟨r, h1, h2, h3⟩
  refine ⟨?_, h1⟩
  rw [h2, h3, htSignChecked_eq]
  rfl

/-! ## `slh_sign_internal_checked` and `slh_sign_checked` -/

@[step]
theorem slh_sign_internal_checked_spec (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 152) :
    slh.slh_sign_internal_checked m sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSignInternalChecked (bytes m.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold slh.slh_sign_internal_checked
  simp only [global_simps]
  step*
  · simp only [Room] at *; omega
  · simp [alloc.vec.Vec.length, alloc.vec.Vec.deref, sig_post, s8_post] at *; scalar_tac
  · simp [alloc.vec.Vec.length, alloc.vec.Vec.deref, sig1_post, sig_post, s8_post] at *; scalar_tac
  all_goals
    have hseed : seed.pk_seed = pk_seed := by assumption
    simp only [hseed] at *
    have hadrs : adrsS adrs = { { Spec.Adrs.zero with tree := idx_tree.val }.setTypeAndClear
        Spec.FORS_TREE with keypair := idx_leaf.val } := by
      simp [adrsS, adrs_post, a2_post1, a1_post, a_post, Spec.Adrs.setTypeAndClear,
        Spec.Adrs.zero, Spec.FORS_TREE]
    have hmd : bytes s6.val = (bytes digest.val).take Spec.mdBytes := by
      simp [s6_post, List.slice, Spec.mdBytes, Spec.k, Spec.a]
    have hdf : (alloc.vec.Vec.deref sig_fors).val = sig_fors.val := by simp [alloc.vec.Vec.deref]
    subst s_post s1_post s2_post s3_post s4_post s5_post
    simp only [Array.val_to_slice, hdf] at *
    simp only [Spec.slhSignInternalChecked]
    rw [← sk_seed_post1, ← sk_prf_post1, ← pk_seed_post1, ← pk_root_post1, ← r_post, ← digest_post,
      ← hmd, ← idx_tree_post, ← idx_leaf_post, ← hadrs, ← sig_fors_post, ← pk_fors_a_post,
      ← pk_fors_b_post, ← sig_ht_post]
  · obtain rfl : ok1 = true := by assumption
    have hdh : (alloc.vec.Vec.deref sig_ht).val = sig_ht.val := by simp [alloc.vec.Vec.deref]
    simp [sig2_post, sig1_post, sig_post, s8_post, hdh]
  · obtain rfl : ok1 = false := by simpa using ‹¬ok1 = true›
    simp

@[step]
theorem slh_sign_checked_spec (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    slh.slh_sign_checked m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSignChecked (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold slh.slh_sign_checked
  by_cases hc : ctx.len > 255#usize
  · have : ctx.val.length > 255 := by scalar_tac
    simp [hc, Spec.slhSignChecked, this]
  · have hc' : ctx.length ≤ 255 := by scalar_tac
    have hc'' : ¬ ctx.val.length > 255 := by scalar_tac
    simp only [hc, ite_false]
    step*
    · have h1 : mp.deref.length = mp.length := by
        simp [alloc.vec.Vec.deref, Slice.length, alloc.vec.Vec.length]
      simp only [Room] at *; scalar_tac
    · simp [Spec.slhSignChecked, *, alloc.vec.Vec.deref]

end slhdsa
