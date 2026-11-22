import Slhdsa.Proofs.Slh
open Aeneas Aeneas.Std Result

/-! The checked signer (`ht_sign_checked`, `slh_sign_internal_checked`,
`slh_sign_checked`) computes `Spec/Checked.lean`, for any valid parameter
set. (`fors_pk_gen` is in `Fors.lean`.) -/

namespace slhdsa

@[local step]
theorem checked_extend_spec (v : alloc.vec.Vec U8) (s : Slice U8) (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  rw [dite_eq_left h]
  apply WP.spec_bind (@List.clone_spec _ core.clone.CloneU8.clone s.val (by intros; rfl))
  intro l hl
  simp [hl]

theorem bytes_beq {N : Usize} (x y : Array U8 N) :
    (bytes x.val == bytes y.val) = decide (x.val = y.val) := by
  by_cases h : x.val = y.val
  · simp [h]
  · have : bytes x.val ≠ bytes y.val := fun hb => h (ht_bytes_injective hb)
    simp [h, this]

theorem ht_sign_checked_loop_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (root : Array U8 N) (sig : alloc.vec.Vec U8)
    (msgA msgB : Array U8 N) (ok1 : Bool)
    (tree : U64) (leaf : U32) (j : U32) (C0 : Spec.Bytes × Spec.Bytes × Spec.Bytes × Bool × Nat × Nat)
    (hj : j.val ≤ p.d.val) (hl : leaf.val < 2 ^ p.hp.val)
    (hlen : sig.length = (2 * N.val + 3 + p.hp.val) * N.val * j.val)
    (hinv : (bytes sig.val, bytes msgA.val, bytes msgB.val, ok1, tree.val, leaf.val) =
      (List.range j.val).foldl
        (Spec.htCheckedStep (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (bytes root.val)) C0) :
    ht.ht_sign_checked_loop p sk seed root sig msgA msgB ok1 tree leaf j ⦃ r =>
      r.1.length = p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) ∧ (bytes r.1.val, r.2) =
        (((List.range p.d.val).foldl
          (Spec.htCheckedStep (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (bytes root.val)) C0).1,
         ((List.range p.d.val).foldl
          (Spec.htCheckedStep (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (bytes root.val)) C0).2.2.2.1) ⦄ := by
  have hv := hp.valid
  have hd : p.d.val ≤ 22 := by simpa using hv.d_le
  have hhp : p.hp.val ≤ 9 := by simpa using hv.hp_le
  have hxsb := ht_xs_le p hp
  generalize hX : (2 * N.val + 3 + p.hp.val) * N.val = X at *
  unfold ht.ht_sign_checked_loop
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × Array U8 N × Array U8 N × Bool × U64 × U32 × U32) =>
      p.d.val - q.2.2.2.2.2.2.val)
    (inv := fun q => q.2.2.2.2.2.2.val ≤ p.d.val ∧ q.2.2.2.2.2.1.val < 2 ^ p.hp.val ∧
      q.1.length = X * q.2.2.2.2.2.2.val ∧
      (bytes q.1.val, bytes q.2.1.val, bytes q.2.2.1.val, q.2.2.2.1, q.2.2.2.2.1.val, q.2.2.2.2.2.1.val) =
        (List.range q.2.2.2.2.2.2.val).foldl
          (Spec.htCheckedStep (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (bytes root.val)) C0)
  · rintro ⟨sig, msgA, msgB, ok1, tree, leaf, j⟩ ⟨hj, hl, hlen, hinv⟩
    simp only [ht.ht_sign_checked_loop.body]
    simp only at hj hl hlen hinv
    split
    · rename_i hlt
      have hlt' : j.val < p.d.val := by scalar_tac
      have hb1 : X * j.val ≤ 2432 * 22 := Nat.mul_le_mul hxsb (by omega)
      step
      step
      step
      step with xmss_sign_spec p hp msgA sk leaf seed hs adrs hl as ⟨s, s_post, s_len⟩
      rw [hX] at s_len
      step with xmss_pk_from_sig_spec p hp leaf (alloc.vec.Vec.deref s) msgB seed hs adrs
        (by simp [s_len, hX]) hl as ⟨root_a, root_a_post⟩
      step as ⟨i, i_post⟩
      have hpow : (0 + 1) * 2 ^ p.hp.val ≤ 2 ^ 32 := by
        have : 2 ^ p.hp.val ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hhp
        omega
      have hrb : (if i < p.d then xmss.xmss_node sk 0#u32 p.hp seed adrs else ok root) ⦃ rb =>
          bytes rb.val = if j.val + 1 < p.d.val then
            Spec.xmssNode (paramsS p) (bytes sk.val) 0 p.hp.val (bytes seed.pk_seed.val) (adrsS adrs)
            else bytes root.val ⦄ := by
        split
        · rename_i hi
          have : j.val + 1 < p.d.val := by scalar_tac
          simp only [this, ↓reduceIte]
          apply WP.spec_mono (xmss_node_spec p hp sk 0#u32 p.hp seed hs adrs (by simpa using hpow))
          intro r hr
          rw [hr]
          simp
        · rename_i hi
          have : ¬ j.val + 1 < p.d.val := by scalar_tac
          simp [this]
      step with hrb as ⟨root_b, root_b_post⟩
      step as ⟨b, b_post⟩
      have hok : (if b = true then ok ok1 else ok false : Result Bool) = ok (ok1 && b) := by
        cases b <;> simp
      rw [hok]
      have hlt64 : p.hp.val < 64 := by omega
      step*
      have h2 : i1.val = 2 ^ p.hp.val := ht_shl_val i1 p.hp hhp i1_post
      have h5 : leaf1.val = tree.val % 2 ^ p.hp.val := by
        rw [leaf1_post]
        exact ht_leaf_val tree i2 i3 p.hp hhp (by omega) i3_post
      have ha : adrsS adrs = { Spec.Adrs.zero with layer := j.val, tree := tree.val } := by
        simp [adrsS, adrs_post, a1_post, a_post, Spec.Adrs.zero]
      have hd' : s.deref.val = s.val := by simp [alloc.vec.Vec.deref]
      refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · rw [h5]; exact Nat.mod_lt _ (by positivity)
      · have : sig1.val.length = sig.val.length + s.val.length := by rw [sig1_post, hd']; simp
        simp only [alloc.vec.Vec.length] at hlen s_len ⊢
        rw [this, hlen, s_len, i_post]; ring
      · rw [i_post, List.range_succ, List.foldl_append, ← hinv]
        simp only [List.foldl_cons, List.foldl_nil, Spec.htCheckedStep]
        rw [b_post, ← bytes_beq]
        simp only [sig1_post, hd', bytes_append, s_post, root_a_post, root_b_post, ha, h5, tree1_post]
        simp
        constructor <;> rfl
    · have hjd : j.val = p.d.val := by scalar_tac
      simp only [step_simps]
      rw [hjd] at hinv hlen
      rw [← hinv]
      exact ⟨by rw [hlen, Nat.mul_comm], rfl, rfl⟩
  · exact ⟨hj, hl, hlen, hinv⟩

theorem htSignChecked_eq (P : Spec.Params) (mA mB sk pk : Spec.Bytes) (t l : Nat) (root : Spec.Bytes) :
    Spec.htSignChecked P mA mB sk pk t l root =
      (((List.range P.d).foldl (Spec.htCheckedStep P sk pk root) ([], mA, mB, mA == mB, t, l)).1,
       ((List.range P.d).foldl (Spec.htCheckedStep P sk pk root) ([], mA, mB, mA == mB, t, l)).2.2.2.1) := by
  unfold Spec.htSignChecked
  generalize List.foldl _ _ _ = C
  obtain ⟨_, _, _, _, _, _⟩ := C
  rfl

@[step]
theorem ht_sign_checked_spec {N : Usize} (p : params.Params) (hp : PN p N) (mA mB sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed)
    (idx_tree : U64) (idx_leaf : U32) (root : Array U8 N) (hl : idx_leaf.val < 2 ^ p.hp.val) :
    ht.ht_sign_checked p mA mB sk seed idx_tree idx_leaf root ⦃ r =>
      (bytes r.1.val, r.2) = Spec.htSignChecked (paramsS p) (bytes mA.val) (bytes mB.val) (bytes sk.val)
        (bytes seed.pk_seed.val) idx_tree.val idx_leaf.val (bytes root.val) ∧
      r.1.length = p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) ⦄ := by
  unfold ht.ht_sign_checked
  step as ⟨b, b_post⟩
  have hok : (if b = true then ok true else ok false : Result Bool) = ok b := by cases b <;> rfl
  rw [hok]
  step with ht_sign_checked_loop_spec p hp sk seed hs root (alloc.vec.Vec.new U8) mA mB b idx_tree
      idx_leaf 0#u32
      ([], bytes mA.val, bytes mB.val, bytes mA.val == bytes mB.val, idx_tree.val, idx_leaf.val)
      (by simp) hl (by simp) (by simp [b_post, bytes_beq]) as ⟨r, h1, h2, h3⟩
  refine ⟨?_, h1⟩
  rw [h2, h3, htSignChecked_eq]
  rfl

set_option maxHeartbeats 2000000 in
@[step]
theorem slh_sign_internal_checked_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Slice U8)
    (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val) (hm : Room m.length (msgSlack N.val)) :
    slh.slh_sign_internal_checked p m sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSignInternalChecked (paramsS p) (bytes m.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  have hv := hp.valid
  have hn := hp.le32
  have hmq := hv.m_eq
  simp only [paramsS_m] at hmq
  have hfl := fors_len_le p hp
  have hhl := ht_len_le p hp
  unfold slh.slh_sign_internal_checked
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
  let* ⟨ pk_fors_a, pk_fors_a_post ⟩ ← fors_pk_from_sig_spec p hp (alloc.vec.Vec.deref sig_fors) md seed
    seed_ok adrs
  let* ⟨ pk_fors_b, pk_fors_b_post ⟩ ← fors_pk_gen_spec p hp sk_seed seed seed_ok adrs
  let* ⟨ sig_ht, ok1, ht_r_post, ht_r_len ⟩ ← ht_sign_checked_spec p hp pk_fors_a pk_fors_b sk_seed seed
    seed_ok idx_tree idx_leaf pk_root idx_leaf_lt
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
  have hdf : (alloc.vec.Vec.deref sig_fors).val = sig_fors.val := by simp [alloc.vec.Vec.deref]
  rw [seed_pk] at sig_fors_post pk_fors_a_post pk_fors_b_post ht_r_post
  rw [hdf] at pk_fors_a_post
  simp only [vec_deref_val] at idx_tree_post idx_leaf_post
  have hspec : Spec.slhSignInternalChecked (paramsS p) (bytes m.val) (bytes sk.val) (bytes addrnd.val) =
      if ok1 then some (bytes r.val ++ bytes sig_fors.val ++ bytes sig_ht.val) else none := by
    simp only [Spec.slhSignInternalChecked]
    rw [← hb0, ← hb1, ← hb2, ← hb3, ← r_post, ← digest_post, ← hmd, ← idx_tree_post,
      ← idx_leaf_post, ← hadrs, ← sig_fors_post, ← pk_fors_a_post, ← pk_fors_b_post, ← ht_r_post]
  rw [hspec]
  split
  · rename_i hok
    subst hok
    let* ⟨ s3, s3_post ⟩ ← Array.to_slice.step_spec
    let* ⟨ sg0, sg0_post ⟩ ← checked_extend_spec
    have hl0 : sg0.length = N.val := by
      simp only [alloc.vec.Vec.length]; rw [sg0_post, s3_post]; simp
    let* ⟨ sg1, sg1_post ⟩ ← checked_extend_spec
    have hl1 : sg1.length = N.val + p.k.val * (1 + p.a.val) * N.val := by
      have : sg1.val.length = sg0.val.length + sig_fors.val.length := by rw [sg1_post]; simp
      simp only [alloc.vec.Vec.length] at hl0 sig_fors_len ⊢; omega
    let* ⟨ sg2, sg2_post ⟩ ← checked_extend_spec
    simp [sg2_post, sg1_post, sg0_post, s3_post]
  · simp

@[step]
theorem slh_sign_checked_spec {N : Usize} (p : params.Params) (hp : PN p N) (m ctx sk : Slice U8)
    (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    slh.slh_sign_checked p m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSignChecked (paramsS p) (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold slh.slh_sign_checked
  by_cases hc : ctx.len > 255#usize
  · have : ctx.val.length > 255 := by scalar_tac
    simp [hc, Spec.slhSignChecked, this]
  · have hc' : ctx.length ≤ 255 := by scalar_tac
    have hc'' : ¬ ctx.val.length > 255 := by scalar_tac
    simp only [hc, ite_false]
    have hR := hm
    simp only [Room] at hR
    let* ⟨ mp, mp_post, mp_len ⟩ ← with_context_spec
    apply WP.spec_mono (slh_sign_internal_checked_spec p hp (alloc.vec.Vec.deref mp) sk addrnd hsk
      (room_ctx m N.val _ hm (by simp [mp_len]; omega)))
    intro r hr
    rw [hr]
    simp [Spec.slhSignChecked, hc'', mp_post]

end slhdsa
