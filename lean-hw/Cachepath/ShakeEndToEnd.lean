import Cachepath.EndToEnd
import Cachepath.ShakeNode
import Cachepath.ShakeScalar
import Slhdsa.Proofs.ShakeSlh

/-! Serial production SHAKE cache assembly, including the extracted XMSS sign and recovery loops.
Lower-level cache primitives use the portable SHAKE models in `Cacheops.FunsExternal`. -/
open Aeneas Aeneas.Std Result slhdsa CacheopsRust
namespace slhdsa.cache.endtoend.shake

private theorem sign_from_digest_loop_spec {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N)
    (sk_seed : Array U8 N) (seed : Array U8 N)
    (top_tree : Slice (Array U8 N)) (layer_d2_hit : Option (Slice (Array U8 N)))
    (root0 : Array U8 N) (sig0 : alloc.vec.Vec U8) (idx_tree : U64) (idx_leaf : U32)
    (htree_lt : idx_tree.val < 2 ^ (p.h.val - p.hp.val))
    (hleaf_lt : idx_leaf.val < 2 ^ p.hp.val)
    (hsig0_len : sig0.length = N.val + p.k.val * (1 + p.a.val) * N.val)
    (htop_len : top_tree.length = treeSize p.hp.val)
    (htop : slhdsa.cache.Built top_tree (Shake.params (toSlhParams p)) (bytes sk_seed.val)
      (bytes seed.val) (layerAdrs (p.d.val - 1) 0))
    (hd2 : ∀ d2, layer_d2_hit = some d2 →
      d2.length = treeSize p.hp.val ∧
      slhdsa.cache.Built d2 (Shake.params (toSlhParams p)) (bytes sk_seed.val)
        (bytes seed.val)
        (layerAdrs (p.d.val - 2) (idx_tree.val >>> ((p.d.val - 2) * p.hp.val)))) :
    CacheopsRust.cache.shake_ops.sign_from_digest_loop
      ⟨0#u32, 0#u64, 0#u32, 0#u32, 0#u32, 0#u32⟩
      { start := 0#u32, «end» := p.d }
      p.n p.h p.d p.hp p.a p.k p.m
      sk_seed seed top_tree layer_d2_hit root0 sig0 idx_tree idx_leaf ⦃ sig =>
        bytes sig.val = bytes sig0.val ++
          Spec.htSign (Shake.params (toSlhParams p)) (bytes root0.val)
            (bytes sk_seed.val) (bytes seed.val) idx_tree.val idx_leaf.val ⦄ := by
  let P := Shake.params (toSlhParams p)
  have hv : P.Valid := ⟨hp.valid.n_cases, hp.valid.lgw_eq, hp.valid.d_ge, hp.valid.d_le,
    hp.valid.hp_pos, hp.valid.hp_le, hp.valid.h_eq, hp.valid.tree_le, hp.valid.a_pos,
    hp.valid.a_le, hp.valid.k_pos, hp.valid.k_le, hp.valid.m_eq⟩
  have hn := hp.le32
  have hd_ge : 2 ≤ p.d.val := hv.d_ge
  have hd_le : p.d.val ≤ 22 := hv.d_le
  have hhp_pos : 1 ≤ p.hp.val := hv.hp_pos
  have hhp_le : p.hp.val ≤ 9 := hv.hp_le
  have h_eq : p.h.val = p.d.val * p.hp.val := hv.h_eq
  have hfl : p.k.val * (1 + p.a.val) * N.val ≤ 16800 := fors_len_le (toSlhParams p) hp
  have hhl : p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) ≤ 53504 := ht_len_le (toSlhParams p) hp
  have hu := usize_max_ge
  have hpow_hp : 2 ^ p.hp.val ≤ 2 ^ 9 := two_pow_le_two_pow hhp_le
  have hpow_pos : 1 ≤ 2 ^ p.hp.val := Nat.two_pow_pos _
  have htop_tree_zero : idx_tree.val >>> (p.hp.val * (p.d.val - 1)) = 0 := by
    have hmul : p.h.val - p.hp.val = p.hp.val * (p.d.val - 1) := by
      rw [h_eq, Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    rw [Nat.shiftRight_eq_div_pow, ← hmul]
    exact Nat.div_eq_of_lt htree_lt
  unfold CacheopsRust.cache.shake_ops.sign_from_digest_loop
  apply loop.spec_decr_nat
    (measure := fun (q : core.ops.range.Range U32 × Option (Slice (Array U8 N)) × Array U8 N ×
      alloc.vec.Vec U8 × U64 × U32) => p.d.val - q.1.start.val)
    (inv := fun q =>
      q.1.end = p.d ∧ q.1.start.val ≤ p.d.val ∧ q.2.1 = layer_d2_hit ∧
      let st := (List.range q.1.start.val).foldl
        (Spec.htLayer P (bytes sk_seed.val) (bytes seed.val))
        ([], bytes root0.val, idx_tree.val, idx_leaf.val)
      bytes q.2.2.2.1.val = bytes sig0.val ++ st.1 ∧
      q.2.2.2.1.length = sig0.length + q.1.start.val * ((2 * N.val + 3 + p.hp.val) * N.val) ∧
      (q.1.start.val < p.d.val → bytes q.2.2.1.val = st.2.1) ∧
      q.2.2.2.2.1.val = st.2.2.1 ∧
      q.2.2.2.2.2.val = st.2.2.2 ∧
      q.2.2.2.2.2.val < 2 ^ p.hp.val)
  · rintro ⟨it, d2Opt, curRoot, curSig, curTree, curLeaf⟩
      ⟨hend, hle, hd2_eq, hsig_inv, hlen_inv, hroot_inv, htree_inv, hleaf_inv, hleaf_bd⟩
    simp only at hend hle hd2_eq hsig_inv hlen_inv hroot_inv htree_inv hleaf_inv hleaf_bd ⊢
    subst d2Opt
    unfold CacheopsRust.cache.shake_ops.sign_from_digest_loop.body
    by_cases hlt : it.start.val < p.d.val
    · obtain ⟨⟨o, next⟩, hget, ho, hstart, hend'⟩ := spec_imp_exists
        (core.iter.range.IteratorRange.next_U32_some_spec it (by rw [hend]; exact hlt))
      subst o
      rw [hget]
      simp only [bind_ok, CacheopsRust.address.Adrs.with_layer, CacheopsRust.address.Adrs.with_tree]
      step as ⟨i7, hi7⟩
      have hroot_eq : bytes curRoot.val =
          ((List.range it.start.val).foldl
            (Spec.htLayer P (bytes sk_seed.val) (bytes seed.val))
            ([], bytes root0.val, idx_tree.val, idx_leaf.val)).2.1 := hroot_inv hlt
      have htree_shift : curTree.val = idx_tree.val >>> (p.hp.val * it.start.val) := by
        rw [htree_inv]
        exact (htLayer_state P hv (bytes sk_seed.val) (bytes seed.val)
          (bytes root0.val) idx_tree.val idx_leaf.val hleaf_lt it.start.val
          (by show it.start.val ≤ p.d.val; omega)).1
      have hcur_adrs : adrsS (toSlhAdrs ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩) =
          { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val } := rfl
      have hlen_bound : curSig.length + (2 * N.val + 3 + p.hp.val) * N.val ≤ Usize.max := by
        have hstep_le : (it.start.val + 1) * ((2 * N.val + 3 + p.hp.val) * N.val) ≤
            p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at hstep_le
        omega
      have hstep_branch :
          (if it.start = i7 then do
              let a2 ← CacheopsRust.address.Adrs.with_type
                ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩ CacheopsRust.address.WOTS_HASH
              let a3 ← CacheopsRust.address.Adrs.with_keypair a2 curLeaf
              let wots ← CacheopsRust.cache.shake_ops.wots_sign curRoot sk_seed seed a3
              let s := alloc.vec.Vec.deref wots
              let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 curSig s
              let sig3 ← CacheopsRust.cache.append_auth_path top_tree p.hp curLeaf sig2
              ok (layer_d2_hit, curRoot, sig3, next)
            else do
              let i8 ← it.start + 2#u32
              if i8 = p.d then
                let (a2, v) ← match layer_d2_hit with
                  | none => do
                      let s ← CacheopsRust.cache.shake_ops.xmss_sign
                        { n := p.n, h := p.h, d := p.d, hp := p.hp, a := p.a, k := p.k, m := p.m }
                        curRoot sk_seed curLeaf seed
                        ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩
                      let s1 := alloc.vec.Vec.deref s
                      let root2 ← CacheopsRust.cache.shake_ops.xmss_pk_from_sig
                        { n := p.n, h := p.h, d := p.d, hp := p.hp, a := p.a, k := p.k, m := p.m }
                        curLeaf s1 curRoot seed
                        ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩
                      let s2 := alloc.vec.Vec.deref s
                      let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 curSig s2
                      ok (root2, sig2)
                  | some d2_tree => do
                      let a3 ← CacheopsRust.address.Adrs.with_type
                        ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩ CacheopsRust.address.WOTS_HASH
                      let a4 ← CacheopsRust.address.Adrs.with_keypair a3 curLeaf
                      let wots ← CacheopsRust.cache.shake_ops.wots_sign curRoot sk_seed seed a4
                      let s := alloc.vec.Vec.deref wots
                      let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 curSig s
                      let sig3 ← CacheopsRust.cache.append_auth_path d2_tree p.hp curLeaf sig2
                      let root2 ← CacheopsRust.cache.tree_root d2_tree
                      ok (root2, sig3)
                ok (layer_d2_hit, a2, v, next)
              else do
                let s ← CacheopsRust.cache.shake_ops.xmss_sign
                  { n := p.n, h := p.h, d := p.d, hp := p.hp, a := p.a, k := p.k, m := p.m }
                  curRoot sk_seed curLeaf seed
                  ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩
                let s1 := alloc.vec.Vec.deref s
                let root2 ← CacheopsRust.cache.shake_ops.xmss_pk_from_sig
                  { n := p.n, h := p.h, d := p.d, hp := p.hp, a := p.a, k := p.k, m := p.m }
                  curLeaf s1 curRoot seed
                  ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩
                let s2 := alloc.vec.Vec.deref s
                let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 curSig s2
                ok (layer_d2_hit, root2, sig2, next)) ⦃ res =>
            res.1 = layer_d2_hit ∧ res.2.2.2 = next ∧
            let adrsS_cur : Spec.Adrs :=
              { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val }
            let xsig := Spec.xmssSign P (bytes curRoot.val) (bytes sk_seed.val) curLeaf.val
              (bytes seed.val) adrsS_cur
            bytes res.2.2.1.val = bytes curSig.val ++ xsig ∧
            res.2.2.1.length = curSig.length + (2 * N.val + 3 + p.hp.val) * N.val ∧
            (it.start.val + 1 < p.d.val →
              bytes res.2.1.val = Spec.xmssPkFromSig P curLeaf.val xsig (bytes curRoot.val)
                (bytes seed.val) adrsS_cur) ⦄ := by
        by_cases htop_case : it.start = i7
        · simp only [htop_case, ↓reduceIte, CacheopsRust.address.Adrs.with_type,
            CacheopsRust.address.Adrs.with_keypair, bind_ok]
          have hlayer_eq : it.start.val = p.d.val - 1 := by rw [htop_case, hi7]
          have htree0 : curTree.val = 0 := by rw [htree_shift, hlayer_eq, htop_tree_zero]
          step with slhdsa.Shake.wots_sign_spec (toSlhParams p) hp curRoot sk_seed seed
            as ⟨wots, hwots_bytes, hwots_len⟩
          have hwots_room : curSig.length + (alloc.vec.Vec.deref wots).length ≤ Usize.max := by
            simp only [vec_deref_len, hwots_len]
            have hmc : N.val * (2 * N.val + 3) = (2 * N.val + 3) * N.val := Nat.mul_comm _ _
            have : (2 * N.val + 3) * N.val ≤ (2 * N.val + 3 + p.hp.val) * N.val :=
              Nat.mul_le_mul_right _ (by omega)
            omega
          step with xmss_extend_u8_spec curSig (alloc.vec.Vec.deref wots) hwots_room
            as ⟨sig2, hsig2_val, hsig2_len⟩
          have hap_room : sig2.length + P.hp * N.val ≤ Usize.max := by
            rw [hsig2_len, vec_deref_len, hwots_len]
            have : N.val * (2 * N.val + 3) + p.hp.val * N.val =
                (2 * N.val + 3 + p.hp.val) * N.val := by ring
            simp only [P, Shake.params, paramsS_hp]; omega
          have htop' : slhdsa.cache.Built top_tree P (bytes sk_seed.val) (bytes seed.val)
              { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val } := by
            simpa [layerAdrs, hlayer_eq, htree0] using htop
          step with append_auth_path_of_built P (bytes sk_seed.val) (bytes seed.val)
            { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val }
            top_tree p.hp curLeaf sig2 rfl hhp_le hleaf_bd htop_len htop' hap_room
            as ⟨sig3, hsig3_bytes, hsig3_len⟩
          refine ⟨?_, ?_, fun hbad => by omega⟩
          · rw [hsig3_bytes, hsig2_val, bytes_append, vec_deref_val, hwots_bytes]
            simp only [Spec.xmssSign, List.append_assoc, adrsS,
              Spec.Adrs.setTypeAndClear, Spec.WOTS_HASH, CacheopsRust.address.WOTS_HASH,
              Spec.Adrs.zero, htop_case]
            rfl
          · rw [hsig3_len, hsig2_len, vec_deref_len, hwots_len]
            simp only [Shake.params, paramsS_hp]; ring
        · simp only [htop_case, ↓reduceIte]
          have hlt_top : it.start.val + 1 < p.d.val := by
            have : it.start.val ≠ p.d.val - 1 := by
              intro h; apply htop_case; apply UScalar.eq_of_val_eq; omega
            omega
          step as ⟨i8, hi8⟩
          by_cases hd2_case : i8 = p.d
          · simp only [hd2_case, ↓reduceIte]
            have hlayer_d2 : it.start.val = p.d.val - 2 := by
              have : i8.val = p.d.val := congrArg UScalar.val hd2_case
              omega
            cases hopt : layer_d2_hit with
            | none =>
              simp only
              simp only [xmss_sign_eq, xmss_pk_from_sig_eq]
              step with slhdsa.Shake.xmss_sign_spec (toSlhParams p) hp curRoot sk_seed curLeaf
                seed _ hleaf_bd as ⟨s, hs_bytes, hs_len⟩
              step with slhdsa.Shake.xmss_pk_from_sig_spec (toSlhParams p) hp curLeaf
                (alloc.vec.Vec.deref s) curRoot seed _
                (by rw [vec_deref_len, hs_len]) hleaf_bd as ⟨root2, hroot2⟩
              step with xmss_extend_u8_spec curSig (alloc.vec.Vec.deref s)
                (by rw [vec_deref_len, hs_len]; exact hlen_bound)
                as ⟨sig2, hsig2_val, hsig2_len⟩
              refine ⟨?_, ?_, fun _ => ?_⟩
              · rw [hsig2_val, bytes_append, vec_deref_val, hs_bytes, hcur_adrs]
              · rw [hsig2_len, vec_deref_len, hs_len]
              · rw [hroot2, vec_deref_val, hs_bytes, hcur_adrs]
            | some d2_tree =>
              simp only [CacheopsRust.address.Adrs.with_type, CacheopsRust.address.Adrs.with_keypair,
                bind_ok]
              obtain ⟨hd2_len, hd2_built⟩ := hd2 d2_tree hopt
              have htree_d2 : curTree.val = idx_tree.val >>> ((p.d.val - 2) * p.hp.val) := by
                rw [htree_shift, hlayer_d2, Nat.mul_comm]
              have hd2_built' : slhdsa.cache.Built d2_tree P (bytes sk_seed.val)
                  (bytes seed.val)
                  { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val } := by
                simpa [layerAdrs, hlayer_d2, htree_d2] using hd2_built
              step with slhdsa.Shake.wots_sign_spec (toSlhParams p) hp curRoot sk_seed seed
                as ⟨wots, hwots_bytes, hwots_len⟩
              have hwots_room : curSig.length + (alloc.vec.Vec.deref wots).length ≤ Usize.max := by
                simp only [vec_deref_len, hwots_len]
                have hmc : N.val * (2 * N.val + 3) = (2 * N.val + 3) * N.val := Nat.mul_comm _ _
                have : (2 * N.val + 3) * N.val ≤ (2 * N.val + 3 + p.hp.val) * N.val :=
                  Nat.mul_le_mul_right _ (by omega)
                omega
              step with xmss_extend_u8_spec curSig (alloc.vec.Vec.deref wots) hwots_room
                as ⟨sig2, hsig2_val, hsig2_len⟩
              have hap_room : sig2.length + P.hp * N.val ≤ Usize.max := by
                rw [hsig2_len, vec_deref_len, hwots_len]
                have : N.val * (2 * N.val + 3) + p.hp.val * N.val =
                    (2 * N.val + 3 + p.hp.val) * N.val := by ring
                simp only [P, Shake.params, paramsS_hp]; omega
              step with append_auth_path_of_built P (bytes sk_seed.val) (bytes seed.val)
                { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val }
                d2_tree p.hp curLeaf sig2 rfl hhp_le hleaf_bd hd2_len hd2_built' hap_room
                as ⟨sig3, hsig3_bytes, hsig3_len⟩
              step with slhdsa.cache.root d2_tree (by rw [hd2_len]; exact treeSize_pos p.hp.val)
                as ⟨root2, hroot2⟩
              refine ⟨?_, ?_, fun _ => ?_⟩
              · rw [hsig3_bytes, hsig2_val, bytes_append, vec_deref_val, hwots_bytes]
                simp only [Spec.xmssSign, List.append_assoc, adrsS,
                  Spec.Adrs.setTypeAndClear, Spec.WOTS_HASH, CacheopsRust.address.WOTS_HASH,
                  Spec.Adrs.zero]
                rfl
              · rw [hsig3_len, hsig2_len, vec_deref_len, hwots_len]
                simp only [Shake.params, paramsS_hp]; ring
              · rw [hroot2, built_root_eq_fips hd2_len hd2_built']
                exact (Spec.xmss_correct P hv (bytes curRoot.val) (bytes sk_seed.val)
                  (bytes seed.val) curLeaf.val
                  { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val } hleaf_bd).symm
          · simp only [hd2_case, ↓reduceIte]
            simp only [xmss_sign_eq, xmss_pk_from_sig_eq]
            step with slhdsa.Shake.xmss_sign_spec (toSlhParams p) hp curRoot sk_seed curLeaf
              seed _ hleaf_bd as ⟨s, hs_bytes, hs_len⟩
            step with slhdsa.Shake.xmss_pk_from_sig_spec (toSlhParams p) hp curLeaf
              (alloc.vec.Vec.deref s) curRoot seed _
              (by rw [vec_deref_len, hs_len]) hleaf_bd as ⟨root2, hroot2⟩
            step with xmss_extend_u8_spec curSig (alloc.vec.Vec.deref s)
              (by rw [vec_deref_len, hs_len]; exact hlen_bound)
              as ⟨sig2, hsig2_val, hsig2_len⟩
            refine ⟨?_, ?_, fun _ => ?_⟩
            · rw [hsig2_val, bytes_append, vec_deref_val, hs_bytes, hcur_adrs]
            · rw [hsig2_len, vec_deref_len, hs_len]
            · rw [hroot2, vec_deref_val, hs_bytes, hcur_adrs]
      have hbind : ∀ {α β : Type} {x : Result α} {f : α → Result β} {P_a : α → Prop} {Q_b : β → Prop},
          x ⦃ P_a ⦄ → (∀ a, P_a a → f a ⦃ Q_b ⦄) → (Std.bind x f) ⦃ Q_b ⦄ := by
        intro α β x f P_a Q_b hx hf
        obtain ⟨a, rfl, ha⟩ := spec_imp_exists hx
        simpa [bind_ok] using hf a ha
      apply hbind hstep_branch
      rintro ⟨d2', root1, sig1, iter2⟩ ⟨hd2', hiter2, hsig1_bytes, hsig1_len, hroot1⟩
      dsimp only at hd2' hiter2 hsig1_bytes hsig1_len hroot1 ⊢
      step as ⟨i8, hi8⟩
      have hi8' : i8.val = 2 ^ p.hp.val := by
        rw [hi8, Nat.one_shiftLeft]
        apply Nat.mod_eq_of_lt; simp [U64.size, U64.numBits]; omega
      step as ⟨i9, hi9⟩
      have hi9' : i9.val = 2 ^ p.hp.val - 1 := by rw [hi9, hi8']
      step as ⟨i10, hi10, _⟩
      have hi10' : i10.val = curTree.val % 2 ^ p.hp.val := by
        rw [hi10, and_mask_val _ _ _ hi9']
      have hi10_lt : i10.val < 2 ^ p.hp.val := by
        rw [hi10']; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      step as ⟨leaf1, hleaf1⟩
      have hleaf1_val : leaf1.val = curTree.val % 2 ^ p.hp.val := by
        have h32 : 2 ^ 9 < 2 ^ UScalarTy.U32.numBits := by simp [UScalarTy.numBits]
        rw [hleaf1, UScalar.cast_val_eq, hi10']
        exact Nat.mod_eq_of_lt (by omega)
      step as ⟨tree1, htree1, _⟩
      subst hiter2 hd2'
      refine ⟨hend'.trans hend, by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
      · rw [hstart, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [Spec.htLayer]
        rw [hsig1_bytes, hsig_inv, hroot_eq, htree_inv, hleaf_inv, List.append_assoc]
      · rw [hsig1_len, hlen_inv, hstart]; ring
      · intro hnext_lt
        rw [hstart, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [Spec.htLayer]
        rw [hroot1 (by omega), hroot_eq, htree_inv, hleaf_inv]
      · rw [hstart, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [Spec.htLayer, htree1, htree_inv]; rfl
      · rw [hstart, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [Spec.htLayer, hleaf1_val, htree_inv]; rfl
      · rw [hleaf1_val]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · step with core.iter.range.IteratorRange.next_U32_none_spec it
          (by rw [hend]; exact Nat.not_lt.mp hlt) as ⟨o, next, ho, _⟩
      simp only [ho, step_simps]
      have heq : it.start.val = p.d.val := by omega
      rw [hsig_inv, heq]
      rfl
  · exact ⟨rfl, Nat.zero_le _, rfl, by simp, by simp, fun _ => rfl, rfl, rfl, hleaf_lt⟩

/-- The extracted serial SHAKE assembler returns the FIPS 205 signature bytes for
a supplied randomizer and digest, using built top and optional layer d−2 trees. -/
theorem sign_from_digest_spec {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N)
    (sk_seed pk_seed r : Array U8 N) (digest : Slice U8)
    (top_tree : Slice (Array U8 N)) (layer_d2_hit : Option (Slice (Array U8 N)))
    (hdig : digest.length = p.m.val)
    (htop_len : top_tree.length = treeSize p.hp.val)
    (htop : slhdsa.cache.Built top_tree (Shake.params (toSlhParams p)) (bytes sk_seed.val)
      (bytes pk_seed.val) (layerAdrs (p.d.val - 1) 0))
    (hd2 : ∀ d2, layer_d2_hit = some d2 →
      d2.length = treeSize p.hp.val ∧
      slhdsa.cache.Built d2 (Shake.params (toSlhParams p)) (bytes sk_seed.val)
        (bytes pk_seed.val)
        (layerAdrs (p.d.val - 2)
          (Spec.digestTree (Shake.params (toSlhParams p)) (bytes digest.val) >>>
            ((p.d.val - 2) * p.hp.val)))) :
    CacheopsRust.cache.shake_ops.sign_from_digest p sk_seed pk_seed r digest top_tree layer_d2_hit ⦃ sig =>
      let P := Shake.params (toSlhParams p)
      let md := (bytes digest.val).take P.mdBytes
      let idxTree := Spec.digestTree P (bytes digest.val)
      let idxLeaf := Spec.digestLeaf P (bytes digest.val)
      let adrs := { { Spec.Adrs.zero with tree := idxTree }.setTypeAndClear
        Spec.FORS_TREE with keypair := idxLeaf }
      let sigFors := Spec.forsSign P md (bytes sk_seed.val) (bytes pk_seed.val) adrs
      let pkFors := Spec.forsPkFromSig P sigFors md (bytes pk_seed.val) adrs
      bytes sig.val = bytes r.val ++ sigFors ++
        Spec.htSign P pkFors (bytes sk_seed.val) (bytes pk_seed.val) idxTree idxLeaf ⦄ := by
  have hv := hp.valid
  have hn := hp.le32
  have hfl : p.k.val * (1 + p.a.val) * N.val ≤ 16800 := fors_len_le (toSlhParams p) hp
  have hu := usize_max_ge
  unfold CacheopsRust.cache.shake_ops.sign_from_digest
  step with cache_digest_tree_spec p digest hv hdig as ⟨idx_tree, hidx_tree, hidx_tree_lt⟩
  step with cache_digest_leaf_spec p digest hv hdig as ⟨idx_leaf, hidx_leaf, hidx_leaf_lt⟩
  change idx_tree.val = Spec.digestTree (Shake.params (toSlhParams p)) _ at hidx_tree
  change idx_leaf.val = Spec.digestLeaf (Shake.params (toSlhParams p)) _ at hidx_leaf
  simp only [CacheopsRust.address.Adrs.new, CacheopsRust.address.Adrs.with_tree,
    CacheopsRust.address.Adrs.with_type, CacheopsRust.address.Adrs.with_keypair, bind_ok]
  have hmd_eq : CacheopsRust.params.Params.md_bytes p =
      slhdsa.params.Params.md_bytes (toSlhParams p) := rfl
  rw [hmd_eq]
  step with slhdsa.md_bytes_spec (toSlhParams p) hv as ⟨i, hi_eq, hi_le⟩
  have hmd_le : i.val ≤ digest.length := by
    have hm := hv.m_eq
    have hmd_lt : (paramsS (toSlhParams p)).mdBytes ≤ (paramsS (toSlhParams p)).m := by omega
    rw [hi_eq, hdig]; exact hmd_lt
  step as ⟨md, hmd_val, hmd_len⟩
  step with slhdsa.Shake.fors_sign_spec (toSlhParams p) hp md sk_seed pk_seed _
    (by rw [hmd_len, hi_eq]; rfl) as ⟨sig_fors, hsf_bytes, hsf_len⟩
  step with slhdsa.Shake.fors_pk_from_sig_spec (toSlhParams p) hp (alloc.vec.Vec.deref sig_fors) md
    pk_seed _ (by rw [vec_deref_len, hsf_len])
    (by rw [hmd_len, hi_eq]; rfl) as ⟨root, hroot_bytes⟩
  rw [sig_bytes_eq]
  step with slhdsa.sig_bytes_spec (toSlhParams p) hv as ⟨i1, _⟩
  step as ⟨s1, hs1⟩
  step with xmss_extend_u8_spec (alloc.vec.Vec.with_capacity U8 i1) s1
    (by simp [alloc.vec.Vec.with_capacity, hs1]; omega) as ⟨sig1, hsig1_val, hsig1_l⟩
  step with xmss_extend_u8_spec sig1 (alloc.vec.Vec.deref sig_fors)
    (by simp [hsig1_l, alloc.vec.Vec.with_capacity, hs1, hsf_len]; omega)
    as ⟨sig2, hsig2_val, hsig2_l⟩
  have hsig2_len : sig2.length = N.val + p.k.val * (1 + p.a.val) * N.val := by
    rw [hsig2_l, hsig1_l, vec_deref_len, hsf_len]
    simp [alloc.vec.Vec.with_capacity, hs1]
  have hd2' : ∀ d2, layer_d2_hit = some d2 →
      d2.length = treeSize p.hp.val ∧
      slhdsa.cache.Built d2 (Shake.params (toSlhParams p)) (bytes sk_seed.val)
        (bytes pk_seed.val)
        (layerAdrs (p.d.val - 2) (idx_tree.val >>> ((p.d.val - 2) * p.hp.val))) := by
    intro d2 hd2_eq
    rw [hidx_tree]
    exact hd2 d2 hd2_eq
  step with sign_from_digest_loop_spec p hp sk_seed pk_seed
    top_tree layer_d2_hit root sig2 idx_tree idx_leaf hidx_tree_lt hidx_leaf_lt hsig2_len
    htop_len htop hd2' as ⟨out, hout⟩
  have hmd_bytes : bytes md.val = (bytes digest.val).take (Shake.params (toSlhParams p)).mdBytes := by
    rw [hmd_val, List.slice, hi_le]; simp [Shake.params, Spec.Params.mdBytes]
  have hfors_adrs : adrsS (toSlhAdrs ⟨0#u32, idx_tree, CacheopsRust.address.FORS_TREE,
      idx_leaf, 0#u32, 0#u32⟩) =
      { { Spec.Adrs.zero with tree := idx_tree.val }.setTypeAndClear Spec.FORS_TREE with
        keypair := idx_leaf.val } := by
    simp [adrsS, Spec.Adrs.setTypeAndClear, Spec.Adrs.zero, Spec.FORS_TREE,
      CacheopsRust.address.FORS_TREE]
  rw [hout, hsig2_val, hsig1_val, bytes_append, bytes_append, hs1, Array.val_to_slice,
    vec_deref_val, hroot_bytes, vec_deref_val, hsf_bytes, hmd_bytes, hfors_adrs,
    hidx_tree, hidx_leaf]
  simp [alloc.vec.Vec.with_capacity, List.append_assoc]

/-- Serial SHAKE signing with the extracted layer-index calculation and cache lookup. -/
theorem sign_from_digest_with_cache_spec {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N)
    (c : CacheopsRust.cache.TopTreeCache N)
    (sk_seed pk_seed r : Array U8 N) (digest : Slice U8)
    (hdig : digest.length = p.m.val)
    (hc : CacheValid c (Shake.params (toSlhParams p)) (bytes sk_seed.val) (bytes pk_seed.val)) :
    (do
      let tree_d2 ← CacheopsRust.cache.TopTreeCache.layer_d2_tree_index N p digest
      let d2_hit ← CacheopsRust.cache.TopTreeCache.lookup_d2 c tree_d2
      CacheopsRust.cache.shake_ops.sign_from_digest p sk_seed pk_seed r digest
        (alloc.vec.Vec.deref c.top_tree) d2_hit) ⦃ sig =>
      let P := Shake.params (toSlhParams p)
      let md := (bytes digest.val).take P.mdBytes
      let idxTree := Spec.digestTree P (bytes digest.val)
      let idxLeaf := Spec.digestLeaf P (bytes digest.val)
      let adrs := { { Spec.Adrs.zero with tree := idxTree }.setTypeAndClear
        Spec.FORS_TREE with keypair := idxLeaf }
      let sigFors := Spec.forsSign P md (bytes sk_seed.val) (bytes pk_seed.val) adrs
      let pkFors := Spec.forsPkFromSig P sigFors md (bytes pk_seed.val) adrs
      bytes sig.val = bytes r.val ++ sigFors ++
        Spec.htSign P pkFors (bytes sk_seed.val) (bytes pk_seed.val) idxTree idxLeaf ⦄ := by
  step with layer_d2_tree_index_spec N p digest hp.valid hdig as ⟨tree_d2, htd2⟩
  step with lookup_d2_spec hc tree_d2 as ⟨d2_hit, hd2_spec⟩
  apply sign_from_digest_spec p hp sk_seed pk_seed r digest (alloc.vec.Vec.deref c.top_tree)
    d2_hit hdig (by rw [vec_deref_len]; exact hc.top_len) hc.top_built
  intro d2 heq
  rw [heq] at hd2_spec
  change tree_d2.val = Spec.digestTree (Shake.params (toSlhParams p)) _ >>> _ at htd2
  rw [htd2] at hd2_spec
  exact hd2_spec

end slhdsa.cache.endtoend.shake
