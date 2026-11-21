import Slhdsa.Proofs.Wots
open Aeneas Aeneas.Std Result

/-! XMSS (FIPS 205 §6). -/

namespace slhdsa

/-- Appending a byte slice to a byte vector. -/
private theorem xmss_extend_u8_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r =>
      r.val = v.val ++ s.val ∧ r.length = v.length + s.length ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (l := s.val) (by intro x _; rfl))
  intro l' hl'
  simp [hl']

/-- `n ≤ 32` for a valid parameter set. -/
theorem xmss_valid_n_le (p : params.Params) (hv : (paramsS p).Valid) : p.n.val ≤ 32 := by
  have hn := hv.n_cases
  simp only [paramsS_n] at hn
  omega

theorem valid_n_pos (p : params.Params) (hv : (paramsS p).Valid) : 0 < p.n.val := by
  have hn := hv.n_cases
  simp only [paramsS_n] at hn
  omega

theorem valid_hp_le (p : params.Params) (hv : (paramsS p).Valid) : p.hp.val ≤ 9 := by
  have h := hv.hp_le
  simpa using h

@[step]
theorem hash2_spec (p : params.Params) (pk : Slice U8) (a : address.Adrs) (l r : Slice U8)
    (hv : (paramsS p).Valid) (hpk : pk.length = p.n.val) (hl : l.length = p.n.val)
    (hr : r.length = p.n.val) :
    xmss.hash2 p pk a l r ⦃ x =>
      bytes x.val = Spec.H (paramsS p) (bytes pk.val) (adrsS a) (bytes l.val ++ bytes r.val) ∧
      x.length = p.n.val ⦄ := by
  unfold xmss.hash2
  have hn := xmss_valid_n_le p hv
  let* ⟨ buf, buf_post, buf_len ⟩ ← xmss_extend_u8_spec
  have hbuf : buf.length = p.n.val := by
    rw [buf_len]; simp [alloc.vec.Vec.new, hl]
  let* ⟨ buf1, buf1_post, buf1_len ⟩ ← xmss_extend_u8_spec
  have hbuf1 : buf1.length = 2 * p.n.val := by
    rw [buf1_len, hbuf, hr]; omega
  let* ⟨ x, x_post, x_len ⟩ ← thash_h_spec
  refine ⟨?_, x_len⟩
  rw [x_post]
  simp [buf1_post, buf_post, alloc.vec.Vec.new]

private theorem xmss_node_aux (p : params.Params) (sk pk : Slice U8) (a : address.Adrs)
    (hv : (paramsS p).Valid) (hsk : sk.length = p.n.val) (hpk : pk.length = p.n.val) (n : Nat) :
    ∀ (i z : U32), z.val = n → (i.val + 1) * 2 ^ n ≤ 2 ^ 32 →
    xmss.xmss_node p sk i z pk a ⦃ r =>
      bytes r.val = Spec.xmssNode (paramsS p) (bytes sk.val) i.val n (bytes pk.val) (adrsS a) ∧
      r.length = p.n.val ⦄ := by
  induction n with
  | zero =>
    intro i z hz h
    unfold xmss.xmss_node
    have hz0 : z = 0#u32 := by scalar_tac
    simp only [hz0, ↓reduceIte]
    let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
    let* ⟨ a2, a2_post ⟩ ← with_keypair_spec
    let* ⟨ r, r_post, r_len ⟩ ← wots_pk_gen_spec
    refine ⟨?_, r_len⟩
    rw [r_post]
    simp [a2_post, a1_post1, Spec.xmssNode, adrsS, Spec.Adrs.setTypeAndClear, Spec.WOTS_HASH,
      address.WOTS_HASH]
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
    let* ⟨ i1, i1_post ⟩ ← U32.mul_spec
    let* ⟨ i2, i2_post ⟩ ← U32.sub_spec
    let* ⟨ lnode, lnode_post, lnode_len ⟩ ← ih
    let* ⟨ i3, i3_post ⟩ ← U32.add_spec
    let* ⟨ rnode, rnode_post, rnode_len ⟩ ← ih
    let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
    let* ⟨ a2, a2_post ⟩ ← with_word2_spec
    let* ⟨ a3, a3_post ⟩ ← with_word3_spec
    let* ⟨ r, r_post, r_len ⟩ ← hash2_spec
    refine ⟨?_, r_len⟩
    rw [r_post]
    simp [lnode_post, rnode_post, i1_post, i3_post, a3_post, a2_post, a1_post1, hz,
      Spec.xmssNode, adrsS, Spec.Adrs.setTypeAndClear, Spec.TREE, address.TREE]

@[step]
theorem xmss_node_spec (p : params.Params) (sk : Slice U8) (i z : U32) (pk : Slice U8)
    (a : address.Adrs) (hv : (paramsS p).Valid) (hsk : sk.length = p.n.val)
    (hpk : pk.length = p.n.val) (h : (i.val + 1) * 2 ^ z.val ≤ 2 ^ 32) :
    xmss.xmss_node p sk i z pk a ⦃ r =>
      bytes r.val = Spec.xmssNode (paramsS p) (bytes sk.val) i.val z.val (bytes pk.val) (adrsS a) ∧
      r.length = p.n.val ⦄ :=
  xmss_node_aux p sk pk a hv hsk hpk z.val i z rfl h

private theorem xmss_sign_loop_spec (p : params.Params) (sk : Slice U8) (idx : U32)
    (pk : Slice U8) (a : address.Adrs) (sig : alloc.vec.Vec U8) (j : U32) (wsig : Spec.Bytes)
    (hv : (paramsS p).Valid) (hsk : sk.length = p.n.val) (hpk : pk.length = p.n.val)
    (hidx : idx.val < 2 ^ p.hp.val) (hj : j.val ≤ p.hp.val)
    (hlen : sig.length = (2 * p.n.val + 3) * p.n.val + p.n.val * j.val)
    (hinv : bytes sig.val = wsig ++ (List.range j.val).flatMap fun j =>
      Spec.xmssNode (paramsS p) (bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j (bytes pk.val)
        (adrsS a)) :
    xmss.xmss_sign_loop p sk idx pk a sig j ⦃ r =>
      bytes r.val = wsig ++ (List.range p.hp.val).flatMap (fun j =>
        Spec.xmssNode (paramsS p) (bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j (bytes pk.val)
          (adrsS a)) ∧
      r.length = (2 * p.n.val + 3 + p.hp.val) * p.n.val ⦄ := by
  have hn32 := xmss_valid_n_le p hv
  have hhp := valid_hp_le p hv
  have hidx9 : idx.val < 2 ^ 9 :=
    lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) hhp)
  unfold xmss.xmss_sign_loop
  apply loop.spec_decr_nat (measure := fun (q : alloc.vec.Vec U8 × U32) => p.hp.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.hp.val ∧
      q.1.length = (2 * p.n.val + 3) * p.n.val + p.n.val * q.2.val ∧
      bytes q.1.val = wsig ++ (List.range q.2.val).flatMap fun j =>
        Spec.xmssNode (paramsS p) (bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j (bytes pk.val)
          (adrsS a))
  · clear hj hlen hinv sig j
    rintro ⟨sig, j⟩ ⟨hj, hlen, hinv⟩
    simp only [xmss.xmss_sign_loop.body]
    simp only at hj hlen hinv
    simp only [step_simps]
    spec_split
    · rename_i hlt
      have hjlt : j.val < p.hp.val := by scalar_tac
      let* ⟨ i, i_post, i_post1 ⟩ ← U32.ShiftRight_spec
      let* ⟨ k, k_post, k_post1 ⟩ ← UScalar.xor_spec
      have hk : k.val = (idx.val / 2 ^ j.val) ^^^ 1 := by
        rw [k_post]; simp [i_post, Nat.shiftRight_eq_div_pow]
      have hkb : k.val < 2 ^ 9 := by
        rw [hk]
        exact Nat.xor_lt_two_pow (lt_of_le_of_lt (Nat.div_le_self _ _) hidx9) (by decide)
      let* ⟨ node, node_post, node_len ⟩ ← xmss_node_spec
      · calc (k.val + 1) * 2 ^ j.val ≤ 2 ^ 9 * 2 ^ 8 :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega))
          _ ≤ 2 ^ 32 := by norm_num
      have hb1 : (2 * p.n.val + 3) * p.n.val ≤ 67 * 32 :=
        Nat.mul_le_mul (by omega) hn32
      have hb2 : p.n.val * j.val ≤ 32 * 9 := Nat.mul_le_mul hn32 (by omega)
      let* ⟨ sig1, sig1_post, sig1_len ⟩ ← xmss_extend_u8_spec
      let* ⟨ j1, j1_post ⟩ ← U32.add_spec
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [sig1_len, hlen, vec_deref_length, node_len, j1_post]; ring
      · simp [sig1_post, hinv, j1_post, List.range_succ, node_post, hk]
    · rename_i hge
      have hjeq : j.val = p.hp.val := by scalar_tac
      simp only [step_simps]
      refine ⟨?_, ?_⟩
      · rw [hinv, hjeq]
      · rw [hlen, hjeq]; ring
  · exact ⟨hj, hlen, hinv⟩

@[step]
theorem xmss_sign_spec (p : params.Params) (m sk : Slice U8) (idx : U32) (pk : Slice U8)
    (a : address.Adrs) (hv : (paramsS p).Valid) (hm : m.length = p.n.val)
    (hsk : sk.length = p.n.val) (hpk : pk.length = p.n.val) (h : idx.val < 2 ^ p.hp.val) :
    xmss.xmss_sign p m sk idx pk a ⦃ r =>
      bytes r.val = Spec.xmssSign (paramsS p) (bytes m.val) (bytes sk.val) idx.val (bytes pk.val)
        (adrsS a) ∧
      r.length = (2 * p.n.val + 3 + p.hp.val) * p.n.val ⦄ := by
  unfold xmss.xmss_sign
  let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
  let* ⟨ a2, a2_post ⟩ ← with_keypair_spec
  let* ⟨ sig, sig_post, sig_len ⟩ ← wots_sign_spec
  apply WP.spec_mono
  · exact xmss_sign_loop_spec p sk idx pk a sig 0#u32 (bytes sig.val) hv hsk hpk h
      (by scalar_tac) (by simp [sig_len]) (by simp)
  · rintro r ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1, sig_post]
    simp [Spec.xmssSign, a2_post, a1_post1, adrsS, Spec.Adrs.setTypeAndClear,
      Spec.WOTS_HASH, address.WOTS_HASH]

/-- One level of `Spec.climb`. -/
private def climbStep (P : Spec.Params) (leaf : Nat) (auth pk : Spec.Bytes) (adrs : Spec.Adrs)
    (st : Spec.Bytes × Nat) (j : Nat) : Spec.Bytes × Nat :=
  if (leaf / 2 ^ j) % 2 = 0 then
    (Spec.H P pk { adrs with word2 := j + 1, word3 := st.2 / 2 } (st.1 ++ Spec.block P auth j),
      st.2 / 2)
  else
    (Spec.H P pk { adrs with word2 := j + 1, word3 := (st.2 - 1) / 2 }
      (Spec.block P auth j ++ st.1), (st.2 - 1) / 2)

private theorem climb_eq (P : Spec.Params) (node : Spec.Bytes) (leaf ti : Nat) (auth : Spec.Bytes)
    (height : Nat) (pk : Spec.Bytes) (adrs : Spec.Adrs) :
    Spec.climb P node leaf ti auth height pk adrs =
      ((List.range height).foldl (climbStep P leaf auth pk adrs) (node, ti)).1 := by
  unfold Spec.climb
  congr 2

/-- Block `k` of the `h` blocks starting at block `f` is block `f + k`. -/
theorem block_drop_take (P : Spec.Params) (s : Spec.Bytes) (f h k : Nat) (hk : k < h) :
    Spec.block P ((s.drop (f * P.n)).take (h * P.n)) k = Spec.block P s (f + k) := by
  simp only [Spec.block, List.drop_take, List.take_take, List.drop_drop]
  have h0 : h * P.n - k * P.n = (h - k) * P.n := by rw [Nat.sub_mul]
  have h1 : min P.n (h * P.n - k * P.n) = P.n := by
    rw [h0]; exact Nat.min_eq_left (Nat.le_mul_of_pos_left _ (by omega))
  have h2 : f * P.n + k * P.n = (f + k) * P.n := by ring
  rw [h1, h2]

private theorem climb_loop_spec (p : params.Params) (auth : Slice U8) (first : Usize)
    (height : U32) (pk : Slice U8) (a : address.Adrs) (node : alloc.vec.Vec U8) (index k : U32)
    (c leaf : Nat) (N0 : Spec.Bytes) (T0 : Nat)
    (hv : (paramsS p).Valid) (hnode : node.length = p.n.val) (hpk : pk.length = p.n.val)
    (hlen : (first.val + height.val) * p.n.val ≤ auth.length) (hh : height.val ≤ 31)
    (hk : k.val ≤ height.val)
    (hidx : index.val = c * 2 ^ (height.val - k.val) + leaf / 2 ^ k.val)
    (hinv : (bytes node.val, index.val) = (List.range k.val).foldl
      (climbStep (paramsS p) leaf
        (((bytes auth.val).drop (first.val * p.n.val)).take (height.val * p.n.val))
        (bytes pk.val) (adrsS a)) (N0, T0)) :
    xmss.climb_loop p auth first height pk a node index k ⦃ r =>
      bytes r.val = ((List.range height.val).foldl
        (climbStep (paramsS p) leaf
          (((bytes auth.val).drop (first.val * p.n.val)).take (height.val * p.n.val))
          (bytes pk.val) (adrsS a)) (N0, T0)).1 ∧
      r.length = p.n.val ⦄ := by
  have hnpos := valid_n_pos p hv
  unfold xmss.climb_loop
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32 × U32) => height.val - q.2.2.val)
    (inv := fun q => q.2.2.val ≤ height.val ∧ q.1.length = p.n.val ∧
      q.2.1.val = c * 2 ^ (height.val - q.2.2.val) + leaf / 2 ^ q.2.2.val ∧
      (bytes q.1.val, q.2.1.val) = (List.range q.2.2.val).foldl
        (climbStep (paramsS p) leaf
          (((bytes auth.val).drop (first.val * p.n.val)).take (height.val * p.n.val))
          (bytes pk.val) (adrsS a)) (N0, T0))
  · clear hk hidx hinv hnode node index k
    rintro ⟨node, index, k⟩ ⟨hk, hnode, hidx, hinv⟩
    simp only [xmss.climb_loop.body]
    simp only at hk hnode hidx hinv
    simp only [step_simps]
    spec_split
    · rename_i hlt
      have hklt : k.val < height.val := by scalar_tac
      have hfk : (first.val + k.val + 1) * p.n.val ≤ auth.length :=
        le_trans (Nat.mul_le_mul_right _ (by omega)) hlen
      have hfk' : first.val + k.val + 1 ≤ auth.length :=
        le_trans (Nat.le_mul_of_pos_right _ hnpos) hfk
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
      have hsib : bytes sibling.val = Spec.block (paramsS p)
          (((bytes auth.val).drop (first.val * p.n.val)).take (height.val * p.n.val)) k.val := by
        rw [bytes_block p auth.val sibling.val i1.val sibling_post, i1_post, hi]
        exact (block_drop_take (paramsS p) _ _ _ _ hklt).symm
      have hadrs : adrsS a2 = { adrsS a with word2 := k.val + 1, word3 := index.val / 2 } := by
        simp [adrsS, a2_post, a1_post, i2_post, hpar]
      by_cases h3 : i3 = 0#u32
      · simp only [h3, ↓reduceIte]
        have heven : (leaf / 2 ^ k.val) % 2 = 0 := by
          rw [← hmod, ← hi3, h3]; rfl
        let* ⟨ node1, node1_post, node1_len ⟩ ← hash2_spec
        refine ⟨by scalar_tac, node1_len, ?_, ?_, by scalar_tac⟩
        · rw [i2_post, hpar, hdiv]
        · rw [i2_post, List.range_succ, List.foldl_append, ← hinv]
          simp [climbStep, heven, node1_post, hadrs, hsib, hpar]
      · simp only [h3, ↓reduceIte]
        have hodd : ¬ (leaf / 2 ^ k.val) % 2 = 0 := by
          rw [← hmod, ← hi3]; intro h0; apply h3; scalar_tac
        have hsub : (index.val - 1) / 2 = index.val / 2 := by omega
        let* ⟨ node1, node1_post, node1_len ⟩ ← hash2_spec
        refine ⟨by scalar_tac, node1_len, ?_, ?_, by scalar_tac⟩
        · rw [i2_post, hpar, hdiv]
        · rw [i2_post, List.range_succ, List.foldl_append, ← hinv]
          simp [climbStep, hodd, node1_post, hadrs, hsib, hpar, hsub]
    · rename_i hge
      have hkh : k.val = height.val := by scalar_tac
      simp only [step_simps]
      have h1 := congrArg Prod.fst hinv
      rw [hkh] at h1
      exact ⟨h1, hnode⟩
  · exact ⟨hk, hnode, hidx, hinv⟩

/-- `idx = c · 2^height + leaf`: `leaf` is the index within the tree being
climbed, whose bits choose left or right; `idx` is the index written into the
addresses. For XMSS `c = 0`; for the `i`-th FORS tree `c = i`. -/
@[step]
theorem climb_spec (p : params.Params) (node : alloc.vec.Vec U8) (idx : U32) (auth : Slice U8)
    (first : Usize) (height : U32) (pk : Slice U8) (a : address.Adrs) (c leaf : Nat)
    (hv : (paramsS p).Valid) (hnode : node.length = p.n.val) (hpk : pk.length = p.n.val)
    (hlen : (first.val + height.val) * p.n.val ≤ auth.length) (hh : height.val ≤ 31)
    (hidx : idx.val = c * 2 ^ height.val + leaf) (hleaf : leaf < 2 ^ height.val) :
    xmss.climb p node idx auth first height pk a ⦃ r =>
      bytes r.val = Spec.climb (paramsS p) (bytes node.val) leaf idx.val
        (((bytes auth.val).drop (first.val * p.n.val)).take (height.val * p.n.val)) height.val
        (bytes pk.val) (adrsS a) ∧
      r.length = p.n.val ⦄ := by
  have _ := hleaf
  unfold xmss.climb
  apply WP.spec_mono
  · exact climb_loop_spec p auth first height pk a node idx 0#u32 c leaf (bytes node.val) idx.val
      hv hnode hpk hlen hh (by scalar_tac) (by simpa using hidx) (by simp)
  · rintro r ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [climb_eq]; exact h1

/-- The first `l` blocks are unaffected by truncation to `l` blocks. -/
theorem block_take (P : Spec.Params) (s : Spec.Bytes) (l i : Nat) (hi : i < l) :
    Spec.block P (s.take (l * P.n)) i = Spec.block P s i := by
  simp only [Spec.block, List.drop_take, List.take_take]
  have h0 : l * P.n - i * P.n = (l - i) * P.n := by rw [Nat.sub_mul]
  have h1 : min P.n (l * P.n - i * P.n) = P.n := by
    rw [h0]; exact Nat.min_eq_left (Nat.le_mul_of_pos_left _ (by omega))
  rw [h1]

/-- `wots_pkFromSig` reads only the first `len · n` bytes of its signature argument. -/
theorem wotsPkFromSig_take (P : Spec.Params) (s msg pk : Spec.Bytes) (ad : Spec.Adrs) :
    Spec.wotsPkFromSig P (s.take (P.len * P.n)) msg pk ad = Spec.wotsPkFromSig P s msg pk ad := by
  unfold Spec.wotsPkFromSig
  refine congrArg (Spec.T P pk (Spec.wotsPkAdrs ad)) ?_
  apply List.flatMap_congr
  intro i hi
  rw [block_take P s P.len i (by simpa using hi)]

@[step]
theorem xmss_pk_from_sig_spec (p : params.Params) (idx : U32) (sig m pk : Slice U8)
    (a : address.Adrs) (hv : (paramsS p).Valid)
    (h : sig.length = (2 * p.n.val + 3 + p.hp.val) * p.n.val) (hm : m.length = p.n.val)
    (hpk : pk.length = p.n.val) (hidx : idx.val < 2 ^ p.hp.val) :
    xmss.xmss_pk_from_sig p idx sig m pk a ⦃ r =>
      bytes r.val = Spec.xmssPkFromSig (paramsS p) idx.val (bytes sig.val) (bytes m.val)
        (bytes pk.val) (adrsS a) ∧
      r.length = p.n.val ⦄ := by
  unfold xmss.xmss_pk_from_sig
  have hhp := valid_hp_le p hv
  let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
  let* ⟨ a2, a2_post ⟩ ← with_keypair_spec
  let* ⟨ node, node_post, node_len ⟩ ← wots_pk_from_sig_spec
  let* ⟨ i, i_post, i_post1 ⟩ ← len_spec
  let* ⟨ a3, a3_post, a3_post1 ⟩ ← with_type_spec
  apply WP.spec_mono
  · exact climb_spec p node idx sig i p.hp pk a3 0 idx.val hv node_len hpk
      (by rw [i_post, h]) (by omega) (by simp) hidx
  · rintro r ⟨hr, hr2⟩
    refine ⟨?_, hr2⟩
    simp only [Spec.xmssPkFromSig, wotsPkFromSig_take]
    rw [hr, node_post, a3_post, i_post1]
    simp [a2_post, a1_post1, adrsS,
      Spec.Adrs.setTypeAndClear, Spec.WOTS_HASH, address.WOTS_HASH, Spec.TREE, address.TREE]

end slhdsa
