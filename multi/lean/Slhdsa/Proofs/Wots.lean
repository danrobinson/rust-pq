import Slhdsa.Proofs.Hash
import Slhdsa.Proofs.Util
open Aeneas Aeneas.Std Result

/-! WOTS+ (FIPS 205 §5). -/

namespace slhdsa

/-- `Vec::extend_from_slice` appends (bytes). -/
@[local step]
theorem extend_u8_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (by intros; simp [liftFun1]))
  intro l hl
  simp [hl]

/-- `Vec::extend_from_slice` appends (words). -/
@[local step]
theorem extend_u32_spec (v : alloc.vec.Vec U32) (s : Slice U32)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU32 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (by intros; simp [liftFun1]))
  intro l hl
  simp [hl]

theorem W_eq : params.W = 16#u32 := by with_unfolding_all rfl
theorem LEN2_eq : params.LEN2 = 3#usize := by with_unfolding_all rfl
theorem LG_W_eq : params.LG_W = 4#u32 := by with_unfolding_all rfl

/-- `n ≤ 32` for a valid parameter set. -/
theorem n_le_32 (p : params.Params) (hv : (paramsS p).Valid) : p.n.val ≤ 32 := by
  have hn := hv.n_cases
  simp at hn
  omega

theorem chain_loop_spec (p : params.Params) (x : Slice U8) (i e : U32) (pk : Slice U8)
    (a : address.Adrs) (tmp : alloc.vec.Vec U8) (j : U32)
    (hv : (paramsS p).Valid) (hpk : pk.length = p.n.val)
    (hij : i.val ≤ j.val) (hje : j.val ≤ e.val) (hlen : tmp.length = p.n.val)
    (hinv : bytes tmp.val = (List.range (j.val - i.val)).foldl
      (fun t k => Spec.F (paramsS p) (bytes pk.val) { adrsS a with word3 := i.val + k } t)
      (bytes x.val)) :
    wots.chain_loop p pk a tmp j e ⦃ r =>
      bytes r.val = (List.range (e.val - i.val)).foldl
        (fun t k => Spec.F (paramsS p) (bytes pk.val) { adrsS a with word3 := i.val + k } t)
        (bytes x.val) ∧
      r.length = p.n.val ⦄ := by
  have hn32 := n_le_32 p hv
  unfold wots.chain_loop
  apply loop.spec_decr_nat (measure := fun (q : alloc.vec.Vec U8 × U32) => e.val - q.2.val)
    (inv := fun q => i.val ≤ q.2.val ∧ q.2.val ≤ e.val ∧ q.1.length = p.n.val ∧
      bytes q.1.val = (List.range (q.2.val - i.val)).foldl
        (fun t k => Spec.F (paramsS p) (bytes pk.val) { adrsS a with word3 := i.val + k } t)
        (bytes x.val))
  · rintro ⟨tmp, j⟩ ⟨h1, h2, hl, h3⟩
    simp only [wots.chain_loop.body]
    simp only at h1 h2 hl h3
    simp only [step_simps]
    spec_split
    · let* ⟨ a1, a1_post ⟩ ← with_word3_spec
      let* ⟨ tmp1, tmp1_post, tmp1_len ⟩ ← thash_f_spec
      let* ⟨ j1, j1_post ⟩ ← U32.add_spec
      refine ⟨by scalar_tac, by scalar_tac, tmp1_len, ?_, by scalar_tac⟩
      have hj : j1.val - i.val = (j.val - i.val) + 1 := by scalar_tac
      have hk : i.val + (j.val - i.val) = j.val := by scalar_tac
      rw [hj, List.range_succ, List.foldl_append, ← h3, tmp1_post, a1_post]
      simp [adrsS, hk]
    · simp only [step_simps]
      have : j.val = e.val := by scalar_tac
      rw [this] at h3
      exact ⟨h3, hl⟩
  · exact ⟨hij, hje, hlen, hinv⟩

@[step]
theorem chain_spec (p : params.Params) (x : Slice U8) (i s : U32) (pk : Slice U8) (a : address.Adrs)
    (hv : (paramsS p).Valid) (hx : x.length = p.n.val) (hpk : pk.length = p.n.val)
    (h : i.val + s.val ≤ U32.max) :
    wots.chain p x i s pk a ⦃ r =>
      bytes r.val = Spec.chain (paramsS p) (bytes x.val) i.val s.val (bytes pk.val) (adrsS a) ∧
      r.length = p.n.val ⦄ := by
  have hn32 := n_le_32 p hv
  unfold wots.chain
  let* ⟨ tmp, tmp_post ⟩ ← extend_u8_spec
  let* ⟨ e, e_post ⟩ ← U32.add_spec
  have hs : e.val - i.val = s.val := by scalar_tac
  have htv : tmp.val = x.val := tmp_post.trans (List.nil_append _)
  have := chain_loop_spec p x i e pk a tmp i hv hpk (Nat.le_refl _) (by rw [e_post]; omega)
    (by show tmp.val.length = _; rw [htv]; exact hx) (by rw [htv, Nat.sub_self]; rfl)
  simp only [Spec.chain, ← hs]
  exact this

theorem wots_digits_loop_spec (len1 : Usize) (msg : alloc.vec.Vec U32) (csum : U32) (i : Usize)
    (hlen : msg.length = len1.val) (hl64 : len1.val ≤ 64) (hdig : ∀ d ∈ msg.val, d.val < 16)
    (hi : i.val ≤ len1.val)
    (hinv : csum.val = ((nats msg.val).take i.val).foldl (fun c x => c + (16 - 1 - x)) 0)
    (hb : csum.val ≤ 15 * i.val) :
    wots.wots_digits_loop len1 msg csum i ⦃ r =>
      r.val = (nats msg.val).foldl (fun c x => c + (16 - 1 - x)) 0 ∧ r.val ≤ 960 ⦄ := by
  unfold wots.wots_digits_loop
  apply loop.spec_decr_nat (measure := fun (q : U32 × Usize) => len1.val - q.2.val)
    (inv := fun q => q.2.val ≤ len1.val ∧
      q.1.val = ((nats msg.val).take q.2.val).foldl (fun c x => c + (16 - 1 - x)) 0 ∧
      q.1.val ≤ 15 * q.2.val)
  · rintro ⟨csum, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.wots_digits_loop.body, W_eq]
    simp only at h1 h2 h3
    simp only [step_simps]
    spec_split
    · have hil : i.val < msg.val.length := by scalar_tac
      have hd : (msg.val[i.val]).val < 16 := hdig _ (List.getElem_mem hil)
      let* ⟨ i1, i1_post, i1_post1 ⟩ ← U32.sub_spec
      let* ⟨ i2, i2_post ⟩ ← alloc.vec.Vec.index_usize_spec
      let* ⟨ i3, i3_post, i3_post1 ⟩ ← U32.sub_spec
      let* ⟨ csum1, csum1_post ⟩ ← U32.add_spec
      let* ⟨ i4, i4_post ⟩ ← Usize.add_spec
      refine ⟨by scalar_tac, ?_, by scalar_tac, by scalar_tac⟩
      have hn : i.val < (nats msg.val).length := by simp [nats]; scalar_tac
      rw [i4_post, List.take_add_one, List.foldl_append, ← h2, List.getElem?_eq_getElem hn]
      simp [nats, csum1_post, i3_post, i1_post, i2_post]
    · simp only [step_simps]
      have hi32 : i.val = len1.val := by scalar_tac
      have : List.take i.val (nats msg.val) = nats msg.val := by
        apply List.take_of_length_le; simp [nats]; scalar_tac
      rw [this] at h2
      exact ⟨h2, by scalar_tac⟩
  · exact ⟨hi, hinv, hb⟩

@[step]
theorem wots_digits_spec (p : params.Params) (m : Slice U8)
    (hv : (paramsS p).Valid) (hm : m.length = p.n.val) :
    wots.wots_digits p m ⦃ r =>
      nats r.val = Spec.wotsDigits (paramsS p) (bytes m.val) ∧ r.length = 2 * p.n.val + 3 ∧
      ∀ d ∈ r.val, d.val < 16 ⦄ := by
  have hn32 := n_le_32 p hv
  unfold wots.wots_digits
  simp only [LG_W_eq, LEN2_eq]
  let* ⟨ len1, len1_post, len1_post1 ⟩ ← len1_spec
  let* ⟨ msg, msg_post, msg_post1, msg_post2 ⟩ ← base_2b_spec
  let* ⟨ csum, csum_post, csum_le ⟩ ← wots_digits_loop_spec
  · simp
  let* ⟨ csum1, csum1_post, csum1_post1 ⟩ ← U32.ShiftLeft_IScalar_spec
  let* ⟨ i, i_post, i_post1 ⟩ ← U32.ShiftRight_IScalar_spec
  let* ⟨ i1, i1_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i2, i2_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ tail, tail_post, tail_post1, tail_post2 ⟩ ← base_2b_spec
  have hbytes : bytes s1.val = Spec.toByte (csum.val <<< 4) 2 := by
    simp [s1_post, Spec.toByte, List.range, List.range.loop, i1_post, i2_post]
    constructor
    · apply BitVec.eq_of_toNat_eq
      simp [i_post1, csum1_post1, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
      omega
    · apply BitVec.eq_of_toNat_eq
      simp [csum1_post1, Nat.shiftLeft_eq]
  let* ⟨ r, r_post ⟩ ← extend_u32_spec
  rw [vec_deref_val] at r_post
  refine ⟨?_, ?_, ?_⟩
  · simp only [Spec.wotsDigits, r_post, nats, List.map_append, len1_eq p hv, len2_eq p hv,
      w_eq p, paramsS_lgw]
    simp only [nats] at msg_post tail_post csum_post
    rw [msg_post, tail_post, hbytes, csum_post, msg_post, len1_post]
  · simp [r_post]; scalar_tac
  · intro d hd
    simp [r_post] at hd
    rcases hd with hd | hd
    · exact msg_post2 d hd
    · exact tail_post2 d hd

theorem WOTS_PRF_eq : address.WOTS_PRF = 5#u32 := by with_unfolding_all rfl
theorem WOTS_PK_eq : address.WOTS_PK = 1#u32 := by with_unfolding_all rfl

theorem adrsS_sk (adrs a sk_adrs : address.Adrs)
    (ha : a = ⟨adrs.layer, adrs.tree, address.WOTS_PRF, 0#u32, 0#u32, 0#u32⟩)
    (hs : sk_adrs = ⟨a.layer, a.tree, a.typ, adrs.keypair, a.word2, a.word3⟩) :
    adrsS sk_adrs = Spec.wotsSkAdrs (adrsS adrs) := by
  subst ha; subst hs
  simp [adrsS, Spec.wotsSkAdrs, Spec.Adrs.setTypeAndClear, Spec.WOTS_PRF, WOTS_PRF_eq]

theorem adrsS_pk (adrs a pk_adrs : address.Adrs)
    (ha : a = ⟨adrs.layer, adrs.tree, address.WOTS_PK, 0#u32, 0#u32, 0#u32⟩)
    (hs : pk_adrs = ⟨a.layer, a.tree, a.typ, adrs.keypair, a.word2, a.word3⟩) :
    adrsS pk_adrs = Spec.wotsPkAdrs (adrsS adrs) := by
  subst ha; subst hs
  simp [adrsS, Spec.wotsPkAdrs, Spec.Adrs.setTypeAndClear, Spec.WOTS_PK, WOTS_PK_eq]

/-- Length bookkeeping for the three `len`-iteration loops: `n * i` stays small. -/
theorem wots_acc_bound (n i L : Nat) (hn : n ≤ 32) (hL : L = 2 * n + 3) (hi : i ≤ L) :
    n * i ≤ 2144 := by
  have h1 : n * i ≤ 32 * 67 := Nat.mul_le_mul hn (by omega)
  omega

/-- One iteration of the `wots_pkGen` loop in the specification. -/
def pkGenStep (P : Spec.Params) (sk pk : Spec.Bytes) (a : Spec.Adrs) (i : Nat) : Spec.Bytes :=
  Spec.chain P (Spec.PRF P pk sk { Spec.wotsSkAdrs a with word2 := i }) 0 (P.w - 1) pk
    { a with word2 := i }

theorem wots_pk_gen_loop_spec (p : params.Params) (sk_seed pk_seed : Slice U8)
    (adrs sk_adrs : address.Adrs) (len : U32) (tmp : alloc.vec.Vec U8) (i : U32)
    (hv : (paramsS p).Valid) (hskl : sk_seed.length = p.n.val) (hpkl : pk_seed.length = p.n.val)
    (hL : len.val = 2 * p.n.val + 3)
    (hsk : adrsS sk_adrs = Spec.wotsSkAdrs (adrsS adrs)) (hi : i.val ≤ len.val)
    (hlen : tmp.length = p.n.val * i.val)
    (hinv : bytes tmp.val = (List.range i.val).flatMap
      (pkGenStep (paramsS p) (bytes sk_seed.val) (bytes pk_seed.val) (adrsS adrs))) :
    wots.wots_pk_gen_loop p sk_seed pk_seed adrs.layer adrs.tree adrs.typ adrs.keypair adrs.word2
        adrs.word3 sk_adrs len tmp i ⦃ r =>
      bytes r.val = (List.range len.val).flatMap
        (pkGenStep (paramsS p) (bytes sk_seed.val) (bytes pk_seed.val) (adrsS adrs)) ∧
      r.length = p.n.val * len.val ⦄ := by
  have hn32 := n_le_32 p hv
  unfold wots.wots_pk_gen_loop
  apply loop.spec_decr_nat (measure := fun (q : alloc.vec.Vec U8 × U32) => len.val - q.2.val)
    (inv := fun q => q.2.val ≤ len.val ∧ q.1.length = p.n.val * q.2.val ∧
      bytes q.1.val = (List.range q.2.val).flatMap
        (pkGenStep (paramsS p) (bytes sk_seed.val) (bytes pk_seed.val) (adrsS adrs)))
  · rintro ⟨tmp, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.wots_pk_gen_loop.body, W_eq]
    simp only at h1 h2 h3
    simp only [step_simps]
    have hacc := wots_acc_bound p.n.val i.val len.val hn32 hL h1
    spec_split
    · let* ⟨ a, a_post ⟩ ← with_word2_spec
      let* ⟨ sk, sk_post, sk_len ⟩ ← thash_f_spec
      let* ⟨ i8, i8_post, i8_post1 ⟩ ← U32.sub_spec
      let* ⟨ a1, a1_post ⟩ ← with_word2_spec
      let* ⟨ t, t_post, t_len ⟩ ← chain_spec
      let* ⟨ tmp1, tmp1_post ⟩ ← extend_u8_spec
      let* ⟨ i9, i9_post ⟩ ← U32.add_spec
      have ha : adrsS a = { Spec.wotsSkAdrs (adrsS adrs) with word2 := i.val } := by
        rw [← hsk, a_post]; rfl
      have ha1 : adrsS a1 = { adrsS adrs with word2 := i.val } := by rw [a1_post]; rfl
      have h8 : i8.val = (paramsS p).w - 1 := by simp [w_eq, i8_post]
      have htl : t.val.length = p.n.val := t_len
      have h2' : tmp.val.length = p.n.val * i.val := h2
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp [alloc.vec.Vec.length, tmp1_post, htl, h2', i9_post, Nat.mul_succ]
      · rw [i9_post, List.range_succ, List.flatMap_append, ← h3, tmp1_post]
        simp [pkGenStep, t_post, sk_post, ha, ha1, h8, PRF_eq_F]
    · simp only [step_simps]
      have : i.val = len.val := by scalar_tac
      rw [this] at h3 h2
      exact ⟨h3, h2⟩
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem wots_pk_gen_spec (p : params.Params) (sk pk : Slice U8) (a : address.Adrs)
    (hv : (paramsS p).Valid) (hsk : sk.length = p.n.val) (hpk : pk.length = p.n.val) :
    wots.wots_pk_gen p sk pk a ⦃ r =>
      bytes r.val = Spec.wotsPkGen (paramsS p) (bytes sk.val) (bytes pk.val) (adrsS a) ∧
      r.length = p.n.val ⦄ := by
  rename' a => adrs
  have hn32 := n_le_32 p hv
  unfold wots.wots_pk_gen
  simp only [step_simps]
  let* ⟨ a, a_post, a_post1 ⟩ ← with_type_spec
  let* ⟨ sk_adrs, sk_adrs_post ⟩ ← with_keypair_spec
  let* ⟨ l, l_post, l_post1 ⟩ ← len_spec
  let* ⟨ len, len_post ⟩ ← UScalar.cast.step_spec
  have hL : len.val = 2 * p.n.val + 3 := by
    rw [len_post]; simp [l_post]; scalar_tac
  let* ⟨ tmp, tmp_post, tmp_len ⟩ ← wots_pk_gen_loop_spec
  · exact adrsS_sk adrs a sk_adrs a_post1 sk_adrs_post
  · simp
  let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
  let* ⟨ pk_adrs, pk_adrs_post ⟩ ← with_keypair_spec
  have hacc := wots_acc_bound p.n.val len.val len.val hn32 hL (Nat.le_refl _)
  let* ⟨ r, r_post, r_len ⟩ ← thash_h_spec
  refine ⟨?_, r_len⟩
  rw [r_post, adrsS_pk adrs a1 pk_adrs a1_post1 pk_adrs_post, vec_deref_val, tmp_post, hL,
    ← len_eq p hv]
  rfl

/-- One iteration of the `wots_sign` loop in the specification. -/
def signStep (P : Spec.Params) (sk pk : Spec.Bytes) (a : Spec.Adrs) (digits : List Nat) (i : Nat) :
    Spec.Bytes :=
  Spec.chain P (Spec.PRF P pk sk { Spec.wotsSkAdrs a with word2 := i }) 0 digits[i]! pk
    { a with word2 := i }

theorem wots_sign_loop_spec (p : params.Params) (sk_seed pk_seed : Slice U8)
    (adrs sk_adrs : address.Adrs) (msg : alloc.vec.Vec U32) (len : U32)
    (sig : alloc.vec.Vec U8) (i : U32)
    (hv : (paramsS p).Valid) (hskl : sk_seed.length = p.n.val) (hpkl : pk_seed.length = p.n.val)
    (hL : len.val = 2 * p.n.val + 3)
    (hsk : adrsS sk_adrs = Spec.wotsSkAdrs (adrsS adrs)) (hmsg : msg.length = len.val)
    (hi : i.val ≤ len.val) (hlen : sig.length = p.n.val * i.val)
    (hinv : bytes sig.val = (List.range i.val).flatMap
      (signStep (paramsS p) (bytes sk_seed.val) (bytes pk_seed.val) (adrsS adrs) (nats msg.val))) :
    wots.wots_sign_loop p sk_seed pk_seed adrs.layer adrs.tree adrs.typ adrs.keypair adrs.word2
        adrs.word3 msg sk_adrs len sig i ⦃ r =>
      bytes r.val = (List.range len.val).flatMap
        (signStep (paramsS p) (bytes sk_seed.val) (bytes pk_seed.val) (adrsS adrs)
          (nats msg.val)) ∧
      r.length = p.n.val * len.val ⦄ := by
  have hn32 := n_le_32 p hv
  unfold wots.wots_sign_loop
  apply loop.spec_decr_nat (measure := fun (q : alloc.vec.Vec U8 × U32) => len.val - q.2.val)
    (inv := fun q => q.2.val ≤ len.val ∧ q.1.length = p.n.val * q.2.val ∧
      bytes q.1.val = (List.range q.2.val).flatMap
        (signStep (paramsS p) (bytes sk_seed.val) (bytes pk_seed.val) (adrsS adrs)
          (nats msg.val)))
  · rintro ⟨sig, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.wots_sign_loop.body]
    simp only at h1 h2 h3
    simp only [step_simps]
    have hacc := wots_acc_bound p.n.val i.val len.val hn32 hL h1
    spec_split
    · let* ⟨ a, a_post ⟩ ← with_word2_spec
      let* ⟨ sk, sk_post, sk_len ⟩ ← thash_f_spec
      let* ⟨ i8, i8_post ⟩ ← UScalar.cast.step_spec
      have h8 : i8.val = i.val := by simp [i8_post]
      let* ⟨ i9, i9_post ⟩ ← alloc.vec.Vec.index_usize_spec
      let* ⟨ a1, a1_post ⟩ ← with_word2_spec
      let* ⟨ t, t_post, t_len ⟩ ← chain_spec
      let* ⟨ sig1, sig1_post ⟩ ← extend_u8_spec
      let* ⟨ i10, i10_post ⟩ ← U32.add_spec
      have ha : adrsS a = { Spec.wotsSkAdrs (adrsS adrs) with word2 := i.val } := by
        rw [← hsk, a_post]; rfl
      have ha1 : adrsS a1 = { adrsS adrs with word2 := i.val } := by rw [a1_post]; rfl
      have hil : i.val < msg.val.length := by scalar_tac
      have hd : (nats msg.val)[i.val]! = i9.val := by simp [nats, i9_post, h8, hil]
      have htl : t.val.length = p.n.val := t_len
      have h2' : sig.val.length = p.n.val * i.val := h2
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp [alloc.vec.Vec.length, sig1_post, htl, h2', i10_post, Nat.mul_succ]
      · rw [i10_post, List.range_succ, List.flatMap_append, ← h3, sig1_post]
        simp [signStep, t_post, sk_post, ha, ha1, hd, PRF_eq_F]
    · simp only [step_simps]
      have : i.val = len.val := by scalar_tac
      rw [this] at h3 h2
      exact ⟨h3, h2⟩
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem wots_sign_spec (p : params.Params) (m sk pk : Slice U8) (a : address.Adrs)
    (hv : (paramsS p).Valid) (hm : m.length = p.n.val) (hsk : sk.length = p.n.val)
    (hpk : pk.length = p.n.val) :
    wots.wots_sign p m sk pk a ⦃ r =>
      bytes r.val = Spec.wotsSign (paramsS p) (bytes m.val) (bytes sk.val) (bytes pk.val) (adrsS a) ∧
      r.length = (2 * p.n.val + 3) * p.n.val ⦄ := by
  rename' a => adrs
  have hn32 := n_le_32 p hv
  unfold wots.wots_sign
  let* ⟨ msg, msg_post, msg_len, msg_dig ⟩ ← wots_digits_spec
  let* ⟨ a, a_post, a_post1 ⟩ ← with_type_spec
  let* ⟨ sk_adrs, sk_adrs_post ⟩ ← with_keypair_spec
  let* ⟨ l, l_post, l_post1 ⟩ ← len_spec
  let* ⟨ len, len_post ⟩ ← UScalar.cast.step_spec
  have hL : len.val = 2 * p.n.val + 3 := by
    rw [len_post]; simp [l_post]; scalar_tac
  let* ⟨ r, r_post, r_len ⟩ ← wots_sign_loop_spec
  · exact adrsS_sk adrs a sk_adrs a_post1 sk_adrs_post
  · simp
  refine ⟨?_, by rw [r_len, hL, Nat.mul_comm]⟩
  rw [r_post, msg_post, hL, ← len_eq p hv]
  rfl

/-- One iteration of the `wots_pkFromSig` loop in the specification. -/
def fromSigStep (P : Spec.Params) (sig pk : Spec.Bytes) (a : Spec.Adrs) (digits : List Nat)
    (i : Nat) : Spec.Bytes :=
  Spec.chain P (Spec.block P sig i) digits[i]! (P.w - 1 - digits[i]!) pk { a with word2 := i }

theorem wots_pk_from_sig_loop_spec (p : params.Params) (sig pk_seed : Slice U8)
    (adrs : address.Adrs) (msg : alloc.vec.Vec U32) (len : U32) (tmp : alloc.vec.Vec U8) (i : U32)
    (hv : (paramsS p).Valid) (hpkl : pk_seed.length = p.n.val)
    (hL : len.val = 2 * p.n.val + 3)
    (hsig : len.val * p.n.val ≤ sig.length) (hmsg : msg.length = len.val)
    (hdig : ∀ d ∈ msg.val, d.val < 16)
    (hi : i.val ≤ len.val) (hlen : tmp.length = p.n.val * i.val)
    (hinv : bytes tmp.val = (List.range i.val).flatMap
      (fromSigStep (paramsS p) (bytes sig.val) (bytes pk_seed.val) (adrsS adrs) (nats msg.val))) :
    wots.wots_pk_from_sig_loop p sig pk_seed adrs msg len tmp i ⦃ r =>
      r.1 = p ∧
      bytes r.2.val = (List.range len.val).flatMap
        (fromSigStep (paramsS p) (bytes sig.val) (bytes pk_seed.val) (adrsS adrs)
          (nats msg.val)) ∧
      r.2.length = p.n.val * len.val ⦄ := by
  have hn32 := n_le_32 p hv
  unfold wots.wots_pk_from_sig_loop
  apply loop.spec_decr_nat (measure := fun (q : alloc.vec.Vec U8 × U32) => len.val - q.2.val)
    (inv := fun q => q.2.val ≤ len.val ∧ q.1.length = p.n.val * q.2.val ∧
      bytes q.1.val = (List.range q.2.val).flatMap
        (fromSigStep (paramsS p) (bytes sig.val) (bytes pk_seed.val) (adrsS adrs)
          (nats msg.val)))
  · rintro ⟨tmp, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.wots_pk_from_sig_loop.body, W_eq]
    simp only at h1 h2 h3
    simp only [step_simps]
    have hacc := wots_acc_bound p.n.val i.val len.val hn32 hL h1
    spec_split
    · let* ⟨ i2, i2_post ⟩ ← UScalar.cast.step_spec
      have h2' : i2.val = i.val := by simp [i2_post]
      let* ⟨ d, d_post ⟩ ← alloc.vec.Vec.index_usize_spec
      let* ⟨ i3, i3_post ⟩ ← UScalar.cast.step_spec
      have h3' : i3.val = i.val := by simp [i3_post]
      have hblk : (i3.val + 1) * p.n.val ≤ sig.length := by
        have : (i3.val + 1) * p.n.val ≤ len.val * p.n.val :=
          Nat.mul_le_mul_right _ (by scalar_tac)
        omega
      let* ⟨ x, x_post, x_len ⟩ ← block_spec
      let* ⟨ i4, i4_post, i4_post1 ⟩ ← U32.sub_spec
      have hd16 : d.val < 16 := hdig d (by rw [d_post]; exact List.getElem_mem _)
      let* ⟨ i5, i5_post, i5_post1 ⟩ ← U32.sub_spec
      let* ⟨ a1, a1_post ⟩ ← with_word2_spec
      let* ⟨ t, t_post, t_len ⟩ ← chain_spec
      let* ⟨ tmp1, tmp1_post ⟩ ← extend_u8_spec
      let* ⟨ i6, i6_post ⟩ ← U32.add_spec
      have ha1 : adrsS a1 = { adrsS adrs with word2 := i.val } := by rw [a1_post]; rfl
      have hil : i.val < msg.val.length := by scalar_tac
      have hdd : (nats msg.val)[i.val]! = d.val := by simp [nats, d_post, h2', hil]
      have h5 : i5.val = (paramsS p).w - 1 - d.val := by simp [w_eq, i5_post, i4_post]
      have hx : bytes x.val = Spec.block (paramsS p) (bytes sig.val) i.val := by
        apply bytes_block; rw [x_post, h3']
      have htl : t.val.length = p.n.val := t_len
      have h2'' : tmp.val.length = p.n.val * i.val := h2
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp [alloc.vec.Vec.length, tmp1_post, htl, h2'', i6_post, Nat.mul_succ]
      · rw [i6_post, List.range_succ, List.flatMap_append, ← h3, tmp1_post]
        simp [fromSigStep, t_post, hx, ha1, h5, hdd]
    · simp only [step_simps]
      have : i.val = len.val := by scalar_tac
      rw [this] at h3 h2
      exact ⟨h3, h2⟩
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem wots_pk_from_sig_spec (p : params.Params) (sig m pk : Slice U8) (a : address.Adrs)
    (hv : (paramsS p).Valid) (h : (2 * p.n.val + 3) * p.n.val ≤ sig.length)
    (hm : m.length = p.n.val) (hpk : pk.length = p.n.val) :
    wots.wots_pk_from_sig p sig m pk a ⦃ r =>
      bytes r.val = Spec.wotsPkFromSig (paramsS p) (bytes sig.val) (bytes m.val) (bytes pk.val)
        (adrsS a) ∧
      r.length = p.n.val ⦄ := by
  rename' a => adrs
  have hn32 := n_le_32 p hv
  unfold wots.wots_pk_from_sig
  simp only [step_simps]
  let* ⟨ msg, msg_post, msg_len, msg_dig ⟩ ← wots_digits_spec
  let* ⟨ l, l_post, l_post1 ⟩ ← len_spec
  let* ⟨ len, len_post ⟩ ← UScalar.cast.step_spec
  have hL : len.val = 2 * p.n.val + 3 := by
    rw [len_post]; simp [l_post]; scalar_tac
  let* ⟨ p1, tmp, p1_post, tmp_post, tmp_len ⟩ ← wots_pk_from_sig_loop_spec
  · simp
  subst p1
  let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
  let* ⟨ pk_adrs, pk_adrs_post ⟩ ← with_keypair_spec
  have hacc := wots_acc_bound p.n.val len.val len.val hn32 hL (Nat.le_refl _)
  let* ⟨ r, r_post, r_len ⟩ ← thash_h_spec
  refine ⟨?_, r_len⟩
  rw [msg_post] at tmp_post
  rw [r_post, adrsS_pk adrs a1 pk_adrs a1_post1 pk_adrs_post, vec_deref_val, tmp_post, hL,
    ← len_eq p hv]
  rfl

end slhdsa
