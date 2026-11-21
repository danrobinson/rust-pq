import Slhdsa.Proofs.Hash
import Slhdsa.Proofs.Util
open Aeneas Aeneas.Std Result

/-! WOTS+. -/

namespace slhdsa

/-- `Vec::extend_from_slice` appends (bytes). -/
@[local step]
theorem extend_u8_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  step with List.clone_spec
  simp [*]

/-- `Vec::extend_from_slice` appends (words). -/
@[local step]
theorem extend_u32_spec (v : alloc.vec.Vec U32) (s : Slice U32)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU32 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  step with List.clone_spec
  simp [*]

theorem W_eq : params.W = 16#u32 := by with_unfolding_all rfl
theorem LEN1_eq : params.LEN1 = 32#usize := by with_unfolding_all rfl
theorem LEN2_eq : params.LEN2 = 3#usize := by with_unfolding_all rfl
theorem LEN_eq : params.LEN = 35#usize := by with_unfolding_all rfl
theorem LG_W_eq : params.LG_W = 4#u32 := by with_unfolding_all rfl

theorem chain_loop_spec (x : Array U8 16#usize) (i e : U32) (pk : hash.Seed) (hpk : SeedOk pk)
    (a : address.Adrs) (tmp : Array U8 16#usize) (j : U32)
    (hij : i.val ≤ j.val) (hje : j.val ≤ e.val)
    (hinv : bytes tmp.val = (List.range (j.val - i.val)).foldl
      (fun t k => Spec.F (bytes pk.pk_seed.val) { adrsS a with word3 := i.val + k } t) (bytes x.val)) :
    wots.chain_loop pk a tmp j e ⦃ r =>
      bytes r.val = (List.range (e.val - i.val)).foldl
        (fun t k => Spec.F (bytes pk.pk_seed.val) { adrsS a with word3 := i.val + k } t) (bytes x.val) ⦄ := by
  unfold wots.chain_loop
  apply loop.spec_decr_nat (measure := fun (p : Array U8 16#usize × U32) => e.val - p.2.val)
    (inv := fun p => i.val ≤ p.2.val ∧ p.2.val ≤ e.val ∧
      bytes p.1.val = (List.range (p.2.val - i.val)).foldl
        (fun t k => Spec.F (bytes pk.pk_seed.val) { adrsS a with word3 := i.val + k } t) (bytes x.val))
  · rintro ⟨tmp, j⟩ ⟨h1, h2, h3⟩
    simp only [wots.chain_loop.body]
    simp only at h1 h2 h3
    step*
    · refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have hj : j1.val - i.val = (j.val - i.val) + 1 := by scalar_tac
      have hk : i.val + (j.val - i.val) = j.val := by scalar_tac
      rw [hj, List.range_succ, List.foldl_append, ← h3, tmp1_post, s_post, a_post]
      simp [Spec.F, adrsS, hk]
  · exact ⟨hij, hje, hinv⟩

@[step]
theorem chain_spec (x : Array U8 16#usize) (i s : U32) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (h : i.val + s.val ≤ U32.max) :
    wots.chain x i s pk a ⦃ r =>
      bytes r.val = Spec.chain (bytes x.val) i.val s.val (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  unfold wots.chain
  step
  have hs : «end».val - i.val = s.val := by scalar_tac
  have := chain_loop_spec x i «end» pk hpk a x i (Nat.le_refl _) (by scalar_tac) (by simp)
  simp only [Spec.chain, ← hs]
  exact this

theorem wots_digits_loop_spec (msg : alloc.vec.Vec U32) (csum : U32) (i : Usize)
    (hlen : msg.length = 32) (hdig : ∀ d ∈ msg.val, d.val < 16)
    (hi : i.val ≤ 32)
    (hinv : csum.val = ((nats msg.val).take i.val).foldl (fun c x => c + (Spec.w - 1 - x)) 0)
    (hb : csum.val ≤ 15 * i.val) :
    wots.wots_digits_loop msg csum i ⦃ r =>
      r.val = (nats msg.val).foldl (fun c x => c + (Spec.w - 1 - x)) 0 ∧ r.val ≤ 480 ⦄ := by
  unfold wots.wots_digits_loop
  apply loop.spec_decr_nat (measure := fun (p : U32 × Usize) => 32 - p.2.val)
    (inv := fun p => p.2.val ≤ 32 ∧
      p.1.val = ((nats msg.val).take p.2.val).foldl (fun c x => c + (Spec.w - 1 - x)) 0 ∧
      p.1.val ≤ 15 * p.2.val)
  · rintro ⟨csum, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.wots_digits_loop.body, W_eq, LEN1_eq]
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
      simp [nats, Spec.w, csum1_post, i3_post, i1_post, i2_post]
    · simp only [step_simps]
      have hi32 : i.val = 32 := by scalar_tac
      have : List.take i.val (nats msg.val) = nats msg.val := by
        apply List.take_of_length_le; simp [nats]; scalar_tac
      rw [this] at h2
      exact ⟨h2, by scalar_tac⟩
  · exact ⟨hi, hinv, hb⟩

@[step]
theorem wots_digits_spec (m : Array U8 16#usize) :
    wots.wots_digits m ⦃ r =>
      nats r.val = Spec.wotsDigits (bytes m.val) ∧ r.length = 35 ∧ ∀ d ∈ r.val, d.val < 16 ⦄ := by
  unfold wots.wots_digits
  simp only [LG_W_eq, LEN1_eq, LEN2_eq]
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
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
  have hderef : tail.deref.val = tail.val := by simp [alloc.vec.Vec.deref]
  let* ⟨ r, r_post ⟩ ← extend_u32_spec
  rw [hderef] at r_post
  refine ⟨?_, ?_, ?_⟩
  · simp only [Spec.wotsDigits, r_post, nats, List.map_append]
    simp only [nats] at msg_post tail_post csum_post
    rw [msg_post, tail_post, hbytes, csum_post, msg_post, s_post]
    simp [Spec.lgw, Spec.len1, Spec.len2]
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

/-- One iteration of the `wots_pkGen` loop in the specification. -/
def pkGenStep (sk pk : Spec.Bytes) (a : Spec.Adrs) (i : Nat) : Spec.Bytes :=
  Spec.chain (Spec.PRF pk sk { Spec.wotsSkAdrs a with word2 := i }) 0 (Spec.w - 1) pk
    { a with word2 := i }

theorem wots_pk_gen_loop_spec (sk_seed : Array U8 16#usize) (pk_seed : hash.Seed) (hpk_seed : SeedOk pk_seed) (adrs sk_adrs : address.Adrs)
    (tmp : alloc.vec.Vec U8) (i : U32)
    (hsk : adrsS sk_adrs = Spec.wotsSkAdrs (adrsS adrs)) (hi : i.val ≤ 35)
    (hlen : tmp.length = 16 * i.val)
    (hinv : bytes tmp.val =
      (List.range i.val).flatMap (pkGenStep (bytes sk_seed.val) (bytes pk_seed.pk_seed.val) (adrsS adrs))) :
    wots.wots_pk_gen_loop sk_seed pk_seed adrs.layer adrs.tree adrs.typ adrs.keypair adrs.word2
        adrs.word3 sk_adrs tmp i ⦃ r =>
      bytes r.val =
        (List.range 35).flatMap (pkGenStep (bytes sk_seed.val) (bytes pk_seed.pk_seed.val) (adrsS adrs)) ∧
      r.length = 560 ⦄ := by
  unfold wots.wots_pk_gen_loop
  apply loop.spec_decr_nat (measure := fun (p : alloc.vec.Vec U8 × U32) => 35 - p.2.val)
    (inv := fun p => p.2.val ≤ 35 ∧ p.1.length = 16 * p.2.val ∧
      bytes p.1.val =
        (List.range p.2.val).flatMap (pkGenStep (bytes sk_seed.val) (bytes pk_seed.pk_seed.val) (adrsS adrs)))
  · rintro ⟨tmp, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.wots_pk_gen_loop.body, W_eq, LEN_eq]
    simp only at h1 h2 h3
    simp only [step_simps]
    let* ⟨ i7, i7_post ⟩ ← UScalar.cast.step_spec
    have h7 : i7.val = 35 := by simp [i7_post]
    spec_split
    · let* ⟨ a, a_post ⟩ ← with_word2_spec
      let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ sk, sk_post ⟩ ← thash_short_spec
      let* ⟨ i8, i8_post, i8_post1 ⟩ ← U32.sub_spec
      let* ⟨ a1, a1_post ⟩ ← with_word2_spec
      let* ⟨ t, t_post ⟩ ← chain_spec
      let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ tmp1, tmp1_post ⟩ ← extend_u8_spec
      let* ⟨ i9, i9_post ⟩ ← U32.add_spec
      have ha : adrsS a = { Spec.wotsSkAdrs (adrsS adrs) with word2 := i.val } := by
        rw [← hsk, a_post]; rfl
      have ha1 : adrsS a1 = { adrsS adrs with word2 := i.val } := by rw [a1_post]; rfl
      have h8 : i8.val = Spec.w - 1 := by simp [Spec.w, i8_post]
      refine ⟨by scalar_tac, by simp [tmp1_post, s1_post]; scalar_tac, ?_, by scalar_tac⟩
      rw [i9_post, List.range_succ, List.flatMap_append, ← h3, tmp1_post]
      simp [pkGenStep, s1_post, t_post, sk_post, ha, ha1, h8, Spec.PRF, s_post]
    · simp only [step_simps]
      have : i.val = 35 := by scalar_tac
      rw [this] at h3 h2
      exact ⟨h3, by scalar_tac⟩
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem wots_pk_gen_spec (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) :
    wots.wots_pk_gen sk pk a ⦃ r =>
      bytes r.val = Spec.wotsPkGen (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  rename' a => adrs
  unfold wots.wots_pk_gen
  simp only [step_simps]
  let* ⟨ a, a_post, a_post1 ⟩ ← with_type_spec
  let* ⟨ sk_adrs, sk_adrs_post ⟩ ← with_keypair_spec
  let* ⟨ tmp, tmp_post, tmp_len ⟩ ← wots_pk_gen_loop_spec
  · exact adrsS_sk adrs a sk_adrs a_post1 sk_adrs_post
  · simp
  let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
  let* ⟨ pk_adrs, pk_adrs_post ⟩ ← with_keypair_spec
  let* ⟨ r, r_post ⟩ ← thash_spec
  have ht : bytes tmp.deref.val = bytes tmp.val := by simp [alloc.vec.Vec.deref]
  rw [r_post, adrsS_pk adrs a1 pk_adrs a1_post1 pk_adrs_post, ht, tmp_post]
  rfl

/-- One iteration of the `wots_sign` loop in the specification. -/
def signStep (sk pk : Spec.Bytes) (a : Spec.Adrs) (digits : List Nat) (i : Nat) : Spec.Bytes :=
  Spec.chain (Spec.PRF pk sk { Spec.wotsSkAdrs a with word2 := i }) 0 digits[i]! pk
    { a with word2 := i }

theorem wots_sign_loop_spec (sk_seed : Array U8 16#usize) (pk_seed : hash.Seed) (hpk_seed : SeedOk pk_seed) (adrs sk_adrs : address.Adrs)
    (msg : alloc.vec.Vec U32) (sig : alloc.vec.Vec U8) (i : U32)
    (hsk : adrsS sk_adrs = Spec.wotsSkAdrs (adrsS adrs)) (hmsg : msg.length = 35)
    (hi : i.val ≤ 35) (hlen : sig.length = 16 * i.val)
    (hinv : bytes sig.val = (List.range i.val).flatMap
      (signStep (bytes sk_seed.val) (bytes pk_seed.pk_seed.val) (adrsS adrs) (nats msg.val))) :
    wots.wots_sign_loop sk_seed pk_seed adrs.layer adrs.tree adrs.typ adrs.keypair adrs.word2
        adrs.word3 msg sk_adrs sig i ⦃ r =>
      bytes r.val = (List.range 35).flatMap
        (signStep (bytes sk_seed.val) (bytes pk_seed.pk_seed.val) (adrsS adrs) (nats msg.val)) ∧
      r.length = 560 ⦄ := by
  unfold wots.wots_sign_loop
  apply loop.spec_decr_nat (measure := fun (p : alloc.vec.Vec U8 × U32) => 35 - p.2.val)
    (inv := fun p => p.2.val ≤ 35 ∧ p.1.length = 16 * p.2.val ∧
      bytes p.1.val = (List.range p.2.val).flatMap
        (signStep (bytes sk_seed.val) (bytes pk_seed.pk_seed.val) (adrsS adrs) (nats msg.val)))
  · rintro ⟨sig, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.wots_sign_loop.body, LEN_eq]
    simp only at h1 h2 h3
    simp only [step_simps]
    let* ⟨ i7, i7_post ⟩ ← UScalar.cast.step_spec
    have h7 : i7.val = 35 := by simp [i7_post]
    spec_split
    · let* ⟨ a, a_post ⟩ ← with_word2_spec
      let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ sk, sk_post ⟩ ← thash_short_spec
      let* ⟨ i8, i8_post ⟩ ← UScalar.cast.step_spec
      let* ⟨ i9, i9_post ⟩ ← alloc.vec.Vec.index_usize_spec
      let* ⟨ a1, a1_post ⟩ ← with_word2_spec
      let* ⟨ t, t_post ⟩ ← chain_spec
      let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ sig1, sig1_post ⟩ ← extend_u8_spec
      let* ⟨ i10, i10_post ⟩ ← U32.add_spec
      have ha : adrsS a = { Spec.wotsSkAdrs (adrsS adrs) with word2 := i.val } := by
        rw [← hsk, a_post]; rfl
      have ha1 : adrsS a1 = { adrsS adrs with word2 := i.val } := by rw [a1_post]; rfl
      have h8 : i8.val = i.val := by simp [i8_post]
      have hil : i.val < msg.val.length := by scalar_tac
      have hd : (nats msg.val)[i.val]! = i9.val := by simp [nats, i9_post, h8, hil]
      refine ⟨by scalar_tac, by simp [sig1_post, s1_post]; scalar_tac, ?_, by scalar_tac⟩
      rw [i10_post, List.range_succ, List.flatMap_append, ← h3, sig1_post]
      simp [signStep, s1_post, t_post, sk_post, ha, ha1, hd, Spec.PRF, s_post]
    · simp only [step_simps]
      have : i.val = 35 := by scalar_tac
      rw [this] at h3 h2
      exact ⟨h3, by scalar_tac⟩
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem wots_sign_spec (m sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) :
    wots.wots_sign m sk pk a ⦃ r =>
      bytes r.val = Spec.wotsSign (bytes m.val) (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) ∧
      r.length = 560 ⦄ := by
  rename' a => adrs
  unfold wots.wots_sign
  let* ⟨ msg, msg_post, msg_len, msg_dig ⟩ ← wots_digits_spec
  let* ⟨ a, a_post, a_post1 ⟩ ← with_type_spec
  let* ⟨ sk_adrs, sk_adrs_post ⟩ ← with_keypair_spec
  let* ⟨ r, r_post, r_len ⟩ ← wots_sign_loop_spec
  · exact adrsS_sk adrs a sk_adrs a_post1 sk_adrs_post
  · simp
  refine ⟨?_, r_len⟩
  rw [r_post, msg_post]
  rfl

/-- One iteration of the `wots_pkFromSig` loop in the specification. -/
def fromSigStep (sig pk : Spec.Bytes) (a : Spec.Adrs) (digits : List Nat) (i : Nat) : Spec.Bytes :=
  Spec.chain (Spec.block sig i) digits[i]! (Spec.w - 1 - digits[i]!) pk { a with word2 := i }

theorem wots_pk_from_sig_loop_spec (sig : Slice U8) (pk_seed : hash.Seed) (hpk_seed : SeedOk pk_seed) (adrs : address.Adrs)
    (msg : alloc.vec.Vec U32) (tmp : alloc.vec.Vec U8) (i : U32)
    (hsig : 560 ≤ sig.length) (hmsg : msg.length = 35) (hdig : ∀ d ∈ msg.val, d.val < 16)
    (hi : i.val ≤ 35) (hlen : tmp.length = 16 * i.val)
    (hinv : bytes tmp.val = (List.range i.val).flatMap
      (fromSigStep (bytes sig.val) (bytes pk_seed.pk_seed.val) (adrsS adrs) (nats msg.val))) :
    wots.wots_pk_from_sig_loop sig pk_seed adrs msg tmp i ⦃ r =>
      bytes r.val = (List.range 35).flatMap
        (fromSigStep (bytes sig.val) (bytes pk_seed.pk_seed.val) (adrsS adrs) (nats msg.val)) ∧
      r.length = 560 ⦄ := by
  unfold wots.wots_pk_from_sig_loop
  apply loop.spec_decr_nat (measure := fun (p : alloc.vec.Vec U8 × U32) => 35 - p.2.val)
    (inv := fun p => p.2.val ≤ 35 ∧ p.1.length = 16 * p.2.val ∧
      bytes p.1.val = (List.range p.2.val).flatMap
        (fromSigStep (bytes sig.val) (bytes pk_seed.pk_seed.val) (adrsS adrs) (nats msg.val)))
  · rintro ⟨tmp, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.wots_pk_from_sig_loop.body, W_eq, LEN_eq]
    simp only at h1 h2 h3
    simp only [step_simps]
    let* ⟨ i7, i7_post ⟩ ← UScalar.cast.step_spec
    have h7 : i7.val = 35 := by simp [i7_post]
    spec_split
    · let* ⟨ i2, i2_post ⟩ ← UScalar.cast.step_spec
      let* ⟨ d, d_post ⟩ ← alloc.vec.Vec.index_usize_spec
      let* ⟨ i3, i3_post ⟩ ← UScalar.cast.step_spec
      let* ⟨ a, a_post, a_post1 ⟩ ← block_spec
      let* ⟨ i4, i4_post, i4_post1 ⟩ ← U32.sub_spec
      have hd16 : d.val < 16 := hdig d (by rw [d_post]; exact List.getElem_mem _)
      let* ⟨ i5, i5_post, i5_post1 ⟩ ← U32.sub_spec
      let* ⟨ a1, a1_post ⟩ ← with_word2_spec
      let* ⟨ t, t_post ⟩ ← chain_spec
      let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ tmp1, tmp1_post ⟩ ← extend_u8_spec
      let* ⟨ i6, i6_post ⟩ ← U32.add_spec
      have ha1 : adrsS a1 = { adrsS adrs with word2 := i.val } := by rw [a1_post]; rfl
      have h2' : i2.val = i.val := by simp [i2_post]
      have h3' : i3.val = i.val := by simp [i3_post]
      have hil : i.val < msg.val.length := by scalar_tac
      have hdd : (nats msg.val)[i.val]! = d.val := by simp [nats, d_post, h2', hil]
      have h5 : i5.val = Spec.w - 1 - d.val := by simp [Spec.w, i5_post, i4_post]
      refine ⟨by scalar_tac, by simp [tmp1_post, s_post]; scalar_tac, ?_, by scalar_tac⟩
      rw [i6_post, List.range_succ, List.flatMap_append, ← h3, tmp1_post]
      simp [fromSigStep, s_post, t_post, a_post1, ha1, h5, hdd, h3']
    · simp only [step_simps]
      have : i.val = 35 := by scalar_tac
      rw [this] at h3 h2
      exact ⟨h3, by scalar_tac⟩
  · exact ⟨hi, hlen, hinv⟩

@[step]
theorem wots_pk_from_sig_spec (sig : Slice U8) (m : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (h : 560 ≤ sig.length) :
    wots.wots_pk_from_sig sig m pk a ⦃ r =>
      bytes r.val = Spec.wotsPkFromSig (bytes sig.val) (bytes m.val) (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  rename' a => adrs
  unfold wots.wots_pk_from_sig
  simp only [step_simps]
  let* ⟨ msg, msg_post, msg_len, msg_dig ⟩ ← wots_digits_spec
  let* ⟨ tmp, tmp_post, tmp_len ⟩ ← wots_pk_from_sig_loop_spec
  · simp
  let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
  let* ⟨ pk_adrs, pk_adrs_post ⟩ ← with_keypair_spec
  let* ⟨ r, r_post ⟩ ← thash_spec
  rw [msg_post] at tmp_post
  have ht : bytes tmp.deref.val = bytes tmp.val := by simp [alloc.vec.Vec.deref]
  rw [r_post, adrsS_pk adrs a1 pk_adrs a1_post1 pk_adrs_post, ht, tmp_post]
  rfl

end slhdsa
