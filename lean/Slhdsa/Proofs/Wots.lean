import Slhdsa.Proofs.ChainTop
import Slhdsa.Proofs.Util
import Mathlib.Data.Nat.Count
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

/-! The secret values. -/

theorem forall_set_succ {α} [Inhabited α] (l : List α) (i : Nat) (x : α) (P : Nat → α → Prop)
    (hl : i < l.length) (h : ∀ j, j < i → P j l[j]!) (hx : P i x) :
    ∀ j, j < i + 1 → P j (l.set i x)[j]! := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
  · rw [getElem!_set_ne' _ _ _ _ (by omega)]; exact h j hj
  · subst hj; rw [getElem!_set_self' _ _ _ hl]; exact hx

theorem cast_u32_val (i : Usize) (h : i.val < 35) : (UScalar.cast .U32 i).val = i.val := by
  simp; scalar_tac

theorem sk_blocks_loop0_spec (sk_seed : Array U8 16#usize) (sk_adrs : address.Adrs)
    (blocks : Array (Array U8 64#usize) 35#usize) (i : Usize) (hi : i.val ≤ 35)
    (hinv : ∀ j, j < i.val → bytes (blocks.val[j]!).val =
      padFrom 64 ({ adrsS sk_adrs with word2 := j }.compress ++ bytes sk_seed.val)) :
    wots.sk_blocks_loop0 sk_seed sk_adrs blocks i ⦃ r =>
      ∀ j, j < 35 → bytes (r.val[j]!).val =
        padFrom 64 ({ adrsS sk_adrs with word2 := j }.compress ++ bytes sk_seed.val) ⦄ := by
  unfold wots.sk_blocks_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 35#usize × Usize) => 35 - p.2.val)
    (inv := fun p => p.2.val ≤ 35 ∧ ∀ j, j < p.2.val → bytes (p.1.val[j]!).val =
      padFrom 64 ({ adrsS sk_adrs with word2 := j }.compress ++ bytes sk_seed.val))
  · rintro ⟨blocks, i⟩ ⟨h1, h2⟩
    simp only [wots.sk_blocks_loop0.body, LEN_eq]
    simp only at h1 h2
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [i2_post, a2_post, Array.set_val_eq]
    refine forall_set_succ blocks.val i.val a1 (fun j (b : Array U8 64#usize) => bytes b.val =
      padFrom 64 ({ adrsS sk_adrs with word2 := j }.compress ++ bytes sk_seed.val))
      (by simp; scalar_tac) h2 ?_
    rw [a1_post, s_post, a_post, i1_post]
    simp only [adrsS, Array.val_to_slice, cast_u32_val i (by scalar_tac)]
  · exact ⟨hi, hinv⟩

/-- Setting byte 9 (the address type) of every block. -/
theorem sk_blocks_loop1_spec (ty : U32) (blocks0 blocks : Array (Array U8 64#usize) 35#usize)
    (i : Usize) (hi : i.val ≤ 35)
    (hdone : ∀ j, j < i.val → bytes (blocks.val[j]!).val =
      (bytes (blocks0.val[j]!).val).set 9 (BitVec.ofNat 8 ty.val))
    (hrest : ∀ j, i.val ≤ j → blocks.val[j]! = blocks0.val[j]!) :
    wots.sk_blocks_loop1 ty blocks i ⦃ r =>
      ∀ j, j < 35 → bytes (r.val[j]!).val =
        (bytes (blocks0.val[j]!).val).set 9 (BitVec.ofNat 8 ty.val) ⦄ := by
  unfold wots.sk_blocks_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 35#usize × Usize) => 35 - p.2.val)
    (inv := fun p => p.2.val ≤ 35 ∧
      (∀ j, j < p.2.val → bytes (p.1.val[j]!).val =
        (bytes (blocks0.val[j]!).val).set 9 (BitVec.ofNat 8 ty.val)) ∧
      (∀ j, p.2.val ≤ j → p.1.val[j]! = blocks0.val[j]!))
  · rintro ⟨blocks, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.sk_blocks_loop1.body, LEN_eq]
    simp only at h1 h2 h3
    step*
    have hil : i.val < blocks.val.length := by simp; scalar_tac
    refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
    · rw [i3_post, index_mut_back_post, Array.set_val_eq]
      refine forall_set_succ blocks.val i.val a1 (fun j (b : Array U8 64#usize) => bytes b.val =
        (bytes (blocks0.val[j]!).val).set 9 (BitVec.ofNat 8 ty.val)) hil h2 ?_
      rw [a1_post, Array.set_val_eq, bytes_set, i2_post, cast_u8_bv32, a_post,
        ← getElem!_eq _ _ hil, h3 _ (le_refl _)]
      rfl
    · intro j hj
      rw [index_mut_back_post, Array.set_val_eq, getElem!_set_ne' _ _ _ _ (by scalar_tac)]
      exact h3 j (by scalar_tac)
  · exact ⟨hi, hdone, hrest⟩

theorem repeat_getElem! {α} [Inhabited α] (x : α) (j : Nat) (hj : j < 35) :
    ((Array.repeat 35#usize x).to_slice.val)[j]! = x := by
  rw [Array.val_to_slice, Array.repeat_val, List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
  simp [hj]

theorem toSlice_getElem! {n : Usize} (a : Array (Array U8 64#usize) n) (j : Nat) :
    a.to_slice.val[j]! = a.val[j]! := by
  rw [Array.val_to_slice]

/-- The blocks of the `LEN` chains, each holding its secret value `PRF` at the
address of chain `i` with hash address `0`. -/
@[step]
theorem sk_blocks_spec (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk)
    (adrs : address.Adrs) :
    wots.sk_blocks sk pk adrs ⦃ r =>
      ∀ i, i < 35 → bytes (r.val[i]!).val =
        padFrom 64 ({ adrsS adrs with word2 := i, word3 := 0 }.compress ++
          Spec.PRF (bytes pk.pk_seed.val) (bytes sk.val) { Spec.wotsSkAdrs (adrsS adrs) with word2 := i }) ⦄ := by
  unfold wots.sk_blocks
  let* ⟨ a, a_post, a_post1 ⟩ ← with_type_spec
  let* ⟨ sk_adrs, sk_adrs_post ⟩ ← with_keypair_spec
  let* ⟨ blocks1, blocks1_post ⟩ ← sk_blocks_loop0_spec
  let* ⟨ s, back, s_post, back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s2, s2_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s3, s3_len, s3_post ⟩ ← chain_blocks_spec
  have hb2 : (back s3).val = s3.val := by
    rw [back_post]; exact Array.from_slice_val _ _ (by simp [s3_len, s_post])
  apply WP.spec_mono (sk_blocks_loop1_spec adrs.typ (back s3) (back s3) 0#usize (by simp)
    (by simp) (fun _ _ => rfl))
  intro r hr i hi
  rw [hr i hi, hb2]
  have hsl : s.length = 35 := by simp [s_post]
  rw [s3_post i (by omega), s_post, s1_post, s2_post, repeat_getElem! _ _ hi, repeat_getElem! _ _ hi]
  have hpkl : (bytes pk.pk_seed.val).length = 16 := by simp
  rw [blocks1_post i hi, show (1#u32).val = 0 + 1 from rfl, show (0#u32).val = 0 from rfl,
    runBlock_one, hpk, ← hpk, stepBlock_thash _ hpkl _ hpk _ _ (by simp), block_set_typ _ _ (by rw [thash_length _ hpkl]; omega)]
  simp [sk_adrs_post, a_post1, Spec.PRF, adrsS, Spec.wotsSkAdrs, Spec.Adrs.setTypeAndClear,
    Spec.WOTS_PRF, WOTS_PRF_eq]

/-! The values held in the chain blocks. -/

/-- The value of a block after the steps `s`, …, `e − 1`: `chain`. -/
theorem lane_value (pk : hash.Seed) (hpk : SeedOk pk) (A : Spec.Adrs) (m : Spec.Bytes)
    (hm : m.length = 16) (B : Spec.Bytes) (hB : ValBlk A m B) (s e : Nat) (hse : s ≤ e) :
    ((runBlock (wv pk.state.val) B s e).drop 22).take 16 =
      Spec.chain m s (e - s) (bytes pk.pk_seed.val) A := by
  have hpkl : (bytes pk.pk_seed.val).length = 16 := by simp
  have h := runBlock_chain _ hpkl _ hpk A m B hm hB s (e - s)
  rw [show s + (e - s) = e by omega] at h
  exact ValBlk_value _ _ _ (chain_length _ hpkl _ hm _ _ _) h

theorem PRF_length (pk : hash.Seed) (sk : Spec.Bytes) (A : Spec.Adrs) :
    (Spec.PRF (bytes pk.pk_seed.val) sk A).length = 16 :=
  thash_length _ (by simp) _ _

/-! The three WOTS+ algorithms. -/

theorem flatMap_lanes (x : Array (Array U8 64#usize) 35#usize) (f : Nat → Spec.Bytes)
    (h : ∀ (i : Nat), i < 35 → blkVal x.val[i]! = f i) :
    (List.range 35).flatMap (fun (j : Nat) => blkVal x.val[j]!) = (List.range 35).flatMap f :=
  List.flatMap_congr (fun i hi => h i (List.mem_range.mp hi))

/-- Chain `i` of `wots_pkGen` in the specification. -/
def pkGenStep (sk pk : Spec.Bytes) (a : Spec.Adrs) (i : Nat) : Spec.Bytes :=
  Spec.chain (Spec.PRF pk sk { Spec.wotsSkAdrs a with word2 := i }) 0 (Spec.w - 1) pk
    { a with word2 := i }

@[step]
theorem wots_pk_gen_spec (sk : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) :
    wots.wots_pk_gen sk pk a ⦃ r =>
      bytes r.val = Spec.wotsPkGen (bytes sk.val) (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  rename' a => adrs
  unfold wots.wots_pk_gen
  simp only [step_simps, W_eq]
  step*
  have hi15 : i = 15#u32 := by rw [i_post]; decide
  have hb : (to_slice_mut_back s3).val = s3.val := by
    rw [to_slice_mut_back_post]; exact Array.from_slice_val _ _ (by simp [s3_post, s_post])
  rw [r_post, adrsS_pk adrs a2 pk_adrs a2_post1 pk_adrs_post,
    flatMap_lanes _ (pkGenStep (bytes sk.val) (bytes pk.pk_seed.val) (adrsS adrs))]
  · rfl
  · intro j hj
    have hsl : s.length = 35 := by simp [s_post]
    rw [blkVal, hb, s3_post1 j (by omega), s_post, s1_post, s2_post, repeat_getElem! _ _ hj,
      repeat_getElem! _ _ hj, hi15,
      lane_value pk hpk { adrsS adrs with word2 := j } _ (PRF_length _ _ _) _ ⟨0, blocks_post j hj⟩
        (0#u32).val (15#u32).val (by decide)]
    rfl

theorem nats_getElem! (l : List U32) (j : Nat) (h : j < l.length) : (nats l)[j]! = (l[j]!).val := by
  simp [nats, h]

theorem digit_le (msg : alloc.vec.Vec U32) (hlen : msg.length = 35) (hdig : ∀ d ∈ msg.val, d.val < 16)
    (j : Nat) (hj : j < 35) : ((alloc.vec.Vec.deref msg).val[j]!).val ≤ 15 := by
  have hj' : j < msg.val.length := by scalar_tac
  have := hdig _ (List.getElem_mem hj')
  rw [vec_deref_val, getElem!_eq _ _ hj']
  omega

/-- Chain `i` of `wots_sign` in the specification. -/
def signStep (sk pk : Spec.Bytes) (a : Spec.Adrs) (digits : List Nat) (i : Nat) : Spec.Bytes :=
  Spec.chain (Spec.PRF pk sk { Spec.wotsSkAdrs a with word2 := i }) 0 digits[i]! pk
    { a with word2 := i }

/-- Concatenating the values held in the blocks. -/
theorem wots_sign_loop_spec (x : Array (Array U8 64#usize) 35#usize) (out : alloc.vec.Vec U8)
    (i : Usize) (hi : i.val ≤ 35) (hlen : out.length = 16 * i.val)
    (hinv : bytes out.val = (List.range i.val).flatMap (fun (j : Nat) => blkVal x.val[j]!)) :
    wots.wots_sign_loop x out i ⦃ r =>
      bytes r.val = (List.range 35).flatMap (fun (j : Nat) => blkVal x.val[j]!) ∧
      r.length = 560 ⦄ := by
  unfold wots.wots_sign_loop
  apply loop.spec_decr_nat (measure := fun (p : alloc.vec.Vec U8 × Usize) => 35 - p.2.val)
    (inv := fun p => p.2.val ≤ 35 ∧ p.1.length = 16 * p.2.val ∧
      bytes p.1.val = (List.range p.2.val).flatMap (fun (j : Nat) => blkVal x.val[j]!))
  · rintro ⟨out, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.wots_sign_loop.body, LEN_eq]
    simp only at h1 h2 h3
    simp only [step_simps]
    spec_split
    · let* ⟨ a, a_post ⟩ ← Array.index_usize_spec
      let* ⟨ s, s_post, s_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      let* ⟨ out1, out1_post ⟩ ← extend_u8_spec
      let* ⟨ i1, i1_post ⟩ ← Usize.add_spec
      refine ⟨by scalar_tac, by simp [out1_post]; scalar_tac, ?_, by scalar_tac⟩
      rw [i1_post, List.range_succ, List.flatMap_append, ← h3, out1_post]
      simp [s_post, a_post, blkVal, List.slice,
        List.getElem?_eq_getElem (show i.val < x.val.length by simp; scalar_tac)]
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
  step*
  have hb : (to_slice_mut_back s3).val = s3.val := by
    rw [to_slice_mut_back_post]; exact Array.from_slice_val _ _ (by simp [s3_post, s_post])
  apply WP.spec_mono (wots_sign_loop_spec _ _ 0#usize (by simp) (by simp) (by simp))
  rintro r ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  rw [h1, flatMap_lanes _
    (signStep (bytes sk.val) (bytes pk.pk_seed.val) (adrsS adrs) (nats msg.val)), msg_post]
  · rfl
  · intro j hj
    have hsl : s.length = 35 := by simp [s_post]
    have hd := digit_le msg msg_len msg_dig j hj
    rw [blkVal, hb, s3_post1 j (by omega), s_post, s1_post, repeat_getElem! _ _ hj,
      lane_value pk hpk { adrsS adrs with word2 := j } _ (PRF_length _ _ _) _ ⟨0, blocks_post j hj⟩
        (0#u32).val _ (by simp),
      signStep, nats_getElem! msg.val j (by scalar_tac), vec_deref_val]
    rfl

/-- Chain `i` of `wots_pkFromSig` in the specification. -/
def fromSigStep (sig pk : Spec.Bytes) (a : Spec.Adrs) (digits : List Nat) (i : Nat) : Spec.Bytes :=
  Spec.chain (Spec.block sig i) digits[i]! (Spec.w - 1 - digits[i]!) pk { a with word2 := i }

theorem wots_pk_from_sig_loop_spec (sig : Slice U8) (adrs : address.Adrs)
    (blocks : Array (Array U8 64#usize) 35#usize)
    (i : Usize) (hsig : 560 ≤ sig.length) (hi : i.val ≤ 35)
    (hinv : ∀ j, j < i.val → bytes (blocks.val[j]!).val =
      padFrom 64 ({ adrsS adrs with word2 := j }.compress ++ Spec.block (bytes sig.val) j)) :
    wots.wots_pk_from_sig_loop sig adrs blocks i ⦃ r =>
      ∀ j, j < 35 → bytes (r.val[j]!).val =
        padFrom 64 ({ adrsS adrs with word2 := j }.compress ++ Spec.block (bytes sig.val) j) ⦄ := by
  unfold wots.wots_pk_from_sig_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 35#usize × Usize) => 35 - p.2.val)
    (inv := fun p => p.2.val ≤ 35 ∧
      ∀ j, j < p.2.val → bytes (p.1.val[j]!).val =
        padFrom 64 ({ adrsS adrs with word2 := j }.compress ++ Spec.block (bytes sig.val) j))
  · rintro ⟨blocks, i⟩ ⟨h1, h2⟩
    simp only [wots.wots_pk_from_sig_loop.body, LEN_eq]
    simp only at h1 h2
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [i2_post, a3_post, Array.set_val_eq]
    refine forall_set_succ blocks.val i.val a2 (fun j (b : Array U8 64#usize) => bytes b.val =
      padFrom 64 ({ adrsS adrs with word2 := j }.compress ++ Spec.block (bytes sig.val) j))
      (by simp; scalar_tac) h2 ?_
    rw [a2_post, s_post, a_post, i1_post, Array.val_to_slice, a1_post1]
    simp only [adrsS, cast_u32_val i (by scalar_tac)]
  · exact ⟨hi, hinv⟩

theorem block_length (s : Spec.Bytes) (j : Nat) (h : (j + 1) * 16 ≤ s.length) :
    (Spec.block s j).length = 16 := by
  simp [Spec.block, Spec.n]; omega

@[step]
theorem wots_pk_from_sig_spec (sig : Slice U8) (m : Array U8 16#usize) (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs)
    (h : 560 ≤ sig.length) :
    wots.wots_pk_from_sig sig m pk a ⦃ r =>
      bytes r.val = Spec.wotsPkFromSig (bytes sig.val) (bytes m.val) (bytes pk.pk_seed.val) (adrsS a) ⦄ := by
  rename' a => adrs
  unfold wots.wots_pk_from_sig
  simp only [step_simps, W_eq]
  let* ⟨ msg, msg_post, msg_len, msg_dig ⟩ ← wots_digits_spec
  let* ⟨ blocks1, blocks1_post ⟩ ← wots_pk_from_sig_loop_spec
  step*
  have hi15 : i = 15#u32 := by rw [i_post]; decide
  have hb : (to_slice_mut_back s3).val = s3.val := by
    rw [to_slice_mut_back_post]; exact Array.from_slice_val _ _ (by simp [s3_post, s_post])
  rw [r_post, adrsS_pk adrs a2 pk_adrs a2_post1 pk_adrs_post,
    flatMap_lanes _ (fromSigStep (bytes sig.val) (bytes pk.pk_seed.val) (adrsS adrs) (nats msg.val)),
    msg_post]
  · rfl
  · intro j hj
    have hsl : s.length = 35 := by simp [s_post]
    have hd := digit_le msg msg_len msg_dig j hj
    rw [blkVal, hb, s3_post1 j (by omega), s_post, s2_post, repeat_getElem! _ _ hj, hi15,
      lane_value pk hpk { adrsS adrs with word2 := j } _
        (block_length _ _ (by simp; scalar_tac)) _ ⟨(adrsS adrs).word3, blocks1_post j hj⟩
        _ (15#u32).val (by simpa using hd),
      fromSigStep, nats_getElem! msg.val j (by scalar_tac), vec_deref_val]
    rfl

end slhdsa
