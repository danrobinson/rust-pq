import Slhdsa.Proofs.ChainTop
import Slhdsa.Proofs.Util
open Aeneas Aeneas.Std Result

/-! WOTS+ (FIPS 205 §5), for `n = N ∈ {16, 24, 32}`: the `len = 2n + 3`
chains are the first `len` blocks of arrays of `LEN_MAX = 67` blocks. -/

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
theorem LEN2_eq : params.LEN2 = 3#usize := by with_unfolding_all rfl
theorem LG_W_eq : params.LG_W = 4#u32 := by with_unfolding_all rfl

/-- The specification's parameters of a valid set whose `n` is `N`. -/
structure PN (p : params.Params) (N : Usize) : Prop where
  valid : (paramsS p).Valid
  n_eq : p.n = N

theorem PN.nok {p : params.Params} {N : Usize} (h : PN p N) : NOk N := by
  have hn := h.valid.n_cases
  simp only [paramsS_n] at hn
  rw [h.n_eq] at hn
  exact hn

theorem PN.n {p : params.Params} {N : Usize} (h : PN p N) : (paramsS p).n = N.val := by
  simp [h.n_eq]

theorem PN.len {p : params.Params} {N : Usize} (h : PN p N) : (paramsS p).len = 2 * N.val + 3 := by
  rw [len_eq p h.valid, h.n_eq]

theorem PN.len1 {p : params.Params} {N : Usize} (h : PN p N) : (paramsS p).len1 = 2 * N.val := by
  rw [len1_eq p h.valid, h.n_eq]

theorem PN.len2 {p : params.Params} {N : Usize} (h : PN p N) : (paramsS p).len2 = 3 :=
  len2_eq p h.valid

theorem PN.le32 {p : params.Params} {N : Usize} (h : PN p N) : N.val ≤ 32 := h.nok.le32

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
theorem wots_digits_spec {N : Usize} (p : params.Params) (hp : PN p N) (m : Array U8 N) :
    wots.wots_digits m ⦃ r =>
      nats r.val = Spec.wotsDigits (paramsS p) (bytes m.val) ∧ r.length = 2 * N.val + 3 ∧
      ∀ d ∈ r.val, d.val < 16 ⦄ := by
  have hn32 := hp.le32
  unfold wots.wots_digits
  simp only [LG_W_eq, LEN2_eq]
  let* ⟨ len1, len1_post ⟩ ← Usize.mul_spec
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
  let* ⟨ r, r_post ⟩ ← extend_u32_spec
  rw [vec_deref_val] at r_post
  refine ⟨?_, ?_, ?_⟩
  · simp only [Spec.wotsDigits, r_post, nats, List.map_append, hp.len1, hp.len2,
      w_eq p, paramsS_lgw]
    simp only [nats] at msg_post tail_post csum_post
    rw [msg_post, tail_post, hbytes, csum_post, msg_post, s_post, len1_post]
    simp
  · simp [r_post]; scalar_tac
  · intro d hd
    simp [r_post] at hd
    rcases hd with hd | hd
    · exact msg_post2 d hd
    · exact tail_post2 d hd

theorem WOTS_PRF_eq : address.WOTS_PRF = 5#u32 := by with_unfolding_all rfl
theorem WOTS_PK_eq : address.WOTS_PK = 1#u32 := by with_unfolding_all rfl

theorem adrsS_pk (adrs a pk_adrs : address.Adrs)
    (ha : a = ⟨adrs.layer, adrs.tree, address.WOTS_PK, 0#u32, 0#u32, 0#u32⟩)
    (hs : pk_adrs = ⟨a.layer, a.tree, a.typ, adrs.keypair, a.word2, a.word3⟩) :
    adrsS pk_adrs = Spec.wotsPkAdrs (adrsS adrs) := by
  subst ha; subst hs
  simp [adrsS, Spec.wotsPkAdrs, Spec.Adrs.setTypeAndClear, Spec.WOTS_PK, WOTS_PK_eq]

theorem forall_set_succ {α} [Inhabited α] (l : List α) (i : Nat) (x : α) (P : Nat → α → Prop)
    (hl : i < l.length) (h : ∀ j, j < i → P j l[j]!) (hx : P i x) :
    ∀ j, j < i + 1 → P j (l.set i x)[j]! := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
  · rw [getElem!_set_ne' _ _ _ _ (by omega)]; exact h j hj
  · subst hj; rw [getElem!_set_self' _ _ _ hl]; exact hx

theorem cast_u32_val (i : Usize) (h : i.val < 67) : (UScalar.cast .U32 i).val = i.val := by
  simp; scalar_tac

theorem len_le {N : Usize} (h : N.val ≤ 32) : 2 * N.val + 3 ≤ 67 := by omega

theorem sk_blocks_loop0_spec {N : Usize} (sk_seed : Array U8 N) (hN : N.val ≤ 32) (len : Usize)
    (hlen : len.val ≤ 67) (sk_adrs : address.Adrs)
    (blocks : Array (Array U8 64#usize) 67#usize) (i : Usize) (hi : i.val ≤ len.val)
    (hinv : ∀ j, j < i.val → bytes (blocks.val[j]!).val =
      padFrom 64 ({ adrsS sk_adrs with word2 := j }.compress ++ bytes sk_seed.val)) :
    wots.sk_blocks_loop0 sk_seed len sk_adrs blocks i ⦃ r =>
      ∀ j, j < len.val → bytes (r.val[j]!).val =
        padFrom 64 ({ adrsS sk_adrs with word2 := j }.compress ++ bytes sk_seed.val) ⦄ := by
  unfold wots.sk_blocks_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 67#usize × Usize) => len.val - p.2.val)
    (inv := fun p => p.2.val ≤ len.val ∧ ∀ j, j < p.2.val → bytes (p.1.val[j]!).val =
      padFrom 64 ({ adrsS sk_adrs with word2 := j }.compress ++ bytes sk_seed.val))
  · rintro ⟨blocks, i⟩ ⟨h1, h2⟩
    simp only [wots.sk_blocks_loop0.body]
    simp only at h1 h2
    step*
    all_goals try scalar_tac
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [i2_post, a2_post, Array.set_val_eq]
      refine forall_set_succ blocks.val i.val a1 (fun j (b : Array U8 64#usize) => bytes b.val =
        padFrom 64 ({ adrsS sk_adrs with word2 := j }.compress ++ bytes sk_seed.val))
        (by simp; scalar_tac) h2 ?_
      rw [a1_post, s_post, a_post, i1_post]
      simp only [adrsS, Array.val_to_slice, cast_u32_val i (by scalar_tac)]
  · exact ⟨hi, hinv⟩

/-- Setting byte 9 (the address type) of the first `len` blocks. -/
theorem sk_blocks_loop1_spec (ty : U32) (len : Usize) (hlen : len.val ≤ 67)
    (blocks0 blocks : Array (Array U8 64#usize) 67#usize)
    (i : Usize) (hi : i.val ≤ len.val)
    (hdone : ∀ j, j < i.val → bytes (blocks.val[j]!).val =
      (bytes (blocks0.val[j]!).val).set 9 (BitVec.ofNat 8 ty.val))
    (hrest : ∀ j, i.val ≤ j → blocks.val[j]! = blocks0.val[j]!) :
    wots.sk_blocks_loop1 ty len blocks i ⦃ r =>
      ∀ j, j < len.val → bytes (r.val[j]!).val =
        (bytes (blocks0.val[j]!).val).set 9 (BitVec.ofNat 8 ty.val) ⦄ := by
  unfold wots.sk_blocks_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 67#usize × Usize) => len.val - p.2.val)
    (inv := fun p => p.2.val ≤ len.val ∧
      (∀ j, j < p.2.val → bytes (p.1.val[j]!).val =
        (bytes (blocks0.val[j]!).val).set 9 (BitVec.ofNat 8 ty.val)) ∧
      (∀ j, p.2.val ≤ j → p.1.val[j]! = blocks0.val[j]!))
  · rintro ⟨blocks, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.sk_blocks_loop1.body]
    simp only at h1 h2 h3
    step*
    all_goals try scalar_tac
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

theorem repeat_getElem! {α} [Inhabited α] (x : α) (j : Nat) (hj : j < 67) :
    ((Array.repeat 67#usize x).to_slice.val)[j]! = x := by
  rw [Array.val_to_slice, Array.repeat_val, List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
  simp [hj]

theorem slice0_getElem! {α} [Inhabited α] (l : List α) (len j : Nat) (hj : j < len) (hl : len ≤ l.length) :
    (l.slice 0 len)[j]! = l[j]! := by
  simp [List.slice, List.getElem!_eq_getElem?_getD, List.getElem?_take, hj]

theorem setSlice0_getElem! {α} [Inhabited α] (l s : List α) (j : Nat) (hj : j < s.length)
    (hl : s.length ≤ l.length) : (l.setSlice! 0 s)[j]! = s[j]! := by
  rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by omega, by omega⟩]
  simp

/-- The seed state is that of the SHA-256 tweakable hashes. -/
theorem seed_state {N : Usize} (seed : hash.Seed N) (hs : SeedOk seed) :
    wv seed.state.val = seedState N.val (bytes seed.pk_seed.val) := hs.1

/-- The value of a block after the steps `s`, …, `e − 1`: `chain`. -/
theorem lane_value {N : Usize} (p : params.Params) (hp : PN p N) (seed : hash.Seed N)
    (hs : SeedOk seed) (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length = N.val) (B : Spec.Bytes)
    (hB : ValBlk A m B) (s e : Nat) (hse : s ≤ e) :
    ((runBlock N.val (wv seed.state.val) B s e).drop 22).take N.val =
      Spec.chain (paramsS p) m s (e - s) (bytes seed.pk_seed.val) A := by
  have hn := hp.n
  have h32 : (paramsS p).n ≤ 32 := by rw [hn]; exact hp.le32
  have hpkl : (bytes seed.pk_seed.val).length = (paramsS p).n := by rw [hn]; simp
  have hm' : m.length = (paramsS p).n := by rw [hn]; exact hm
  have hst : wv seed.state.val = seedState (paramsS p).n (bytes seed.pk_seed.val) := by
    rw [hn]; exact hs.1
  rw [← hn, hst]
  have h := runBlock_chain (paramsS p) h32 _ hpkl A m B hm' hB s (e - s)
  rw [show s + (e - s) = e by omega] at h
  exact ValBlk_value _ _ _ _ (chain_length _ h32 _ hpkl _ hm' _ _ _) (by omega) h

theorem PRF_length {N : Usize} (p : params.Params) (hp : PN p N) (pk : Spec.Bytes)
    (hpk : pk.length = N.val) (sk : Spec.Bytes) (A : Spec.Adrs) :
    (Spec.PRF (paramsS p) pk sk A).length = N.val := by
  rw [PRF_eq, hp.n]; exact th256_length _ hp.le32 _ hpk _ _

/-- The blocks of the `len` chains, each holding its secret value `PRF` at the
address of chain `i` with hash address `0`. -/
@[step]
theorem sk_blocks_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (adrs : address.Adrs) :
    wots.sk_blocks sk seed adrs ⦃ r =>
      ∀ i, i < 2 * N.val + 3 → bytes (r.val[i]!).val =
        padFrom 64 ({ adrsS adrs with word2 := i, word3 := 0 }.compress ++
          Spec.PRF (paramsS p) (bytes seed.pk_seed.val) (bytes sk.val)
            { Spec.wotsSkAdrs (adrsS adrs) with word2 := i }) ⦄ := by
  have hN32 := hp.le32
  unfold wots.sk_blocks
  simp only [LEN2_eq]
  let* ⟨ i, i_post ⟩ ← Usize.mul_spec
  let* ⟨ len, len_post ⟩ ← Usize.add_spec
  let* ⟨ a, a_post, a_post1 ⟩ ← with_type_spec
  let* ⟨ sk_adrs, sk_adrs_post ⟩ ← with_keypair_spec
  let* ⟨ blocks1, blocks1_post ⟩ ← sk_blocks_loop0_spec
  step*
  have hl : len.val = 2 * N.val + 3 := by rw [len_post, i_post]
  have hs3l : s3.val.length = len.val := by
    have : s3.length = len.val := by rw [s3_post, s_post1]; simp
    simpa [Slice.length] using this
  apply WP.spec_mono (sk_blocks_loop1_spec adrs.typ len (by omega) (index_mut_back s3)
    (index_mut_back s3) 0#usize (by simp) (by simp) (fun _ _ => rfl))
  intro r hr j hj
  rw [hl] at hr
  rw [hr j hj, s_post2, setSlice0_getElem! _ _ _ (by omega) (by simp; omega),
    s3_post1 j (by simp [Slice.length] at s_post1 ⊢; omega), s_post,
    slice0_getElem! _ _ _ (by omega) (by simp; omega), s1_post, s2_post,
    repeat_getElem! _ _ (by omega), repeat_getElem! _ _ (by omega),
    blocks1_post j (by omega), show (1#u32).val = 0 + 1 from rfl, show (0#u32).val = 0 from rfl,
    runBlock_one]
  have hn := hp.n
  have h32 : (paramsS p).n ≤ 32 := by rw [hn]; exact hp.le32
  have hpkl : (bytes seed.pk_seed.val).length = (paramsS p).n := by rw [hn]; simp
  have hst : wv seed.state.val = seedState (paramsS p).n (bytes seed.pk_seed.val) := by
    rw [hn]; exact hs.1
  rw [← hn, hst, stepBlock_thash _ h32 _ hpkl _ _ (by rw [hn]; simp),
    block_set_typ _ _ (by rw [F_eq, th256_length _ h32 _ hpkl]; omega)]
  simp [sk_adrs_post, a_post1, Spec.PRF, Spec.F, adrsS, Spec.wotsSkAdrs, Spec.Adrs.setTypeAndClear,
    Spec.WOTS_PRF, WOTS_PRF_eq]

/-! The three WOTS+ algorithms. -/

theorem flatMap_lanes (n : Nat) (x : List (Array U8 64#usize)) (k : Nat) (f : Nat → Spec.Bytes)
    (h : ∀ (i : Nat), i < k → blkVal n x[i]! = f i) :
    (List.range k).flatMap (fun (j : Nat) => blkVal n x[j]!) = (List.range k).flatMap f :=
  List.flatMap_congr (fun i hi => h i (List.mem_range.mp hi))

/-- Chain `i` of `wots_pkGen` in the specification. -/
def pkGenStep (P : Spec.Params) (sk pk : Spec.Bytes) (a : Spec.Adrs) (i : Nat) : Spec.Bytes :=
  Spec.chain P (Spec.PRF P pk sk { Spec.wotsSkAdrs a with word2 := i }) 0 (P.w - 1) pk
    { a with word2 := i }

theorem wrapping_sub_15 : core.num.U32.wrapping_sub params.W 1#u32 = 15#u32 := by
  rw [W_eq]; decide

/-- The block of a chain after the index range is written back. -/
theorem back_lane {α} [Inhabited α] (blocks : List α) (s3 : List α) (j len : Nat) (hj : j < len)
    (h3 : s3.length = len) (hl : len ≤ blocks.length) :
    ((blocks.setSlice! 0 s3).slice 0 len)[j]! = s3[j]! := by
  rw [slice0_getElem! _ _ _ hj (by simp; omega), setSlice0_getElem! _ _ _ (by omega) (by omega)]

@[step]
theorem wots_pk_gen_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) :
    wots.wots_pk_gen sk seed a ⦃ r =>
      bytes r.val = Spec.wotsPkGen (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS a) ⦄ := by
  rename' a => adrs
  have hN32 := hp.le32
  unfold wots.wots_pk_gen
  simp only [LEN2_eq, wrapping_sub_15]
  let* ⟨ i, i_post ⟩ ← Usize.mul_spec
  let* ⟨ len, len_post ⟩ ← Usize.add_spec
  have hl : len.val = 2 * N.val + 3 := by rw [len_post, i_post]
  let* ⟨ blocks, blocks_post ⟩ ← sk_blocks_spec
  step*
  case P => exact paramsS p
  case hPN => exact hp.n
  case hN => exact hp.nok
  all_goals try (simp only [W_eq]; decide)
  have hi15 : i1 = 15#u32 := by rw [i1_post, W_eq]; decide
  have hsl : s.val.length = len.val := by simp [s_post]; omega
  have hs3l : s3.val.length = len.val := by
    have := s3_post; simp only [Slice.length] at this; omega
  have hs4l : s4.length = 2 * N.val + 3 := by rw [s4_post1]; omega
  rw [r_post, adrsS_pk adrs a2 pk_adrs a2_post1 pk_adrs_post, Spec.wotsPkGen, hs4l, ← hp.len,
    flatMap_lanes N.val s4.val _ (pkGenStep (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS adrs))]
  · rfl
  · intro j hj
    rw [hp.len] at hj
    rw [blkVal, s4_post, Array.val_to_slice, s_post2, back_lane _ _ _ _ (by omega) hs3l (by simp; omega),
      s3_post1 j (by simp [Slice.length]; omega), s_post, slice0_getElem! _ _ _ (by omega) (by simp; omega),
      s1_post, s2_post, repeat_getElem! _ _ (by omega), repeat_getElem! _ _ (by omega), hi15,
      lane_value p hp seed hs { adrsS adrs with word2 := j } _
        (PRF_length p hp _ (by simp) _ _) _ ⟨0, blocks_post j hj⟩ (0#u32).val (15#u32).val (by decide),
      pkGenStep, w_eq]
    rfl

theorem nats_getElem! (l : List U32) (j : Nat) (h : j < l.length) : (nats l)[j]! = (l[j]!).val := by
  simp [nats, h]

theorem digit_le (msg : alloc.vec.Vec U32) (len : Nat) (hlen : msg.length = len)
    (hdig : ∀ d ∈ msg.val, d.val < 16)
    (j : Nat) (hj : j < len) : ((alloc.vec.Vec.deref msg).val[j]!).val ≤ 15 := by
  have hj' : j < msg.val.length := by scalar_tac
  have := hdig _ (List.getElem_mem hj')
  rw [vec_deref_val, getElem!_eq _ _ hj']
  omega

/-- Chain `i` of `wots_sign` in the specification. -/
def signStep (P : Spec.Params) (sk pk : Spec.Bytes) (a : Spec.Adrs) (digits : List Nat) (i : Nat) :
    Spec.Bytes :=
  Spec.chain P (Spec.PRF P pk sk { Spec.wotsSkAdrs a with word2 := i }) 0 digits[i]! pk
    { a with word2 := i }

/-- Concatenating the values held in the first `len` blocks. -/
theorem wots_sign_loop_spec (N : Usize) (hN : N.val ≤ 32) (len : Usize) (hlen : len.val ≤ 67)
    (x : Array (Array U8 64#usize) 67#usize) (out : alloc.vec.Vec U8)
    (i : Usize) (hi : i.val ≤ len.val) (hl : out.length = N.val * i.val)
    (hinv : bytes out.val = (List.range i.val).flatMap (fun (j : Nat) => blkVal N.val x.val[j]!)) :
    wots.wots_sign_loop N len x out i ⦃ r =>
      bytes r.val = (List.range len.val).flatMap (fun (j : Nat) => blkVal N.val x.val[j]!) ∧
      r.length = N.val * len.val ⦄ := by
  unfold wots.wots_sign_loop
  apply loop.spec_decr_nat (measure := fun (p : alloc.vec.Vec U8 × Usize) => len.val - p.2.val)
    (inv := fun p => p.2.val ≤ len.val ∧ p.1.length = N.val * p.2.val ∧
      bytes p.1.val = (List.range p.2.val).flatMap (fun (j : Nat) => blkVal N.val x.val[j]!))
  · rintro ⟨out, i⟩ ⟨h1, h2, h3⟩
    simp only [wots.wots_sign_loop.body]
    simp only at h1 h2 h3
    split
    · rename_i hlt
      have hil : i.val < len.val := by scalar_tac
      have hb : N.val * i.val + N.val ≤ 32 * 67 := by
        have := Nat.mul_le_mul hN (show i.val + 1 ≤ 67 by omega); rw [Nat.mul_succ] at this; omega
      step*
      all_goals try scalar_tac
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · have : sig1.val.length = out.val.length + N.val := by
          rw [sig1_post]; simp [s_post, List.slice]; scalar_tac
        simp only [alloc.vec.Vec.length] at h2 ⊢
        rw [this, h2, i2_post, Nat.mul_succ]
      · rw [i2_post, List.range_succ, List.flatMap_append, ← h3, sig1_post]
        simp [s_post, a_post, blkVal, List.slice, i1_post,
          List.getElem?_eq_getElem (show i.val < x.val.length by simp; scalar_tac)]
    · simp only [step_simps]
      have : i.val = len.val := by scalar_tac
      rw [this] at h3 h2
      exact ⟨h3, h2⟩
  · exact ⟨hi, hl, hinv⟩

@[step]
theorem wots_sign_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) :
    wots.wots_sign m sk seed a ⦃ r =>
      bytes r.val = Spec.wotsSign (paramsS p) (bytes m.val) (bytes sk.val) (bytes seed.pk_seed.val)
        (adrsS a) ∧ r.length = N.val * (2 * N.val + 3) ⦄ := by
  rename' a => adrs
  have hN32 := hp.le32
  unfold wots.wots_sign
  simp only [LEN2_eq]
  let* ⟨ i, i_post ⟩ ← Usize.mul_spec
  let* ⟨ len, len_post ⟩ ← Usize.add_spec
  have hl : len.val = 2 * N.val + 3 := by rw [len_post, i_post]
  let* ⟨ msg, msg_post, msg_len, msg_dig ⟩ ← wots_digits_spec
  let* ⟨ blocks, blocks_post ⟩ ← sk_blocks_spec
  step*
  apply WP.spec_mono (wots_sign_loop_spec N hN32 len (by omega) _ _ 0#usize (by simp) (by simp) (by simp))
  rintro r ⟨h1, h2⟩
  refine ⟨?_, by rw [h2, hl]⟩
  have hsl : s.val.length = len.val := by
    have := s_post1; simp only [Slice.length] at this; omega
  have hs3l : s3.val.length = len.val := by
    have := s3_post; simp only [Slice.length] at this; omega
  rw [h1, hl, Spec.wotsSign, ← hp.len, flatMap_lanes N.val _ _
    (signStep (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val) (adrsS adrs) (nats msg.val)), msg_post]
  · rfl
  · intro j hj
    rw [hp.len] at hj
    have hd := digit_le msg _ msg_len msg_dig j hj
    rw [blkVal, s_post2, setSlice0_getElem! _ _ _ (by omega) (by simp; omega),
      s3_post1 j (by simp [Slice.length]; omega), s_post, slice0_getElem! _ _ _ (by omega) (by simp; omega),
      s1_post, repeat_getElem! _ _ (by omega),
      lane_value p hp seed hs { adrsS adrs with word2 := j } _
        (PRF_length p hp _ (by simp) _ _) _ ⟨0, blocks_post j hj⟩ (0#u32).val _ (Nat.zero_le _),
      signStep, nats_getElem! msg.val j (by have := msg_len; simp only [alloc.vec.Vec.length] at this; omega), vec_deref_val]
    rfl

/-- Chain `i` of `wots_pkFromSig` in the specification. -/
def fromSigStep (P : Spec.Params) (sig pk : Spec.Bytes) (a : Spec.Adrs) (digits : List Nat) (i : Nat) :
    Spec.Bytes :=
  Spec.chain P (Spec.block P sig i) digits[i]! (P.w - 1 - digits[i]!) pk { a with word2 := i }

theorem wots_pk_from_sig_loop_spec (N : Usize) (hN : N.val ≤ 32) (sig : Slice U8) (adrs : address.Adrs)
    (len : Usize) (hlen : len.val ≤ 67) (blocks : Array (Array U8 64#usize) 67#usize)
    (i : Usize) (hsig : N.val * len.val ≤ sig.length) (hi : i.val ≤ len.val)
    (hinv : ∀ j, j < i.val → bytes (blocks.val[j]!).val =
      padFrom 64 ({ adrsS adrs with word2 := j }.compress ++ ((bytes sig.val).drop (j * N.val)).take N.val)) :
    wots.wots_pk_from_sig_loop N sig adrs len blocks i ⦃ r =>
      ∀ j, j < len.val → bytes (r.val[j]!).val =
        padFrom 64 ({ adrsS adrs with word2 := j }.compress ++ ((bytes sig.val).drop (j * N.val)).take N.val) ⦄ := by
  unfold wots.wots_pk_from_sig_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Array (Array U8 64#usize) 67#usize × Usize) => len.val - p.2.val)
    (inv := fun p => p.2.val ≤ len.val ∧
      ∀ j, j < p.2.val → bytes (p.1.val[j]!).val =
        padFrom 64 ({ adrsS adrs with word2 := j }.compress ++ ((bytes sig.val).drop (j * N.val)).take N.val))
  · rintro ⟨blocks, i⟩ ⟨h1, h2⟩
    simp only [wots.wots_pk_from_sig_loop.body]
    simp only at h1 h2
    split
    · rename_i hlt
      have hil : i.val < len.val := by scalar_tac
      have hb : (i.val + 1) * N.val ≤ sig.length := by
        have := Nat.mul_le_mul_left N.val (show i.val + 1 ≤ len.val by omega)
        rw [Nat.mul_comm] at this; omega
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [i2_post, a3_post, Array.set_val_eq]
      refine forall_set_succ blocks.val i.val a2 (fun j (b : Array U8 64#usize) => bytes b.val =
        padFrom 64 ({ adrsS adrs with word2 := j }.compress ++ ((bytes sig.val).drop (j * N.val)).take N.val))
        (by simp; scalar_tac) h2 ?_
      rw [a2_post, s_post, a_post, i1_post, Array.val_to_slice, a1_post]
      simp only [adrsS, cast_u32_val i (by scalar_tac), bytes_take, bytes_drop]
    · simp only [step_simps]
      have : i.val = len.val := by scalar_tac
      rw [this] at h2; exact h2
  · exact ⟨hi, hinv⟩

@[step]
theorem wots_pk_from_sig_spec {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (m : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (h : N.val * (2 * N.val + 3) ≤ sig.length) :
    wots.wots_pk_from_sig sig m seed a ⦃ r =>
      bytes r.val = Spec.wotsPkFromSig (paramsS p) (bytes sig.val) (bytes m.val) (bytes seed.pk_seed.val)
        (adrsS a) ⦄ := by
  rename' a => adrs
  have hN32 := hp.le32
  unfold wots.wots_pk_from_sig
  simp only [LEN2_eq]
  let* ⟨ i, i_post ⟩ ← Usize.mul_spec
  let* ⟨ len, len_post ⟩ ← Usize.add_spec
  have hl : len.val = 2 * N.val + 3 := by rw [len_post, i_post]
  let* ⟨ msg, msg_post, msg_len, msg_dig ⟩ ← wots_digits_spec
  let* ⟨ blocks1, blocks1_post ⟩ ← wots_pk_from_sig_loop_spec N hN32 sig adrs len (by omega)
    (hsig := by rw [hl]; exact h)
  step*
  case P => exact paramsS p
  case hPN => exact hp.n
  case hN => exact hp.nok
  all_goals try (simp only [W_eq]; decide)
  have hi15 : i1 = 15#u32 := by rw [i1_post, W_eq]; decide
  have hsl : s.val.length = len.val := by simp [s_post]; omega
  have hs3l : s3.val.length = len.val := by
    have := s3_post; simp only [Slice.length] at this; omega
  have hs4l : s4.length = 2 * N.val + 3 := by rw [s4_post1]; omega
  rw [r_post, adrsS_pk adrs a2 pk_adrs a2_post1 pk_adrs_post, Spec.wotsPkFromSig, hs4l, ← hp.len,
    flatMap_lanes N.val s4.val _
      (fromSigStep (paramsS p) (bytes sig.val) (bytes seed.pk_seed.val) (adrsS adrs) (nats msg.val)),
    msg_post]
  · rfl
  · intro j hj
    rw [hp.len] at hj
    have hd := digit_le msg _ msg_len msg_dig j hj
    have hblk : Spec.block (paramsS p) (bytes sig.val) j = ((bytes sig.val).drop (j * N.val)).take N.val := by
      rw [Spec.block, hp.n]
    have hbl : (((bytes sig.val).drop (j * N.val)).take N.val).length = N.val := by
      have h1 : N.val * (j + 1) ≤ N.val * (2 * N.val + 3) := Nat.mul_le_mul_left _ (by omega)
      have h2 : N.val * (j + 1) = j * N.val + N.val := by ring
      have h3 := h
      simp only [Slice.length] at h3
      simp; omega
    rw [blkVal, s4_post, Array.val_to_slice, s_post2, back_lane _ _ _ _ (by omega) hs3l (by simp; omega),
      s3_post1 j (by simp [Slice.length]; omega), s_post, slice0_getElem! _ _ _ (by omega) (by simp; omega),
      s2_post, repeat_getElem! _ _ (by omega), hi15,
      lane_value p hp seed hs { adrsS adrs with word2 := j } _ hbl _
        ⟨(adrsS adrs).word3, blocks1_post j (by omega)⟩ _ (15#u32).val (by simpa using hd),
      fromSigStep, nats_getElem! msg.val j (by have := msg_len; simp only [alloc.vec.Vec.length] at this; omega), vec_deref_val, hblk, w_eq]
    rfl

end slhdsa
