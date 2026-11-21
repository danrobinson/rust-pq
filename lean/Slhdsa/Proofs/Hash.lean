import Slhdsa.Proofs.Sha256
open Aeneas Aeneas.Std Result

/-! Addresses and the SLH-DSA hash functions. -/

namespace slhdsa

@[step]
theorem with_type_spec (a : address.Adrs) (x : U32) :
    address.Adrs.with_type a x ⦃ r => adrsS r = (adrsS a).setTypeAndClear x.val ∧
      r = { a with typ := x, keypair := 0#u32, word2 := 0#u32, word3 := 0#u32 } ⦄ := by
  unfold address.Adrs.with_type
  simp [adrsS, Spec.Adrs.setTypeAndClear]

@[step]
theorem with_layer_spec (a : address.Adrs) (x : U32) :
    address.Adrs.with_layer a x ⦃ r => r = { a with layer := x } ⦄ := by
  unfold address.Adrs.with_layer
  simp

@[step]
theorem with_tree_spec (a : address.Adrs) (x : U64) :
    address.Adrs.with_tree a x ⦃ r => r = { a with tree := x } ⦄ := by
  unfold address.Adrs.with_tree
  simp

@[step]
theorem with_keypair_spec (a : address.Adrs) (x : U32) :
    address.Adrs.with_keypair a x ⦃ r => r = { a with keypair := x } ⦄ := by
  unfold address.Adrs.with_keypair
  simp

@[step]
theorem with_word2_spec (a : address.Adrs) (x : U32) :
    address.Adrs.with_word2 a x ⦃ r => r = { a with word2 := x } ⦄ := by
  unfold address.Adrs.with_word2
  simp

@[step]
theorem with_word3_spec (a : address.Adrs) (x : U32) :
    address.Adrs.with_word3 a x ⦃ r => r = { a with word3 := x } ⦄ := by
  unfold address.Adrs.with_word3
  simp

@[step]
theorem adrs_new_spec :
    address.Adrs.new ⦃ r => r = ⟨0#u32, 0#u64, 0#u32, 0#u32, 0#u32, 0#u32⟩ ⦄ := by
  unfold address.Adrs.new
  simp

theorem compress_eq (x : Spec.Adrs) :
    x.compress = [BitVec.ofNat 8 x.layer,
      BitVec.ofNat 8 (x.tree >>> 56), BitVec.ofNat 8 (x.tree >>> 48),
      BitVec.ofNat 8 (x.tree >>> 40), BitVec.ofNat 8 (x.tree >>> 32),
      BitVec.ofNat 8 (x.tree >>> 24), BitVec.ofNat 8 (x.tree >>> 16),
      BitVec.ofNat 8 (x.tree >>> 8), BitVec.ofNat 8 x.tree,
      BitVec.ofNat 8 x.typ,
      BitVec.ofNat 8 (x.keypair >>> 24), BitVec.ofNat 8 (x.keypair >>> 16),
      BitVec.ofNat 8 (x.keypair >>> 8), BitVec.ofNat 8 x.keypair,
      BitVec.ofNat 8 (x.word2 >>> 24), BitVec.ofNat 8 (x.word2 >>> 16),
      BitVec.ofNat 8 (x.word2 >>> 8), BitVec.ofNat 8 x.word2,
      BitVec.ofNat 8 (x.word3 >>> 24), BitVec.ofNat 8 (x.word3 >>> 16),
      BitVec.ofNat 8 (x.word3 >>> 8), BitVec.ofNat 8 x.word3] := by
  rfl

theorem cast_u8_bv {ty : UScalarTy} (x : UScalar ty) :
    (UScalar.cast .U8 x).bv = BitVec.ofNat 8 x.val := by
  rw [UScalar.cast_bv_eq, ← UScalar.bv_toNat, BitVec.ofNat_toNat]
  rfl

theorem setWidth_shr64 (x : U64) (k : Nat) :
    BitVec.setWidth 8 (x.bv >>> k) = BitVec.ofNat 8 (x.val >>> k) := by
  rw [← U64.bv_toNat, ← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]

theorem setWidth_shr32 (x : U32) (k : Nat) :
    BitVec.setWidth 8 (x.bv >>> k) = BitVec.ofNat 8 (x.val >>> k) := by
  rw [← U32.bv_toNat, ← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat]

@[step]
theorem adrs_compress_spec (a : address.Adrs) :
    address.Adrs.compress a ⦃ r => bytes r.val = (adrsS a).compress ⦄ := by
  unfold address.Adrs.compress
  step*
  rw [compress_eq]
  simp [bytes, adrsS, setWidth_shr64, setWidth_shr32, *]

/-- Appending a slice of bytes to a vector of bytes. -/
@[local step]
theorem hash_extend_from_slice_u8_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r =>
      r.val = v.val ++ s.val ∧ r.length = v.length + s.length ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (by intros; simp [liftFun1]))
  intro l hl
  simp [hl]

@[simp] theorem vec_deref_val {α} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

@[simp, scalar_tac_simps] theorem vec_deref_length {α} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.deref v).length = v.length := by
  simp [alloc.vec.Vec.deref]

theorem toByte_zero_4 : Spec.toByte 0 4 = List.replicate 4 0#8 := by decide

theorem toByte_zero_48 : Spec.toByte 0 48 = List.replicate 48 0#8 := by decide

/-- A `Seed` is consistent: its state is the SHA-256 compression of the
first block `PK.seed ‖ toByte(0, 48)` of every tweakable hash. -/
def SeedOk (s : hash.Seed) : Prop :=
  wv s.state.val = Spec.SHA256.compress Spec.SHA256.H0 (bytes s.pk_seed.val ++ List.replicate 48 0#8)

@[step]
theorem seed_ctx_spec (pk : Array U8 16#usize) :
    hash.seed_ctx pk ⦃ r => r.pk_seed = pk ∧ SeedOk r ⦄ := by
  unfold hash.seed_ctx
  simp only [global_simps]
  step*
  have hb : (index_mut_back s2).val = pk.val ++ List.replicate 48 0#u8 := by
    rw [s_post2, s2_post, s1_post]
    simp [List.setSlice!]
  simp only [SeedOk]
  rw [state_post, s3_post]
  simp only [Array.val_to_slice, hb, List.drop_zero, bytes_append]
  rw [List.take_of_length_le (by simp)]
  simp [bytes]
  rfl

/-- The tweakable hash, continuing from the compressed first block. -/
theorem thash_eq (pk : Spec.Bytes) (hpk : pk.length = 16) (a : Spec.Adrs) (m : Spec.Bytes) :
    Spec.thash pk a m = (ser (hashFrom (Spec.SHA256.compress Spec.SHA256.H0
      (pk ++ List.replicate 48 0#8)) (padFrom 64 (a.compress ++ m)))).take 16 := by
  unfold Spec.thash
  rw [show 64 - Spec.n = 48 from rfl, toByte_zero_48,
    show ∀ a b c d : Spec.Bytes, a ++ b ++ c ++ d = (a ++ b) ++ (c ++ d) from by intros; simp,
    sha256_prefix64 _ _ (by simp [hpk])]
  rfl

@[step]
theorem thash_spec (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) (m : Slice U8)
    (hm : m.length ≤ 1024) :
    hash.thash pk a m ⦃ r =>
      bytes r.val = Spec.thash (bytes pk.pk_seed.val) (adrsS a) (bytes m.val) ⦄ := by
  unfold hash.thash
  have hN : params.N.val = 16 := by simp [params.N]
  simp only [step_simps]
  let* ⟨ a1, a1_post ⟩ ← adrs_compress_spec
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ buf, buf_post, buf_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ buf1, buf1_post, buf1_len ⟩ ← hash_extend_from_slice_u8_spec
  have hl : buf1.length = 22 + m.length := by
    simp [buf1_len, buf_len, s_post]
  let* ⟨ d, d_post ⟩ ← sha256_from_spec
  · simp only [Room, vec_deref_length]; scalar_tac
  let* ⟨ s4, to_slice_mut_back, s4_post, to_slice_mut_back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s5, s5_post, s5_post1 ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
  let* ⟨ s6, s6_post ⟩ ← core.slice.Slice.copy_from_slice.step_spec
  have hv : (Array.from_slice (Array.repeat 16#usize 0#u8) s5).val = s5.val :=
    Array.from_slice_val _ _ (by scalar_tac)
  simp only [to_slice_mut_back_post, s6_post, hv, s5_post, hN, List.slice]
  rw [thash_eq _ (by simp) , ← hpk, ← a1_post]
  simp [d_post, vec_deref_val, buf1_post, buf_post, s_post]

theorem toByte8_small (x : Nat) (hx : x < 65536) :
    Spec.toByte x 8 = [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, BitVec.ofNat 8 (x >>> 8), BitVec.ofNat 8 x] := by
  have z : ∀ k, 16 ≤ k → x >>> k = 0 := by
    intro k hk
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le hx (by
      calc 65536 = 2 ^ 16 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk))
  simp only [Spec.toByte, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.map_cons,
    List.map_nil]
  simp [z]

/-- One 64-byte block holding `ADRSc ‖ m` and the padding of the whole
message, when `|m| ≤ 33`. -/
theorem padFrom_short (c m : Spec.Bytes) (hc : c.length = 22) (hm : m.length ≤ 33) :
    padFrom 64 (c ++ m) = c ++ m ++ [0x80#8] ++ List.replicate (33 - m.length) 0#8 ++
      [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, BitVec.ofNat 8 ((8 * (86 + m.length)) >>> 8),
        BitVec.ofNat 8 (8 * (86 + m.length))] := by
  have e1 : (119 - (c ++ m).length % 64) % 64 = 33 - m.length := by simp [hc]; omega
  have e2 : 8 * (64 + (c ++ m).length) = 8 * (86 + m.length) := by simp [hc]; omega
  rw [padFrom, e1, e2, toByte8_small _ (by omega)]

theorem hashFrom_one (st : List Spec.SHA256.Word) (P : Spec.Bytes) (hP : P.length = 64) :
    hashFrom st P = Spec.SHA256.compress st P := by
  simp [hashFrom, hP, Spec.SHA256.blockAt, List.take_of_length_le]

theorem set_mid {α} (A C : List α) (x y : α) (i : Nat) (hi : i = A.length) :
    (A ++ x :: C).set i y = A ++ y :: C := by
  subst hi; simp

theorem setSlice!_mid {α} (A B C s : List α) (i : Nat) (hi : i = A.length)
    (hs : s.length = B.length) :
    (A ++ B ++ C).setSlice! i s = A ++ s ++ C := by
  subst hi
  simp [List.setSlice!, hs]

@[step]
theorem short_block_spec (adrs : address.Adrs) (m : Slice U8) (hm : m.length ≤ 33) :
    hash.short_block adrs m ⦃ r =>
      bytes r.val = padFrom 64 ((adrsS adrs).compress ++ bytes m.val) ⦄ := by
  unfold hash.short_block
  simp only [global_simps]
  step*
  · scalar_tac
  · rcases System.Platform.numBits_eq with h | h <;> simp [h]
  · have hL : m.val.length ≤ 33 := hm
    have ha : a.val.length = 22 := by simp
    -- the block, step by step
    have hb1 : (index_mut_back s2).val = [] ++ a.val ++ List.replicate 42 0#u8 := by
      rw [s_post2, s2_post, s1_post, Array.val_to_slice]
      rw [show (Array.repeat 64#usize 0#u8).val = [] ++ List.replicate 22 0#u8 ++ List.replicate 42 0#u8
        by simp [List.replicate_add]]
      exact setSlice!_mid _ _ _ _ _ rfl (by simp)
    have hb2 : (index_mut_back1 s4).val = a.val ++ m.val ++ List.replicate (42 - m.val.length) 0#u8 := by
      rw [s3_post2, s4_post, hb1, List.nil_append,
        show List.replicate 42 0#u8 = List.replicate m.val.length 0#u8 ++
          List.replicate (42 - m.val.length) 0#u8 by rw [← List.replicate_add]; congr 1; omega]
      rw [← List.append_assoc]
      exact setSlice!_mid _ _ _ _ _ (by simp) (by simp)
    have hi : i.val = (a.val ++ m.val).length := by simp [i_post]
    have hb3 : blk3.val = a.val ++ m.val ++ [128#u8] ++ List.replicate (39 - m.val.length) 0#u8 ++
        0#u8 :: [0#u8] := by
      rw [blk3_post, Array.set_val_eq, hb2,
        show 42 - m.val.length = (39 - m.val.length + 2) + 1 by omega, List.replicate_succ,
        set_mid _ _ _ _ _ hi]
      simp [List.replicate_add]
    have hb4 : blk4.val = a.val ++ m.val ++ [128#u8] ++ List.replicate (39 - m.val.length) 0#u8 ++
        i3 :: [0#u8] := by
      rw [blk4_post, Array.set_val_eq, hb3, set_mid _ _ _ _ _ (by simp; omega)]
    have hb5 : r.val = a.val ++ m.val ++ [128#u8] ++ List.replicate (39 - m.val.length) 0#u8 ++
        [i3, i4] := by
      rw [r_post, Array.set_val_eq, hb4,
        show (a.val ++ m.val ++ [128#u8] ++ List.replicate (39 - m.val.length) 0#u8 ++ [i3, 0#u8]) =
          (a.val ++ m.val ++ [128#u8] ++ List.replicate (39 - m.val.length) 0#u8 ++ [i3]) ++ 0#u8 :: []
          by simp,
        set_mid _ _ _ _ _ (by simp; omega)]
      simp
    have hbits : bits.val = 8 * (86 + m.val.length) := by
      rw [bits_post, i1_post]; simp; ring
    rw [padFrom_short _ _ (by rw [← a_post]; simp) (by simp; omega), hb5, ← a_post]
    have h3 : i3.bv = BitVec.ofNat 8 ((8 * (86 + m.val.length)) >>> 8) := by
      rw [i3_post]; exact (cast_u8_bv i2).trans (by rw [i2_post, hbits])
    have h4 : i4.bv = BitVec.ofNat 8 (8 * (86 + m.val.length)) := by
      rw [i4_post]; exact (cast_u8_bv bits).trans (by rw [hbits])
    have h39 : 39 - m.val.length = (33 - m.val.length) + 6 := by omega
    simp [bytes, h3, h4, h39, List.replicate_add]

@[step]
theorem trunc_spec (st : Array U32 8#usize) :
    hash.trunc st ⦃ r => bytes r.val = (ser (wv st.val)).take 16 ⦄ := by
  unfold hash.trunc
  simp only [global_simps]
  step*
  have hv : (Array.from_slice (Array.repeat 16#usize 0#u8) s1).val = s1.val :=
    Array.from_slice_val _ _ (by scalar_tac)
  rw [to_slice_mut_back_post, s2_post, hv, s1_post, ← d_post]
  simp [List.slice]

/-- `thash_short` in terms of its three parts: a block holding the padded
`ADRSc ‖ M`, one compression from the seed state, and the truncated digest. -/
theorem thash_short_parts (pk : hash.Seed) (hpk : SeedOk pk) (A : Spec.Adrs) (M : Spec.Bytes)
    (blk : Array U8 64#usize) (st : Array U32 8#usize) (r : Array U8 16#usize)
    (h1 : bytes blk.val = padFrom 64 (A.compress ++ M))
    (h2 : wv st.val = Spec.SHA256.compress (wv pk.state.val) (bytes blk.val))
    (h3 : bytes r.val = (ser (wv st.val)).take 16) :
    bytes r.val = Spec.thash (bytes pk.pk_seed.val) A M := by
  have hlen : (bytes blk.val).length = 64 := by simp
  rw [thash_eq _ (by simp), h3, h2, ← h1, hashFrom_one _ _ hlen, ← hpk]

/-- The compression of a 64-byte array from its start, as an equation. -/
theorem compress_ok_wv (state : Array U32 8#usize) (blk : Array U8 64#usize) (st : Array U32 8#usize)
    (h : sha256.compress state blk.to_slice 0#usize = ok st) :
    wv st.val = Spec.SHA256.compress (wv state.val) (bytes blk.val) := by
  obtain ⟨v, hv, hp⟩ := spec_imp_exists (compress_spec state blk.to_slice 0#usize (by simp))
  rw [h] at hv
  have e : st = v := by simpa using hv
  subst e
  rw [hp]
  simp [List.take_of_length_le]

@[step]
theorem thash_short_spec (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) (m : Slice U8)
    (hm : m.length ≤ 33) :
    hash.thash_short pk a m ⦃ r =>
      bytes r.val = Spec.thash (bytes pk.pk_seed.val) (adrsS a) (bytes m.val) ⦄ := by
  unfold hash.thash_short
  let* ⟨ blk, blk_post ⟩ ← short_block_spec
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ st, st_post ⟩ ← compress_spec
  let* ⟨ r, r_post ⟩ ← trunc_spec
  rw [s_post, Array.val_to_slice, List.drop_zero,
    List.take_of_length_le (show (bytes blk.val).length ≤ 64 by simp)] at st_post
  exact thash_short_parts pk hpk _ _ blk st r blk_post st_post r_post

@[step]
theorem prf_msg_spec (sk_prf opt_rand : Array U8 16#usize) (m : Slice U8) (hm : Room m.length 152) :
    hash.prf_msg sk_prf opt_rand m ⦃ r =>
      bytes r.val = Spec.PRFmsg (bytes sk_prf.val) (bytes opt_rand.val) (bytes m.val) ⦄ := by
  unfold hash.prf_msg
  have hN : params.N.val = 16 := by simp [params.N]
  have hR := hm
  simp only [Room] at hR
  simp only [step_simps]
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ buf, buf_post, buf_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ buf1, buf1_post, buf1_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
  have hl : buf1.length = 16 + m.length := by
    simp [buf1_len, buf_len, s_post]
  let* ⟨ d, d_post ⟩ ← hmac_sha256_spec
  · simp only [Room, vec_deref_length]; scalar_tac
  let* ⟨ s3, to_slice_mut_back, s3_post, to_slice_mut_back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s4, s4_post, s4_post1 ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
  let* ⟨ s5, s5_post ⟩ ← core.slice.Slice.copy_from_slice.step_spec
  have hv : (Array.from_slice (Array.repeat 16#usize 0#u8) s4).val = s4.val :=
    Array.from_slice_val _ _ (by scalar_tac)
  simp only [to_slice_mut_back_post, s5_post, hv, s4_post, hN, List.slice]
  simp [Spec.PRFmsg, Spec.n, d_post, vec_deref_val, buf1_post, buf_post, s_post, s1_post]

/-- The inner hash of `H_msg`: for a message of at least 16 bytes the first
block is assembled and the rest hashed in place; the result is the same
SHA-256 either way. -/
@[step]
theorem h_msg_inner_spec (r pk_seed pk_root : Array U8 16#usize) (m : Slice U8)
    (hm : Room m.length 120) :
    hash.h_msg_inner r pk_seed pk_root m ⦃ d =>
      bytes d.val = Spec.sha256
        (bytes r.val ++ bytes pk_seed.val ++ bytes pk_root.val ++ bytes m.val) ⦄ := by
  unfold hash.h_msg_inner
  have hN : params.N.val = 16 := by simp [params.N]
  have hR := hm
  simp only [Room] at hR
  simp only [step_simps]
  split
  · rename_i hlen
    have hlen16 : 16 ≤ m.length := by scalar_tac
    simp only [global_simps]
    step*
    · simp [s12_post]
    · simp only [Room]; scalar_tac
    · have hb1 : (index_mut_back s2).val = r.val ++ List.replicate 48 0#u8 := by
        rw [s_post2, s2_post, s1_post]
        simp [List.setSlice!]
      have hb2 : (index_mut_back1 s5).val = r.val ++ pk_seed.val ++ List.replicate 32 0#u8 := by
        rw [s3_post2, s5_post, s4_post, hb1, Array.val_to_slice,
          show List.replicate 48 0#u8 = List.replicate 16 0#u8 ++ List.replicate 32 0#u8
            by simp,
          ← List.append_assoc]
        exact setSlice!_mid _ _ _ _ _ (by simp) (by simp)
      have hb3 : (index_mut_back2 s8).val =
          r.val ++ pk_seed.val ++ pk_root.val ++ List.replicate 16 0#u8 := by
        rw [s6_post2, s8_post, s7_post, hb2, Array.val_to_slice,
          show List.replicate 32 0#u8 = List.replicate 16 0#u8 ++ List.replicate 16 0#u8
            by simp,
          ← List.append_assoc]
        exact setSlice!_mid _ _ _ _ _ (by simp [i1_post]) (by simp)
      have hb4 : (index_mut_back3 s11).val =
          r.val ++ pk_seed.val ++ pk_root.val ++ m.val.take 16 := by
        rw [s9_post2, s11_post, s10_post, hb3]
        have := setSlice!_mid (r.val ++ pk_seed.val ++ pk_root.val) (List.replicate 16 0#u8) []
          (List.slice 0 16 m.val) i2.val (by simp [i2_post]) (by simp [List.slice]; scalar_tac)
        simpa [List.slice] using this
      -- the first block, and the rest of the message
      have hB : bytes (index_mut_back3 s11).val =
          bytes r.val ++ bytes pk_seed.val ++ bytes pk_root.val ++ (bytes m.val).take 16 := by
        rw [hb4]; simp
      have hBl : (bytes r.val ++ bytes pk_seed.val ++ bytes pk_root.val ++
          (bytes m.val).take 16).length = 64 := by
        simp; scalar_tac
      have hs13 : bytes s13.val = (bytes m.val).drop 16 := by
        simp [s13_post, List.slice]
      have hst : wv st.val = Spec.SHA256.compress Spec.SHA256.H0
          (bytes r.val ++ bytes pk_seed.val ++ bytes pk_root.val ++ (bytes m.val).take 16) := by
        rw [st_post, s12_post, Array.val_to_slice, hB, List.drop_zero,
          List.take_of_length_le (Nat.le_of_eq hBl)]
        rfl
      rw [d_post, hst, hs13, ← sha256_prefix64 _ _ hBl]
      simp only [List.append_assoc, List.take_append_drop]
  · let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
    let* ⟨ buf, buf_post, buf_len ⟩ ← hash_extend_from_slice_u8_spec
    let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
    let* ⟨ buf1, buf1_post, buf1_len ⟩ ← hash_extend_from_slice_u8_spec
    let* ⟨ s2, s2_post ⟩ ← Array.to_slice.step_spec
    let* ⟨ buf2, buf2_post, buf2_len ⟩ ← hash_extend_from_slice_u8_spec
    let* ⟨ buf3, buf3_post, buf3_len ⟩ ← hash_extend_from_slice_u8_spec
    have hl : buf3.length = 48 + m.length := by
      simp [buf3_len, buf2_len, buf1_len, buf_len, s_post, s1_post, s2_post]
    let* ⟨ inner, inner_post ⟩ ← sha256_spec
    · simp only [Room, vec_deref_length]; scalar_tac
    simp [inner_post, vec_deref_val, buf3_post, buf2_post, buf1_post, buf_post, s_post, s1_post,
      s2_post]

@[step]
theorem h_msg_spec (r pk_seed pk_root : Array U8 16#usize) (m : Slice U8) (hm : Room m.length 120) :
    hash.h_msg r pk_seed pk_root m ⦃ d =>
      bytes d.val = Spec.Hmsg (bytes r.val) (bytes pk_seed.val) (bytes pk_root.val) (bytes m.val) ⦄ := by
  unfold hash.h_msg
  have hM : params.M.val = 30 := by simp [params.M]
  simp only [step_simps]
  let* ⟨ inner, inner_post ⟩ ← h_msg_inner_spec
  let* ⟨ s4, s4_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ seed, seed_post, seed_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ s5, s5_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ seed1, seed1_post, seed1_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ s6, s6_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ seed2, seed2_post, seed2_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ s7, s7_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ seed3, seed3_post, seed3_len ⟩ ← hash_extend_from_slice_u8_spec
  have hl2 : seed3.length = 68 := by
    simp [seed3_len, seed2_len, seed1_len, seed_len, s4_post, s5_post, s6_post, s7_post]
  let* ⟨ d, d_post ⟩ ← sha256_spec
  · simp only [Room, vec_deref_length]; scalar_tac
  let* ⟨ s9, to_slice_mut_back, s9_post, to_slice_mut_back_post ⟩ ← Array.to_slice_mut_spec
  let* ⟨ s10, s10_post, s10_post1 ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
  let* ⟨ s11, s11_post ⟩ ← core.slice.Slice.copy_from_slice.step_spec
  have hv : (Array.from_slice (Array.repeat 30#usize 0#u8) s10).val = s10.val :=
    Array.from_slice_val _ _ (by scalar_tac)
  simp only [to_slice_mut_back_post, s11_post, hv, s10_post, hM, List.slice]
  simp [Spec.Hmsg, Spec.mgf1, Spec.m, toByte_zero_4, d_post, inner_post, vec_deref_val,
    seed3_post, seed2_post, seed1_post, seed_post,
    s4_post, s5_post, s6_post, s7_post]

/-! Iterated single-block hashing in place: `chain_blocks` and its pure model. -/

/-- One step of `chain_blocks` on a block, on spec bytes: write `t` into the
last address word (bytes 18..22), then replace the value (bytes 22..38) by
`Trunc_n` of the compression of the block from `st`. -/
def stepBlock (st : List Spec.SHA256.Word) (B : Spec.Bytes) (t : Nat) : Spec.Bytes :=
  let B' := B.take 18 ++ Spec.toByte t 4 ++ B.drop 22
  B'.take 22 ++ (ser (Spec.SHA256.compress st B')).take 16 ++ B'.drop 38

/-- The steps `s`, …, `e − 1` of `chain_blocks` on one block (none if `e ≤ s`). -/
def runBlock (st : List Spec.SHA256.Word) (B : Spec.Bytes) (s e : Nat) : Spec.Bytes :=
  (List.range (e - s)).foldl (fun B k => stepBlock st B (s + k)) B

theorem sha_compress_length (st : List Spec.SHA256.Word) (B : Spec.Bytes) :
    (Spec.SHA256.compress st B).length = 8 := by
  simp [Spec.SHA256.compress]

theorem ser_length (l : List Spec.SHA256.Word) : (ser l).length = 4 * l.length := by
  simp [ser, Spec.toByte, List.length_flatMap]; omega

theorem toByte4_eq (t : Nat) : Spec.toByte t 4 =
    [BitVec.ofNat 8 (t >>> 24), BitVec.ofNat 8 (t >>> 16), BitVec.ofNat 8 (t >>> 8), BitVec.ofNat 8 t] := by
  simp [Spec.toByte, show List.range 4 = [0, 1, 2, 3] from rfl]

theorem adrs_compress_length (A : Spec.Adrs) : A.compress.length = 22 := by
  rw [compress_eq]; rfl

theorem compress_word3 (A : Spec.Adrs) (t : Nat) :
    { A with word3 := t }.compress = A.compress.take 18 ++ Spec.toByte t 4 := by
  rw [compress_eq, compress_eq, toByte4_eq]; rfl

theorem compress_typ (A : Spec.Adrs) (ty : Nat) :
    A.compress.set 9 (BitVec.ofNat 8 ty) = { A with typ := ty }.compress := by
  rw [compress_eq, compress_eq]; rfl


/-- The padding after a 22-byte address and a message of `k ≤ 33` bytes, in one block. -/
def padTail (k : Nat) : Spec.Bytes :=
  [0x80#8] ++ List.replicate (33 - k) 0#8 ++
    [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, BitVec.ofNat 8 ((8 * (86 + k)) >>> 8), BitVec.ofNat 8 (8 * (86 + k))]

theorem padTail_length (k : Nat) (hk : k ≤ 33) : (padTail k).length = 42 - k := by
  simp [padTail]; omega

theorem padFrom_blk (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length ≤ 33) :
    padFrom 64 (A.compress ++ m) = A.compress ++ (m ++ padTail m.length) := by
  rw [padFrom_short _ _ (adrs_compress_length A) hm]; simp [padTail]

theorem padFrom_blk_length (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length ≤ 33) :
    (padFrom 64 (A.compress ++ m)).length = 64 := by
  rw [padFrom_blk _ _ hm]; simp [adrs_compress_length, padTail_length _ hm]; omega

/-- Writing a step number into the last address word of a block. -/
theorem counter_set (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length ≤ 33) (t : Nat) :
    (padFrom 64 (A.compress ++ m)).take 18 ++ Spec.toByte t 4 ++ (padFrom 64 (A.compress ++ m)).drop 22 =
      padFrom 64 ({ A with word3 := t }.compress ++ m) := by
  rw [padFrom_blk _ _ hm, padFrom_blk _ _ hm, compress_word3 A t]
  have hc := adrs_compress_length A
  rw [List.take_append_of_le_length (by omega), List.drop_left' hc]

theorem counter_self (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length ≤ 33) :
    (padFrom 64 (A.compress ++ m)).take 18 ++ Spec.toByte A.word3 4 ++ (padFrom 64 (A.compress ++ m)).drop 22 =
      padFrom 64 (A.compress ++ m) := by
  rw [counter_set _ _ hm]

/-- One step on the block of a 16-byte value. -/
theorem stepBlock_short (st : List Spec.SHA256.Word) (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length = 16)
    (t : Nat) :
    stepBlock st (padFrom 64 (A.compress ++ m)) t =
      padFrom 64 ({ A with word3 := t }.compress ++
        (ser (Spec.SHA256.compress st (padFrom 64 ({ A with word3 := t }.compress ++ m)))).take 16) := by
  unfold stepBlock
  simp only []
  rw [counter_set _ _ (by omega)]
  have hl : ((ser (Spec.SHA256.compress st (padFrom 64 ({ A with word3 := t }.compress ++ m)))).take 16).length = 16 := by
    simp [ser_length, sha_compress_length]
  have hc := adrs_compress_length { A with word3 := t }
  have e1 : (padFrom 64 ({ A with word3 := t }.compress ++ m)).take 22 = { A with word3 := t }.compress := by
    rw [padFrom_blk _ _ (by omega), List.take_left' hc]
  have e2 : (padFrom 64 ({ A with word3 := t }.compress ++ m)).drop 38 = padTail 16 := by
    rw [padFrom_blk _ _ (by omega), ← List.append_assoc, List.drop_left' (by simp [hc, hm]), hm]
  rw [e1, e2]
  generalize List.take 16 (ser (Spec.SHA256.compress st
    (padFrom 64 ({ A with word3 := t }.compress ++ m)))) = H at hl ⊢
  rw [padFrom_blk _ H (by omega), hl]
  simp

/-- The value held in a block that has been stepped. -/
theorem stepBlock_value (st : List Spec.SHA256.Word) (B : Spec.Bytes) (hB : B.length = 64) (t : Nat) :
    ((stepBlock st B t).drop 22).take 16 =
      (ser (Spec.SHA256.compress st (B.take 18 ++ Spec.toByte t 4 ++ B.drop 22))).take 16 := by
  unfold stepBlock
  simp only []
  have hl : ((ser (Spec.SHA256.compress st (B.take 18 ++ Spec.toByte t 4 ++ B.drop 22))).take 16).length = 16 := by
    simp [ser_length, sha_compress_length]
  have h22 : ((B.take 18 ++ Spec.toByte t 4 ++ B.drop 22).take 22).length = 22 := by
    simp [Spec.toByte]; omega
  rw [List.append_assoc, List.drop_left' h22, List.take_left' hl]

theorem block_value (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length ≤ 33) :
    ((padFrom 64 (A.compress ++ m)).drop 22).take 16 = (m ++ padTail m.length).take 16 := by
  rw [padFrom_blk _ _ hm, List.drop_left' (adrs_compress_length A)]

theorem block_set_typ (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length ≤ 33) (ty : Nat) :
    (padFrom 64 (A.compress ++ m)).set 9 (BitVec.ofNat 8 ty) = padFrom 64 ({ A with typ := ty }.compress ++ m) := by
  rw [padFrom_blk _ _ hm, padFrom_blk _ _ hm, List.set_append_left _ _ (by simp [adrs_compress_length]),
    compress_typ]

theorem hashFrom_length (st : List Spec.SHA256.Word) (hst : st.length = 8) (P : Spec.Bytes) :
    (hashFrom st P).length = 8 := by
  unfold hashFrom
  have : ∀ (l : List Nat) (st : List Spec.SHA256.Word), st.length = 8 →
      (l.foldl (fun st k => Spec.SHA256.compress st (Spec.SHA256.blockAt P k)) st).length = 8 := by
    intro l
    induction l with
    | nil => intro st h; simpa using h
    | cons x l ih => intro st _; exact ih _ (sha_compress_length _ _)
  exact this _ _ hst

theorem thash_length (pk : Spec.Bytes) (hpk : pk.length = 16) (A : Spec.Adrs) (m : Spec.Bytes) :
    (Spec.thash pk A m).length = 16 := by
  rw [thash_eq pk hpk]
  simp [ser_length, hashFrom_length _ (sha_compress_length _ _)]

/-- One compression of the block of a short message, from the seed state, is the tweakable hash. -/
theorem thash_one (pk : Spec.Bytes) (hpk : pk.length = 16) (A : Spec.Adrs) (m : Spec.Bytes)
    (hm : m.length ≤ 33) :
    (ser (Spec.SHA256.compress (Spec.SHA256.compress Spec.SHA256.H0 (pk ++ List.replicate 48 0#8))
      (padFrom 64 (A.compress ++ m)))).take 16 = Spec.thash pk A m := by
  rw [thash_eq pk hpk, hashFrom_one _ _ (padFrom_blk_length _ _ hm)]

theorem chain_succ (x : Spec.Bytes) (s n : Nat) (pk : Spec.Bytes) (A : Spec.Adrs) :
    Spec.chain x s (n + 1) pk A = Spec.thash pk { A with word3 := s + n } (Spec.chain x s n pk A) := by
  simp only [Spec.chain, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Spec.F]

theorem chain_length (pk : Spec.Bytes) (hpk : pk.length = 16) (x : Spec.Bytes) (hx : x.length = 16)
    (s n : Nat) (A : Spec.Adrs) : (Spec.chain x s n pk A).length = 16 := by
  cases n with
  | zero => simpa [Spec.chain] using hx
  | succ n => rw [chain_succ]; exact thash_length pk hpk _ _

theorem runBlock_succ (st : List Spec.SHA256.Word) (B : Spec.Bytes) (s n : Nat) :
    runBlock st B s (s + (n + 1)) = stepBlock st (runBlock st B s (s + n)) (s + n) := by
  simp [runBlock, List.range_succ, List.foldl_append]

theorem runBlock_le (st : List Spec.SHA256.Word) (B : Spec.Bytes) (s e : Nat) (h : e ≤ s) :
    runBlock st B s e = B := by
  simp [runBlock, Nat.sub_eq_zero_of_le h]

theorem runBlock_one (st : List Spec.SHA256.Word) (B : Spec.Bytes) (s : Nat) :
    runBlock st B s (s + 1) = stepBlock st B s := by
  simp [runBlock]

/-- `B` is the block holding the value `v` at an address that is `A` up to its last word. -/
def ValBlk (A : Spec.Adrs) (v B : Spec.Bytes) : Prop :=
  ∃ w, B = padFrom 64 ({ A with word3 := w }.compress ++ v)

/-- One step with the seed state is `F` (or `PRF`) at the address of the step. -/
theorem stepBlock_thash (pk : Spec.Bytes) (hpk : pk.length = 16) (st : List Spec.SHA256.Word)
    (hst : st = Spec.SHA256.compress Spec.SHA256.H0 (pk ++ List.replicate 48 0#8))
    (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length = 16) (t : Nat) :
    stepBlock st (padFrom 64 (A.compress ++ m)) t =
      padFrom 64 ({ A with word3 := t }.compress ++ Spec.thash pk { A with word3 := t } m) := by
  rw [stepBlock_short _ _ _ hm, hst, thash_one pk hpk _ _ (by omega)]

/-- A run of steps with the seed state is `chain`. -/
theorem runBlock_chain (pk : Spec.Bytes) (hpk : pk.length = 16) (st : List Spec.SHA256.Word)
    (hst : st = Spec.SHA256.compress Spec.SHA256.H0 (pk ++ List.replicate 48 0#8))
    (A : Spec.Adrs) (m B : Spec.Bytes) (hm : m.length = 16) (hB : ValBlk A m B) (s n : Nat) :
    ValBlk A (Spec.chain m s n pk A) (runBlock st B s (s + n)) := by
  induction n with
  | zero => simpa [runBlock, Spec.chain] using hB
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih
    rw [runBlock_succ, hw, stepBlock_thash pk hpk st hst _ _ (chain_length pk hpk m hm s n A),
      chain_succ]
    exact ⟨s + n, rfl⟩

theorem ValBlk_value (A : Spec.Adrs) (v B : Spec.Bytes) (hv : v.length = 16) (hB : ValBlk A v B) :
    (B.drop 22).take 16 = v := by
  obtain ⟨w, rfl⟩ := hB
  rw [block_value _ _ (by omega), List.take_left' hv]

/-- The value of a pair block after its one step, numbered by its own last address word: `H`. -/
theorem stepBlock_pair_value (pk : Spec.Bytes) (hpk : pk.length = 16) (st : List Spec.SHA256.Word)
    (hst : st = Spec.SHA256.compress Spec.SHA256.H0 (pk ++ List.replicate 48 0#8))
    (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length ≤ 33) :
    ((stepBlock st (padFrom 64 (A.compress ++ m)) A.word3).drop 22).take 16 = Spec.thash pk A m := by
  rw [stepBlock_value _ _ (padFrom_blk_length _ _ hm), counter_self _ _ hm, hst, thash_one pk hpk _ _ hm]

@[step]
theorem value_spec (block : Array U8 64#usize) :
    hash.value block ⦃ r => bytes r.val = ((bytes block.val).drop 22).take 16 ⦄ := by
  unfold hash.value
  step*
  have hv : (Array.from_slice (Array.repeat 16#usize 0#u8) s1).val = s1.val :=
    Array.from_slice_val _ _ (by scalar_tac)
  rw [to_slice_mut_back_post, s2_post, hv, s1_post]
  simp [List.slice, bytes]

@[step]
theorem pair_block_spec (adrs : address.Adrs) (l r : Array U8 16#usize) :
    hash.pair_block adrs l r ⦃ b =>
      bytes b.val = padFrom 64 ((adrsS adrs).compress ++ (bytes l.val ++ bytes r.val)) ⦄ := by
  unfold hash.pair_block
  simp only [global_simps]
  step*
  have hb1 : (index_mut_back s2).val = [] ++ l.val ++ List.replicate 16 0#u8 := by
    rw [s_post2, s2_post, s1_post, Array.val_to_slice,
      show (Array.repeat 32#usize 0#u8).val = [] ++ List.replicate 16 0#u8 ++ List.replicate 16 0#u8
        by simp]
    exact setSlice!_mid _ _ _ _ _ rfl (by simp)
  have hb2 : (index_mut_back1 s5).val = l.val ++ r.val ++ [] := by
    rw [s3_post2, s5_post, s4_post, Array.val_to_slice, hb1, List.nil_append,
      show l.val ++ List.replicate 16 0#u8 = l.val ++ List.replicate 16 0#u8 ++ [] by simp]
    exact setSlice!_mid _ _ _ _ _ (by simp) (by simp)
  simp [b_post, s6_post, hb2]

theorem set4_eq {α} (l : List α) (h : 22 ≤ l.length) (a b c d : α) :
    (((l.set 18 a).set 19 b).set 20 c).set 21 d = l.take 18 ++ [a, b, c, d] ++ l.drop 22 := by
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    have hm : min 18 l.length = 18 := by omega
    simp only [List.getElem_set, List.getElem_append, List.length_take, List.length_append,
      List.getElem_take, List.getElem_drop, List.length_cons, List.length_nil, hm]
    split_ifs <;> (try subst_vars) <;> first | rfl | omega | (congr 1; omega)

theorem bytes_set (l : List U8) (k : Nat) (x : U8) : bytes (l.set k x) = (bytes l).set k x.bv := by
  simp [bytes, List.map_set]

theorem bytes_setSlice (l s : List U8) (i : Nat) (h : i + s.length ≤ l.length) :
    bytes (l.setSlice! i s) = (bytes l).take i ++ bytes s ++ (bytes l).drop (i + s.length) := by
  have hm : min s.length (l.length - i) = s.length := by omega
  simp [List.setSlice!, hm]

theorem cast_u8_bv32 (x : U32) : U8.bv (UScalar.cast .U8 x) = BitVec.ofNat 8 x.val := cast_u8_bv x

theorem chain_blocks_inner_spec (state : Array U32 8#usize) (blocks0 : Slice (Array U8 64#usize))
    («end» : Slice U32) (i : Usize) (s0 : Nat)
    (hi : i.val < blocks0.length) (he : i.val < «end».length)
    (blocks : Slice (Array U8 64#usize)) (t : U32)
    (hlen : blocks.length = blocks0.length)
    (hother : ∀ j, j ≠ i.val → blocks.val[j]! = blocks0.val[j]!)
    (hst : s0 ≤ t.val) (hte : t.val ≤ («end».val[i.val]!).val ∨ t.val = s0)
    (hcur : bytes (blocks.val[i.val]!).val =
      runBlock (wv state.val) (bytes (blocks0.val[i.val]!).val) s0 t.val) :
    hash.chain_blocks_portable_loop0_loop0 state blocks «end» i t ⦃ r =>
      r.length = blocks0.length ∧ (∀ j, j ≠ i.val → r.val[j]! = blocks0.val[j]!) ∧
      bytes (r.val[i.val]!).val =
        runBlock (wv state.val) (bytes (blocks0.val[i.val]!).val) s0 («end».val[i.val]!).val ⦄ := by
  unfold hash.chain_blocks_portable_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Slice (Array U8 64#usize) × U32) => («end».val[i.val]!).val - p.2.val)
    (inv := fun p => p.1.length = blocks0.length ∧ (∀ j, j ≠ i.val → p.1.val[j]! = blocks0.val[j]!) ∧
      s0 ≤ p.2.val ∧ (p.2.val ≤ («end».val[i.val]!).val ∨ p.2.val = s0) ∧
      bytes (p.1.val[i.val]!).val =
        runBlock (wv state.val) (bytes (blocks0.val[i.val]!).val) s0 p.2.val)
  · rintro ⟨blocks, t⟩ ⟨h1, h2, h3, h4, h5⟩
    simp only [hash.chain_blocks_portable_loop0_loop0.body]
    simp only at h1 h2 h3 h4 h5
    step*
    all_goals try (simp [*]; done)
    · have hil : i.val < blocks.val.length := by scalar_tac
      have htlt : t.val < («end».val[i.val]!).val := by
        rw [getElem!_eq _ _ (by scalar_tac), ← i1_post]; scalar_tac
      have e2 : a2 = a1 := by simp [a2_post, index_mut_back_post]
      have e4 : a4 = a3 := by simp [a4_post, index_mut_back1_post]
      have e6 : a6 = a5 := by simp [a6_post, index_mut_back2_post]
      have e8 : a8 = a7 := by simp [a8_post, index_mut_back3_post]
      have e9 : a9 = a7 := by simp [a9_post, index_mut_back3_post]
      have h7 : bytes a7.val = (bytes (blocks.val[i.val]).val).take 18 ++ Spec.toByte t.val 4 ++
          (bytes (blocks.val[i.val]).val).drop 22 := by
        rw [a7_post, e6, a5_post, e4, a3_post, e2, a1_post, a_post]
        simp only [Array.set_val_eq, bytes_set, show (18#usize).val = 18 from rfl,
          show (19#usize).val = 19 from rfl, show (20#usize).val = 20 from rfl,
          show (21#usize).val = 21 from rfl]
        rw [set4_eq _ (by simp), toByte4_eq, i8_post, i7_post, i5_post, i3_post, cast_u8_bv32, cast_u8_bv32,
          cast_u8_bv32, cast_u8_bv32, i6_post, i4_post, i2_post]
      have hst' : wv st.val = Spec.SHA256.compress (wv state.val) (bytes a7.val) := by
        rw [st_post, s_post, e8, Array.val_to_slice, List.drop_zero,
          List.take_of_length_le (by simp)]
      have hfin : bytes (index_mut_back5 s3).val = stepBlock (wv state.val) (bytes (blocks.val[i.val]).val) t.val := by
        rw [s1_post2, s3_post, s2_post, e9, Array.val_to_slice]
        unfold stepBlock
        simp only []
        rw [← h7]
        rw [bytes_setSlice _ _ _ (by simp), d_post, hst']
        simp
      refine ⟨by simp [index_mut_back4_post, index_mut_back3_post, index_mut_back2_post,
          index_mut_back1_post, index_mut_back_post, h1], ?_, by omega, ?_, ?_, ?_⟩
      · intro j hj
        simp only [index_mut_back4_post, index_mut_back3_post, index_mut_back2_post,
          index_mut_back1_post, index_mut_back_post, Slice.set_val_eq]
        rw [getElem!_set_ne' _ _ _ _ (Ne.symm hj), getElem!_set_ne' _ _ _ _ (Ne.symm hj),
          getElem!_set_ne' _ _ _ _ (Ne.symm hj), getElem!_set_ne' _ _ _ _ (Ne.symm hj),
          getElem!_set_ne' _ _ _ _ (Ne.symm hj)]
        exact h2 j hj
      · left; rw [t1_post]; omega
      · have hl' : i.val < (index_mut_back3 a7).val.length := by
          simp only [index_mut_back3_post, index_mut_back2_post, index_mut_back1_post,
            index_mut_back_post, Slice.set_val_eq, List.length_set]; exact hil
        rw [index_mut_back4_post, Slice.set_val_eq, getElem!_set_self' _ _ _ hl', hfin, t1_post,
          show t.val + 1 = s0 + ((t.val - s0) + 1) by omega, runBlock_succ,
          show s0 + (t.val - s0) = t.val by omega, ← h5, getElem!_eq _ _ hil]
      · rw [t1_post]; omega
    · have hge : («end».val[i.val]!).val ≤ t.val := by
        rw [getElem!_eq _ _ (by scalar_tac), ← i1_post]; scalar_tac
      refine ⟨h1, h2, ?_⟩
      rw [h5]
      rcases h4 with h4 | h4
      · rw [show t.val = («end».val[i.val]!).val by omega]
      · rw [h4, runBlock_le _ _ _ _ (by omega), runBlock_le _ _ _ _ (by omega)]
  · exact ⟨hlen, hother, hst, hte, hcur⟩

theorem chain_blocks_loop0_spec (state : Array U32 8#usize) (blocks0 : Slice (Array U8 64#usize))
    (start «end» : Slice U32)
    (hs : blocks0.length ≤ start.length) (he : blocks0.length ≤ «end».length)
    (blocks : Slice (Array U8 64#usize)) (i : Usize)
    (hi : i.val ≤ blocks0.length) (hlen : blocks.length = blocks0.length)
    (hdone : ∀ j, j < i.val → bytes (blocks.val[j]!).val =
      runBlock (wv state.val) (bytes (blocks0.val[j]!).val) (start.val[j]!).val («end».val[j]!).val)
    (hrest : ∀ j, i.val ≤ j → blocks.val[j]! = blocks0.val[j]!) :
    hash.chain_blocks_portable_loop0 state blocks start «end» i ⦃ r =>
      r.length = blocks0.length ∧ ∀ j, j < blocks0.length → bytes (r.val[j]!).val =
        runBlock (wv state.val) (bytes (blocks0.val[j]!).val) (start.val[j]!).val («end».val[j]!).val ⦄ := by
  unfold hash.chain_blocks_portable_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Slice (Array U8 64#usize) × Usize) => blocks0.length - p.2.val)
    (inv := fun p => p.2.val ≤ blocks0.length ∧ p.1.length = blocks0.length ∧
      (∀ j, j < p.2.val → bytes (p.1.val[j]!).val =
        runBlock (wv state.val) (bytes (blocks0.val[j]!).val) (start.val[j]!).val («end».val[j]!).val) ∧
      (∀ j, p.2.val ≤ j → p.1.val[j]! = blocks0.val[j]!))
  · rintro ⟨blocks, i⟩ ⟨h1, h2, h3, h4⟩
    simp only [hash.chain_blocks_portable_loop0.body]
    simp only at h1 h2 h3 h4
    simp only [step_simps]
    spec_split
    · let* ⟨ t, t_post ⟩ ← Slice.index_usize_spec
      have hib : i.val < blocks0.length := by scalar_tac
      let* ⟨ b1, b1_len, b1_other, b1_cur ⟩ ← chain_blocks_inner_spec state blocks «end» i t.val
        (by scalar_tac) (by scalar_tac) blocks t rfl (fun _ _ => rfl) (le_refl _) (Or.inr rfl)
        (by simp [runBlock])
      let* ⟨ i2, i2_post ⟩ ← Usize.add_spec
      have hts : t.val = (start.val[i.val]!).val := by
        rw [t_post, getElem!_eq _ _ (by scalar_tac)]
      refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, by scalar_tac⟩
      · intro j hj
        rw [i2_post] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · rw [b1_other j (by omega)]; exact h3 j hj
        · subst hj
          rw [b1_cur, hts, h4 _ (le_refl _)]
      · intro j hj
        rw [b1_other j (by scalar_tac)]; exact h4 j (by scalar_tac)
    · simp only [step_simps]
      have hib : i.val = blocks0.length := by scalar_tac
      exact ⟨h2, fun j hj => h3 j (by omega)⟩
  · exact ⟨hi, hlen, hdone, hrest⟩

/-- `chain_blocks_portable`: block `i` takes the steps `start[i]`, …, `end[i] − 1`. -/
theorem chain_blocks_portable_spec (state : Array U32 8#usize) (blocks : Slice (Array U8 64#usize))
    (start «end» : Slice U32)
    (hs : blocks.length ≤ start.length) (he : blocks.length ≤ «end».length) :
    hash.chain_blocks_portable state blocks start «end» ⦃ r =>
      r.length = blocks.length ∧ ∀ i, i < blocks.length → bytes (r.val[i]!).val =
        runBlock (wv state.val) (bytes (blocks.val[i]!).val) (start.val[i]!).val («end».val[i]!).val ⦄ := by
  unfold hash.chain_blocks_portable
  exact chain_blocks_loop0_spec state blocks start «end» hs he blocks 0#usize (by simp) rfl
    (fun j hj => by simp at hj) (fun _ _ => rfl)

/-- The value held in a 64-byte block (bytes 22..38). -/
def blkVal (b : Array U8 64#usize) : Spec.Bytes := ((bytes b.val).drop 22).take 16

theorem blkVal_length (b : Array U8 64#usize) : (blkVal b).length = 16 := by
  simp [blkVal]

theorem flatMap_blkVal_length (blocks : List (Array U8 64#usize)) (i : Nat) :
    ((List.range i).flatMap fun (j : Nat) => blkVal blocks[j]!).length = 16 * i := by
  induction i with
  | zero => simp
  | succ i ih => rw [List.range_succ, List.flatMap_append]; simp [blkVal_length]; ring

theorem hash_LEN_eq : params.LEN = 35#usize := by simp [global_simps]

theorem thash_values_loop0_spec (blocks : Array (Array U8 64#usize) 35#usize) (C : Spec.Bytes)
    (hC : C.length = 22) (buf : Array U8 640#usize) (i : Usize) (hi : i.val ≤ 35)
    (hinv : bytes buf.val = C ++ (List.range i.val).flatMap (fun (j : Nat) => blkVal blocks.val[j]!) ++
      List.replicate (618 - 16 * i.val) 0#8) :
    hash.thash_values_loop0 blocks buf i ⦃ r =>
      bytes r.val = C ++ (List.range 35).flatMap (fun (j : Nat) => blkVal blocks.val[j]!) ++
        List.replicate 58 0#8 ⦄ := by
  unfold hash.thash_values_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array U8 640#usize × Usize) => 35 - p.2.val)
    (inv := fun p => p.2.val ≤ 35 ∧ bytes p.1.val = C ++
      (List.range p.2.val).flatMap (fun (j : Nat) => blkVal blocks.val[j]!) ++
      List.replicate (618 - 16 * p.2.val) 0#8)
  · rintro ⟨buf, i⟩ ⟨h1, h2⟩
    simp only [hash.thash_values_loop0.body, hash_LEN_eq, global_simps]
    simp only at h1 h2
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    have hil : i.val < 35 := by scalar_tac
    have hF := flatMap_blkVal_length blocks.val i.val
    have hlen : (C ++ (List.range i.val).flatMap (fun (j : Nat) => blkVal blocks.val[j]!)).length =
        i2.val := by simp only [List.length_append, hC, hF, i2_post, i1_post]
    have hs1 : bytes s1.val = blkVal blocks.val[i.val]! := by
      rw [s1_post, a_post, getElem!_eq _ _ (by scalar_tac)]
      simp [blkVal, List.slice]
    have hs1len : s1.val.length = 16 := by scalar_tac
    have hbl : buf.val.length = 640 := by simp
    rw [s_post2, s2_post, bytes_setSlice _ _ _ (by rw [hs1len, hbl]; scalar_tac), h2, hs1len, hs1,
      List.take_left' hlen, ← List.drop_drop, List.drop_left' hlen, i5_post,
      List.range_succ, List.flatMap_append, List.drop_replicate]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    congr 3
  · exact ⟨hi, hinv⟩

theorem thash_values_loop1_spec (buf : Array U8 640#usize) (S0 : List Spec.SHA256.Word)
    (st : Array U32 8#usize) (off : Usize)
    (hoff : off.val % 64 = 0) (hle : off.val ≤ 640)
    (hinv : wv st.val = (List.range (off.val / 64)).foldl
      (fun st k => Spec.SHA256.compress st (Spec.SHA256.blockAt (bytes buf.val) k)) S0) :
    hash.thash_values_loop1 buf st off ⦃ r => wv r.val = hashFrom S0 (bytes buf.val) ⦄ := by
  unfold hash.thash_values_loop1
  apply loop.spec_decr_nat
    (measure := fun (q : Array U32 8#usize × Usize) => 640 - q.2.val)
    (inv := fun q => q.2.val % 64 = 0 ∧ q.2.val ≤ 640 ∧
      wv q.1.val = (List.range (q.2.val / 64)).foldl
        (fun st k => Spec.SHA256.compress st (Spec.SHA256.blockAt (bytes buf.val) k)) S0)
  · rintro ⟨st, off⟩ ⟨hoff, hle, hinv⟩
    simp only [hash.thash_values_loop1.body]
    simp only at hoff hle hinv
    have h64 : off.val = 640 ∨ off.val + 64 ≤ 640 := by omega
    step*
    · refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have e : off1.val / 64 = off.val / 64 + 1 := by scalar_tac
      have e2 : 64 * (off.val / 64) = off.val := by omega
      rw [e, List.range_succ, List.foldl_append, ← hinv, st1_post, s_post]
      simp [Spec.SHA256.blockAt, e2]
    · have : off.val = 640 := by scalar_tac
      rw [this] at hinv
      rw [hinv, hashFrom]
      simp
  · exact ⟨hoff, hle, hinv⟩

theorem toByte_5168 : Spec.toByte (8 * (64 + 582)) 8 = [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0x14#8, 0x30#8] := by
  decide

/-- The buffer of `thash_values`: `ADRSc ‖ M` and its padding, for a 560-byte `M`. -/
theorem padFrom_values (C M : Spec.Bytes) (hC : C.length = 22) (hM : M.length = 560) :
    (((C ++ M ++ List.replicate 58 0#8).set 582 0x80#8).set 638 0x14#8).set 639 0x30#8 =
      padFrom 64 (C ++ M) := by
  have hl : (C ++ M).length = 582 := by simp [hC, hM]
  rw [padFrom, hl, toByte_5168, List.append_assoc C M, List.set_append_right _ _ (by omega),
    List.set_append_right _ _ (by omega), List.set_append_right _ _ (by omega), hC,
    List.set_append_right _ _ (by omega), List.set_append_right _ _ (by omega),
    List.set_append_right _ _ (by omega), hM]
  simp only [List.append_assoc]
  congr 2

@[step]
theorem thash_values_spec (pk : hash.Seed) (hpk : SeedOk pk) (adrs : address.Adrs)
    (blocks : Array (Array U8 64#usize) 35#usize) :
    hash.thash_values pk adrs blocks ⦃ r =>
      bytes r.val = Spec.thash (bytes pk.pk_seed.val) (adrsS adrs)
        ((List.range 35).flatMap fun (j : Nat) => blkVal blocks.val[j]!) ⦄ := by
  unfold hash.thash_values
  step*
  have hb1 : bytes (index_mut_back s2).val = (adrsS adrs).compress ++ List.replicate 618 0#8 := by
    have hr : (Array.repeat 640#usize 0#u8).val = List.replicate 640 0#u8 := Array.repeat_val ..
    rw [s_post2, s2_post, s1_post, Array.val_to_slice, hr,
      bytes_setSlice _ _ _ (by simp only [List.length_replicate]; scalar_tac), ← a_post]
    simp only [bytes, List.map_replicate, List.take_zero, List.nil_append, List.drop_replicate]
    have : (a.val).length = 22 := by simp
    rw [this]; rfl
  let* ⟨ buf2, buf2_post ⟩ ← thash_values_loop0_spec blocks (adrsS adrs).compress
    (adrs_compress_length _) (index_mut_back s2) 0#usize (by simp) (by rw [hb1]; rfl)
  let* ⟨ buf3, buf3_post ⟩ ← Array.update_spec
  let* ⟨ buf4, buf4_post ⟩ ← Array.update_spec
  let* ⟨ a1, a1_post ⟩ ← Array.update_spec
  have hP : bytes a1.val = padFrom 64 ((adrsS adrs).compress ++
      (List.range 35).flatMap fun (j : Nat) => blkVal blocks.val[j]!) := by
    rw [a1_post, buf4_post, buf3_post]
    simp only [Array.set_val_eq, bytes_set]
    rw [buf2_post]
    exact padFrom_values _ _ (adrs_compress_length _) (by simpa using flatMap_blkVal_length blocks.val 35)
  let* ⟨ st, st_post ⟩ ← thash_values_loop1_spec a1 (wv pk.state.val) pk.state 0#usize
    (by simp) (by simp) (by simp)
  let* ⟨ r, r_post ⟩ ← trunc_spec
  rw [r_post, st_post, hP, thash_eq _ (by simp), ← hpk]

end slhdsa
