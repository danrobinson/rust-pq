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
theorem thash_short_spec (pk : hash.Seed) (hpk : SeedOk pk) (a : address.Adrs) (m : Slice U8)
    (hm : m.length ≤ 33) :
    hash.thash_short pk a m ⦃ r =>
      bytes r.val = Spec.thash (bytes pk.pk_seed.val) (adrsS a) (bytes m.val) ⦄ := by
  rename' a => adrs
  unfold hash.thash_short
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
    have hb5 : blk5.val = a.val ++ m.val ++ [128#u8] ++ List.replicate (39 - m.val.length) 0#u8 ++
        [i3, i4] := by
      rw [blk5_post, Array.set_val_eq, hb4,
        show (a.val ++ m.val ++ [128#u8] ++ List.replicate (39 - m.val.length) 0#u8 ++ [i3, 0#u8]) =
          (a.val ++ m.val ++ [128#u8] ++ List.replicate (39 - m.val.length) 0#u8 ++ [i3]) ++ 0#u8 :: []
          by simp,
        set_mid _ _ _ _ _ (by simp; omega)]
      simp
    have hbits : bits.val = 8 * (86 + m.val.length) := by
      rw [bits_post, i1_post]; simp; ring
    have hblock : bytes blk5.val = padFrom 64 ((adrsS adrs).compress ++ bytes m.val) := by
      rw [padFrom_short _ _ (by rw [← a_post]; simp) (by simp; omega), hb5, ← a_post]
      have h3 : i3.bv = BitVec.ofNat 8 ((8 * (86 + m.val.length)) >>> 8) := by
        rw [i3_post]; exact (cast_u8_bv i2).trans (by rw [i2_post, hbits])
      have h4 : i4.bv = BitVec.ofNat 8 (8 * (86 + m.val.length)) := by
        rw [i4_post]; exact (cast_u8_bv bits).trans (by rw [hbits])
      have h39 : 39 - m.val.length = (33 - m.val.length) + 6 := by omega
      simp [bytes, h3, h4, h39, List.replicate_add]
    have hlen : (bytes blk5.val).length = 64 := by simp
    rw [thash_eq _ (by simp)]
    simp only [to_slice_mut_back_post, s8_post]
    have hv : (Array.from_slice (Array.repeat 16#usize 0#u8) s7).val = s7.val :=
      Array.from_slice_val _ _ (by scalar_tac)
    rw [s5_post, Array.val_to_slice, List.drop_zero, List.take_of_length_le (by omega)] at st_post
    rw [hv, s7_post, ← hblock, hashFrom_one _ _ hlen, ← hpk, ← st_post, ← d_post]
    simp [List.slice]

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

@[step]
theorem h_msg_spec (r pk_seed pk_root : Array U8 16#usize) (m : Slice U8) (hm : Room m.length 120) :
    hash.h_msg r pk_seed pk_root m ⦃ d =>
      bytes d.val = Spec.Hmsg (bytes r.val) (bytes pk_seed.val) (bytes pk_root.val) (bytes m.val) ⦄ := by
  unfold hash.h_msg
  have hM : params.M.val = 30 := by simp [params.M]
  have hR := hm
  simp only [Room] at hR
  simp only [step_simps]
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
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
    seed3_post, seed2_post, seed1_post, seed_post, buf3_post, buf2_post, buf1_post, buf_post,
    s_post, s1_post, s2_post, s4_post, s5_post, s6_post, s7_post]

end slhdsa
