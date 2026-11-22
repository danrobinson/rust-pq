import Slhdsa.Proofs.Sha512
import Slhdsa.Proofs.Util
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

theorem toByte_zero (k : Nat) : Spec.toByte 0 k = List.replicate k 0#8 := by
  apply List.ext_getElem
  · simp [Spec.toByte]
  · intro i h1 h2
    simp [Spec.toByte]

/-- The hash lengths of the SHA-2 parameter sets of FIPS 205. -/
def NOk (N : Usize) : Prop := N.val = 16 ∨ N.val = 24 ∨ N.val = 32

theorem NOk.le32 {N : Usize} (h : NOk N) : N.val ≤ 32 := by unfold NOk at h; omega
theorem NOk.ge16 {N : Usize} (h : NOk N) : 16 ≤ N.val := by unfold NOk at h; omega

/-- The tweakable hash of §11.2 with SHA-256 (`F`, `PRF`, and for `n = 16`
also `H` and `T_l`). -/
def th256 (n : Nat) (pk : Spec.Bytes) (a : Spec.Adrs) (m : Spec.Bytes) : Spec.Bytes :=
  (Spec.sha256 (pk ++ Spec.toByte 0 (64 - n) ++ a.compress ++ m)).take n

/-- The tweakable hash of §11.2.2 with SHA-512 (`H` and `T_l` for `n > 16`). -/
def th512 (n : Nat) (pk : Spec.Bytes) (a : Spec.Adrs) (m : Spec.Bytes) : Spec.Bytes :=
  (Spec.sha512 (pk ++ Spec.toByte 0 (128 - n) ++ a.compress ++ m)).take n

theorem F_eq (P : Spec.Params) (pk : Spec.Bytes) (a : Spec.Adrs) (m : Spec.Bytes) :
    Spec.F P pk a m = th256 P.n pk a m := rfl
theorem PRF_eq (P : Spec.Params) (pk sk : Spec.Bytes) (a : Spec.Adrs) :
    Spec.PRF P pk sk a = th256 P.n pk a sk := rfl
theorem H_eq (P : Spec.Params) (pk : Spec.Bytes) (a : Spec.Adrs) (m : Spec.Bytes) :
    Spec.H P pk a m = if P.n = 16 then th256 P.n pk a m else th512 P.n pk a m := rfl
theorem T_eq_H (P : Spec.Params) (pk : Spec.Bytes) (a : Spec.Adrs) (m : Spec.Bytes) :
    Spec.T P pk a m = Spec.H P pk a m := rfl

/-- A `Seed` is consistent: its SHA-256 state is the compression of the first
block `PK.seed ‖ toByte(0, 64 − n)` of every SHA-256 tweakable hash, and for
`n > 16` its SHA-512 state is that of `PK.seed ‖ toByte(0, 128 − n)`. -/
def SeedOk {N : Usize} (s : hash.Seed N) : Prop :=
  wv s.state.val = Spec.SHA256.compress Spec.SHA256.H0
    (bytes s.pk_seed.val ++ List.replicate (64 - N.val) 0#8) ∧
  (N.val ≠ 16 → S512.wv s.state512.val = Spec.SHA512.compress Spec.SHA512.H0
    (bytes s.pk_seed.val ++ List.replicate (128 - N.val) 0#8))

theorem setSlice_rep {α} (l : List α) (k : Nat) (x : α) (h : l.length ≤ k) :
    (List.replicate k x).setSlice! 0 l = l ++ List.replicate (k - l.length) x := by
  have hm : min l.length k = l.length := by omega
  simp [List.setSlice!, hm, List.drop_replicate]

theorem bytes_replicate (k : Nat) (x : U8) : bytes (List.replicate k x) = List.replicate k x.bv := by
  simp [bytes]

@[step]
theorem seed_ctx_spec {N : Usize} (hN : NOk N) (pk : Array U8 N) :
    hash.seed_ctx pk ⦃ r => r.pk_seed = pk ∧ SeedOk r ⦄ := by
  unfold hash.seed_ctx
  have hN32 := hN.le32
  have hpl : pk.val.length = N.val := by simp
  step*
  · refine ⟨?_, fun _ => ?_⟩
    · rw [state_post, s3_post, Array.val_to_slice, s_post2, s2_post, s1_post, Array.val_to_slice,
        H0_eq, Array.repeat_val, setSlice_rep _ _ _ (by simp; omega), hpl, List.drop_zero,
        List.take_of_length_le (by simp; omega)]
      simp [bytes_replicate]
    · rw [state5121_post, s7_post, Array.val_to_slice, s4_post2, s6_post, s5_post,
        Array.val_to_slice, S512.H0_eq, Array.repeat_val, setSlice_rep _ _ _ (by simp; omega), hpl,
        List.drop_zero, List.take_of_length_le (by simp; omega)]
      simp [bytes_replicate]
  · refine ⟨?_, fun h => ?_⟩
    · rw [state_post, s3_post, Array.val_to_slice, s_post2, s2_post, s1_post, Array.val_to_slice,
        H0_eq, Array.repeat_val, setSlice_rep _ _ _ (by simp; omega), hpl, List.drop_zero,
        List.take_of_length_le (by simp; omega)]
      simp [bytes_replicate]
    · exfalso; apply h; scalar_tac
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
theorem trunc_spec (N : Usize) (hN : N.val ≤ 32) (st : Array U32 8#usize) :
    hash.trunc N st ⦃ r => bytes r.val = (ser (wv st.val)).take N.val ⦄ := by
  unfold hash.trunc
  step*
  have hv : (Array.from_slice (Array.repeat N 0#u8) s1).val = s1.val :=
    Array.from_slice_val _ _ (by scalar_tac)
  rw [to_slice_mut_back_post, s2_post, hv, s1_post, ← d_post]
  simp [List.slice]

@[step]
theorem trunc512_spec (N : Usize) (hN : N.val ≤ 64) (st : Array U64 8#usize) :
    hash.trunc512 N st ⦃ r => bytes r.val = (S512.ser (S512.wv st.val)).take N.val ⦄ := by
  unfold hash.trunc512
  step*
  have hv : (Array.from_slice (Array.repeat N 0#u8) s1).val = s1.val :=
    Array.from_slice_val _ _ (by scalar_tac)
  rw [to_slice_mut_back_post, s2_post, hv, s1_post, ← d_post]
  simp [List.slice]

/-- The SHA-256 tweakable hash, continuing from the compressed first block. -/
theorem th256_eq (n : Nat) (pk : Spec.Bytes) (hpk : pk.length = n) (hn : n ≤ 64) (a : Spec.Adrs)
    (m : Spec.Bytes) :
    th256 n pk a m = (ser (hashFrom (Spec.SHA256.compress Spec.SHA256.H0
      (pk ++ List.replicate (64 - n) 0#8)) (padFrom 64 (a.compress ++ m)))).take n := by
  unfold th256
  rw [toByte_zero,
    show ∀ a b c d : Spec.Bytes, a ++ b ++ c ++ d = (a ++ b) ++ (c ++ d) from by intros; simp,
    sha256_prefix64 _ _ (by simp [hpk]; omega)]

/-- The SHA-512 tweakable hash, continuing from the compressed first block. -/
theorem th512_eq (n : Nat) (pk : Spec.Bytes) (hpk : pk.length = n) (hn : n ≤ 128) (a : Spec.Adrs)
    (m : Spec.Bytes) :
    th512 n pk a m = (S512.ser (S512.hashFrom (Spec.SHA512.compress Spec.SHA512.H0
      (pk ++ List.replicate (128 - n) 0#8)) (S512.padFrom 128 (a.compress ++ m)))).take n := by
  unfold th512
  rw [toByte_zero,
    show ∀ a b c d : Spec.Bytes, a ++ b ++ c ++ d = (a ++ b) ++ (c ++ d) from by intros; simp,
    S512.sha512_prefix128 _ _ (by simp [hpk]; omega)]

theorem adrs_compress_length (A : Spec.Adrs) : A.compress.length = 22 := by
  rw [compress_eq]; rfl

/-- One compression of the block of a short message, from the seed state, is the tweakable hash. -/
theorem th256_one (n : Nat) (pk : Spec.Bytes) (hpk : pk.length = n) (hn : n ≤ 64) (A : Spec.Adrs)
    (m : Spec.Bytes) (hm : m.length ≤ 33) :
    (ser (Spec.SHA256.compress (Spec.SHA256.compress Spec.SHA256.H0 (pk ++ List.replicate (64 - n) 0#8))
      (padFrom 64 (A.compress ++ m)))).take n = th256 n pk A m := by
  have hl : (padFrom 64 (A.compress ++ m)).length = 64 := by
    rw [padFrom_short _ _ (adrs_compress_length A) hm]; simp [adrs_compress_length]; omega
  rw [th256_eq n pk hpk hn, hashFrom_one _ _ hl]

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

/-- `F` and `PRF`: one SHA-256 block after the seed state. -/
@[step]
theorem thash_short_spec {N : Usize} (hN : NOk N) (seed : hash.Seed N) (hs : SeedOk seed)
    (a : address.Adrs) (m : Slice U8) (hm : m.length ≤ 33) :
    hash.thash_short seed a m ⦃ r =>
      bytes r.val = th256 N.val (bytes seed.pk_seed.val) (adrsS a) (bytes m.val) ⦄ := by
  unfold hash.thash_short
  have hN32 := hN.le32
  let* ⟨ blk, blk_post ⟩ ← short_block_spec
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ st, st_post ⟩ ← compress_spec
  let* ⟨ r, r_post ⟩ ← trunc_spec
  rw [s_post, Array.val_to_slice, List.drop_zero,
    List.take_of_length_le (show (bytes blk.val).length ≤ 64 by simp)] at st_post
  rw [r_post, st_post, hs.1, blk_post, th256_one _ _ (by simp) (by omega) _ _ (by simpa using hm)]

/-- Writing a piece into the zero part of a block. -/
theorem setSlice_app {α} (X s : List α) (k : Nat) (z : α) (i : Nat) (hi : i = X.length)
    (hs : s.length ≤ k) :
    (X ++ List.replicate k z).setSlice! i s = X ++ s ++ List.replicate (k - s.length) z := by
  subst hi
  have hm : min s.length (X.length + k - X.length) = s.length := by omega
  have hm2 : min s.length k = s.length := by omega
  simp [List.setSlice!, hm, hm2, List.drop_replicate, List.take_append]

/-- Three pieces written one after another into a zero block. -/
theorem build3 {α} (A L R : List α) (z : α) (K i j : Nat) (hi : i = A.length)
    (hj : j = A.length + L.length) (h : A.length + L.length + R.length ≤ K) :
    (((List.replicate K z).setSlice! 0 A).setSlice! i L).setSlice! j R =
      A ++ L ++ R ++ List.replicate (K - A.length - L.length - R.length) z := by
  subst hi hj
  rw [show List.replicate K z = [] ++ List.replicate K z by simp,
    setSlice_app [] A K z 0 rfl (by omega), List.nil_append,
    setSlice_app A L (K - A.length) z A.length rfl (by omega),
    setSlice_app (A ++ L) R (K - A.length - L.length) z (A.length + L.length) (by simp) (by omega)]

/-- The padding byte and the two length bytes at the end of a block. -/
theorem set3_tail {α} (X : List α) (k : Nat) (z u v w : α) (i j l : Nat) (hi : i = X.length)
    (hj : j = X.length + k + 1) (hl : l = X.length + k + 2) :
    (((X ++ List.replicate (k + 3) z).set i u).set j v).set l w =
      X ++ u :: (List.replicate k z ++ [v, w]) := by
  subst hi hj hl
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.length_set, List.length_append, List.length_replicate] at h1
    simp only [List.getElem_set, List.getElem_append, List.getElem_cons, List.getElem_replicate,
      List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    split_ifs <;> (try subst_vars) <;> first | rfl | omega | skip

theorem toByte16_small (x : Nat) (hx : x < 65536) :
    Spec.toByte x 16 = List.replicate 14 0#8 ++ [BitVec.ofNat 8 (x >>> 8), BitVec.ofNat 8 x] := by
  have z : ∀ k, 16 ≤ k → x >>> k = 0 := by
    intro k hk
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le hx (by
      calc 65536 = 2 ^ 16 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk))
  simp only [Spec.toByte, show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    from rfl, List.map_cons, List.map_nil]
  simp [z]

/-- One 128-byte block holding `ADRSc ‖ m` and the SHA-512 padding of the
whole message after a first block, when `|m| ≤ 89`. -/
theorem padFrom512_short (c m : Spec.Bytes) (hc : c.length = 22) (hm : m.length ≤ 89) :
    S512.padFrom 128 (c ++ m) = c ++ m ++ 0x80#8 :: (List.replicate (103 - m.length) 0#8 ++
      [BitVec.ofNat 8 ((8 * (150 + m.length)) >>> 8), BitVec.ofNat 8 (8 * (150 + m.length))]) := by
  have e1 : (239 - (c ++ m).length % 128) % 128 = 89 - m.length := by simp [hc]; omega
  have e2 : 8 * (128 + (c ++ m).length) = 8 * (150 + m.length) := by simp [hc]; omega
  rw [S512.padFrom, e1, e2, toByte16_small _ (by omega)]
  have : 103 - m.length = (89 - m.length) + 14 := by omega
  simp [this, List.replicate_add]

theorem padFrom_short' (c m : Spec.Bytes) (hc : c.length = 22) (hm : m.length ≤ 33) :
    padFrom 64 (c ++ m) = c ++ m ++ 0x80#8 :: (List.replicate (39 - m.length) 0#8 ++
      [BitVec.ofNat 8 ((8 * (86 + m.length)) >>> 8), BitVec.ofNat 8 (8 * (86 + m.length))]) := by
  rw [padFrom_short _ _ hc hm]
  have : 39 - m.length = (33 - m.length) + 6 := by omega
  simp [this, List.replicate_add]

theorem cast_u8_usize (x : Usize) : U8.bv (UScalar.cast .U8 x) = BitVec.ofNat 8 x.val := cast_u8_bv x

@[step]
theorem pair_block_spec (adrs : address.Adrs) (l r : Array U8 16#usize) :
    hash.pair_block adrs l r ⦃ b =>
      bytes b.val = padFrom 64 ((adrsS adrs).compress ++ (bytes l.val ++ bytes r.val)) ⦄ := by
  unfold hash.pair_block
  step*
  · rcases System.Platform.numBits_eq with h | h <;> simp [h]
  · have hb3 : (index_mut_back2 s8).val = a.val ++ l.val ++ r.val ++ List.replicate 10 0#u8 := by
      rw [s6_post2, s8_post, s7_post, Array.val_to_slice, s3_post2, s5_post, s4_post,
        Array.val_to_slice, s_post2, s2_post, s1_post, Array.val_to_slice, Array.repeat_val,
        build3 _ _ _ _ _ _ _ (by simp) (by simp [i_post]) (by simp)]
      simp
    have hfin : b.val = (a.val ++ l.val ++ r.val) ++ 128#u8 :: (List.replicate 7 0#u8 ++ [i6, i7]) := by
      rw [b_post, blk5_post, blk4_post]
      simp only [Array.set_val_eq]
      rw [hb3, show List.replicate 10 0#u8 = List.replicate (7 + 3) 0#u8 from rfl]
      exact set3_tail _ 7 0#u8 _ _ _ _ _ _ (by simp [i3_post, i1_post]) (by simp) (by simp)
    have hbits : bits.val = 8 * (86 + 32) := by rw [bits_post, i4_post, i1_post]
    have h6 : i6.bv = BitVec.ofNat 8 ((8 * (86 + 32)) >>> 8) := by
      rw [i6_post, cast_u8_usize, i5_post, hbits]
    have h7 : i7.bv = BitVec.ofNat 8 (8 * (86 + 32)) := by
      rw [i7_post, cast_u8_usize, hbits]
    rw [hfin, padFrom_short' _ _ (adrs_compress_length _) (by simp), ← a_post]
    simp [bytes, h6, h7]

theorem hashFrom512_one (st : List Spec.SHA512.Word) (P : Spec.Bytes) (hP : P.length = 128) :
    S512.hashFrom st P = Spec.SHA512.compress st P := by
  simp [S512.hashFrom, hP, Spec.SHA512.blockAt, List.take_of_length_le]

/-- One SHA-512 compression of the block of a message of at most 89 bytes,
from the SHA-512 seed state, is the SHA-512 tweakable hash. -/
theorem th512_one (n : Nat) (pk : Spec.Bytes) (hpk : pk.length = n) (hn : n ≤ 128) (A : Spec.Adrs)
    (m : Spec.Bytes) (hm : m.length ≤ 89) :
    (S512.ser (Spec.SHA512.compress (Spec.SHA512.compress Spec.SHA512.H0
      (pk ++ List.replicate (128 - n) 0#8)) (S512.padFrom 128 (A.compress ++ m)))).take n =
      th512 n pk A m := by
  have hl : (S512.padFrom 128 (A.compress ++ m)).length = 128 := by
    rw [padFrom512_short _ _ (adrs_compress_length A) hm]; simp [adrs_compress_length]; omega
  rw [th512_eq n pk hpk hn, hashFrom512_one _ _ hl]

/-- `H(PK.seed, ADRS, left ‖ right)`. -/
@[step]
theorem thash_pair_spec {N : Usize} (P : Spec.Params) (hPN : P.n = N.val) (hN : NOk N)
    (seed : hash.Seed N) (hs : SeedOk seed) (adrs : address.Adrs) (l r : Array U8 N) :
    hash.thash_pair seed adrs l r ⦃ v =>
      bytes v.val = Spec.H P (bytes seed.pk_seed.val) (adrsS adrs) (bytes l.val ++ bytes r.val) ⦄ := by
  unfold hash.thash_pair
  have hN32 := hN.le32
  split
  · rename_i h16
    subst h16
    let* ⟨ blk, blk_post ⟩ ← pair_block_spec
    let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
    let* ⟨ st, st_post ⟩ ← compress_spec
    let* ⟨ v, v_post ⟩ ← trunc_spec
    rw [s_post, Array.val_to_slice, List.drop_zero,
      List.take_of_length_le (show (bytes blk.val).length ≤ 64 by simp)] at st_post
    have hP16 : P.n = 16 := by simpa using hPN
    have := th256_one 16 (bytes seed.pk_seed.val) (by simp) (by omega) (adrsS adrs)
      (bytes l.val ++ bytes r.val) (by simp)
    rw [H_eq, if_pos hP16, v_post, st_post, hs.1, blk_post]
    simpa [hP16] using this
  · rename_i h16
    have hn16 : N.val ≠ 16 := fun h => h16 (by scalar_tac)
    step*
    all_goals try (rcases System.Platform.numBits_eq with h | h <;> simp [h]; done)
    all_goals try (simp only [Slice.length, s4_post, Array.val_to_slice] at s3_post1 ⊢; scalar_tac)
    all_goals try (simp only [Slice.length, s7_post, Array.val_to_slice] at s6_post1 ⊢; scalar_tac)
    have hl : l.val.length = N.val := by simp
    have hr : r.val.length = N.val := by simp
    have hb3 : (index_mut_back2 s8).val = a.val ++ l.val ++ r.val ++
        List.replicate (128 - 22 - N.val - N.val) 0#u8 := by
      rw [s6_post2, s8_post, s7_post, Array.val_to_slice, s3_post2, s5_post, s4_post,
        Array.val_to_slice, s_post2, s2_post, s1_post, Array.val_to_slice, Array.repeat_val,
        build3 _ _ _ _ _ _ _ (by simp) (by simp [i_post]) (by simp; omega)]
      simp [hl]
    have hfin : blk6.val = (a.val ++ l.val ++ r.val) ++ 128#u8 ::
        (List.replicate (103 - 2 * N.val) 0#u8 ++ [i6, i7]) := by
      rw [blk6_post, blk5_post, blk4_post]
      simp only [Array.set_val_eq]
      rw [hb3, show 128 - 22 - N.val - N.val = (103 - 2 * N.val) + 3 by omega]
      exact set3_tail _ _ 0#u8 _ _ _ _ _ _ (by simp [i3_post, i1_post, hl, hr]; omega)
        (by simp [hl, hr]; omega) (by simp [hl, hr]; omega)
    have hbits : bits.val = 8 * (150 + 2 * N.val) := by rw [bits_post, i4_post, i1_post]; ring
    have h6 : i6.bv = BitVec.ofNat 8 ((8 * (150 + 2 * N.val)) >>> 8) := by
      rw [i6_post, cast_u8_usize, i5_post, hbits]
    have h7 : i7.bv = BitVec.ofNat 8 (8 * (150 + 2 * N.val)) := by
      rw [i7_post, cast_u8_usize, hbits]
    have hblk : bytes blk6.val = S512.padFrom 128 ((adrsS adrs).compress ++ (bytes l.val ++ bytes r.val)) := by
      rw [hfin, padFrom512_short _ _ (adrs_compress_length _) (by simp; omega), ← a_post]
      simp [bytes, h6, h7, hl, hr, two_mul]
    rw [s9_post, Array.val_to_slice, List.drop_zero,
      List.take_of_length_le (show (bytes blk6.val).length ≤ 128 by simp)] at st_post
    have := th512_one N.val (bytes seed.pk_seed.val) (by simp) (by omega) (adrsS adrs)
      (bytes l.val ++ bytes r.val) (by simp; omega)
    rw [H_eq, if_neg (by omega), v_post, st_post, hs.2 hn16, hblk, hPN]
    exact this

/-- `T_l` on any message (in practice the `k` FORS roots). -/
@[step]
theorem thash_spec {N : Usize} (P : Spec.Params) (hPN : P.n = N.val) (hN : NOk N)
    (seed : hash.Seed N) (hs : SeedOk seed) (adrs : address.Adrs) (m : Slice U8)
    (hm : m.length ≤ 4096) :
    hash.thash seed adrs m ⦃ r =>
      bytes r.val = Spec.T P (bytes seed.pk_seed.val) (adrsS adrs) (bytes m.val) ⦄ := by
  unfold hash.thash
  have hN32 := hN.le32
  let* ⟨ a1, a1_post ⟩ ← adrs_compress_spec
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ buf, buf_post, buf_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ buf1, buf1_post, buf1_len ⟩ ← hash_extend_from_slice_u8_spec
  have hl : buf1.length = 22 + m.length := by
    simp [buf1_len, buf_len, s_post]
  have hbuf : bytes buf1.val = (adrsS adrs).compress ++ bytes m.val := by
    simp [buf1_post, buf_post, s_post, a1_post]
  split
  · rename_i h16
    have hn : N.val = 16 := by scalar_tac
    let* ⟨ d, d_post ⟩ ← sha256_from_spec
    · simp only [Room, vec_deref_length]; scalar_tac
    step*
    have hv : (Array.from_slice (Array.repeat N 0#u8) s3).val = s3.val :=
      Array.from_slice_val _ _ (by scalar_tac)
    simp only [to_slice_mut_back_post, s4_post, hv, s3_post, List.slice]
    rw [T_eq_H, H_eq, if_pos (by omega), hPN, th256_eq _ _ (by simp) (by omega), ← hs.1, ← hbuf]
    simp [d_post, vec_deref_val]
  · rename_i h16
    have hn : N.val ≠ 16 := fun h => h16 (by scalar_tac)
    let* ⟨ d, d_post ⟩ ← S512.sha512_from_spec
    step*
    have hv : (Array.from_slice (Array.repeat N 0#u8) s3).val = s3.val :=
      Array.from_slice_val _ _ (by scalar_tac)
    simp only [to_slice_mut_back_post, s4_post, hv, s3_post, List.slice]
    rw [T_eq_H, H_eq, if_neg (by omega), hPN, th512_eq _ _ (by simp) (by omega), ← hs.2 hn, ← hbuf]
    simp [d_post, vec_deref_val]

/-! Iterated single-block hashing in place: `chain_blocks` and its pure model. -/

/-- One step of `chain_blocks` on a block, on spec bytes: write `t` into the
last address word (bytes 18..22), then replace the value (bytes 22..22 + n)
by `Trunc_n` of the compression of the block from `st`. -/
def stepBlock (n : Nat) (st : List Spec.SHA256.Word) (B : Spec.Bytes) (t : Nat) : Spec.Bytes :=
  let B' := B.take 18 ++ Spec.toByte t 4 ++ B.drop 22
  B'.take 22 ++ (ser (Spec.SHA256.compress st B')).take n ++ B'.drop (22 + n)

/-- The steps `s`, …, `e − 1` of `chain_blocks` on one block (none if `e ≤ s`). -/
def runBlock (n : Nat) (st : List Spec.SHA256.Word) (B : Spec.Bytes) (s e : Nat) : Spec.Bytes :=
  (List.range (e - s)).foldl (fun B k => stepBlock n st B (s + k)) B

theorem sha_compress_length (st : List Spec.SHA256.Word) (B : Spec.Bytes) :
    (Spec.SHA256.compress st B).length = 8 := by
  simp [Spec.SHA256.compress]

theorem ser_length (l : List Spec.SHA256.Word) : (ser l).length = 4 * l.length := by
  simp [ser, Spec.toByte, List.length_flatMap]; omega

theorem toByte4_eq (t : Nat) : Spec.toByte t 4 =
    [BitVec.ofNat 8 (t >>> 24), BitVec.ofNat 8 (t >>> 16), BitVec.ofNat 8 (t >>> 8), BitVec.ofNat 8 t] := by
  simp [Spec.toByte, show List.range 4 = [0, 1, 2, 3] from rfl]

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

/-- One step on the block of an `n`-byte value. -/
theorem stepBlock_short (n : Nat) (hn : n ≤ 32) (st : List Spec.SHA256.Word) (A : Spec.Adrs)
    (m : Spec.Bytes) (hm : m.length = n) (t : Nat) :
    stepBlock n st (padFrom 64 (A.compress ++ m)) t =
      padFrom 64 ({ A with word3 := t }.compress ++
        (ser (Spec.SHA256.compress st (padFrom 64 ({ A with word3 := t }.compress ++ m)))).take n) := by
  unfold stepBlock
  simp only []
  rw [counter_set _ _ (by omega)]
  have hl : ((ser (Spec.SHA256.compress st (padFrom 64 ({ A with word3 := t }.compress ++ m)))).take n).length = n := by
    simp [ser_length, sha_compress_length]; omega
  have hc := adrs_compress_length { A with word3 := t }
  have e1 : (padFrom 64 ({ A with word3 := t }.compress ++ m)).take 22 = { A with word3 := t }.compress := by
    rw [padFrom_blk _ _ (by omega), List.take_left' hc]
  have e2 : (padFrom 64 ({ A with word3 := t }.compress ++ m)).drop (22 + n) = padTail n := by
    rw [padFrom_blk _ _ (by omega), ← List.append_assoc, List.drop_left' (by simp [hc, hm]), hm]
  rw [e1, e2]
  generalize List.take n (ser (Spec.SHA256.compress st
    (padFrom 64 ({ A with word3 := t }.compress ++ m)))) = H at hl ⊢
  rw [padFrom_blk _ H (by omega), hl]
  simp

/-- The value held in a block that has been stepped. -/
theorem stepBlock_value (n : Nat) (st : List Spec.SHA256.Word) (B : Spec.Bytes) (hB : B.length = 64)
    (hn : n ≤ 32) (t : Nat) :
    ((stepBlock n st B t).drop 22).take n =
      (ser (Spec.SHA256.compress st (B.take 18 ++ Spec.toByte t 4 ++ B.drop 22))).take n := by
  unfold stepBlock
  simp only []
  have hl : ((ser (Spec.SHA256.compress st (B.take 18 ++ Spec.toByte t 4 ++ B.drop 22))).take n).length = n := by
    simp [ser_length, sha_compress_length]; omega
  have h22 : ((B.take 18 ++ Spec.toByte t 4 ++ B.drop 22).take 22).length = 22 := by
    simp [Spec.toByte]; omega
  rw [List.append_assoc, List.drop_left' h22, List.take_left' hl]

theorem block_value (n : Nat) (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length ≤ 33) :
    ((padFrom 64 (A.compress ++ m)).drop 22).take n = (m ++ padTail m.length).take n := by
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

theorem th256_length (n : Nat) (hn : n ≤ 32) (pk : Spec.Bytes) (hpk : pk.length = n) (A : Spec.Adrs)
    (m : Spec.Bytes) : (th256 n pk A m).length = n := by
  rw [th256_eq n pk hpk (by omega)]
  simp [ser_length, hashFrom_length _ (sha_compress_length _ _)]; omega

theorem chain_succ (P : Spec.Params) (x : Spec.Bytes) (s n : Nat) (pk : Spec.Bytes) (A : Spec.Adrs) :
    Spec.chain P x s (n + 1) pk A = Spec.F P pk { A with word3 := s + n } (Spec.chain P x s n pk A) := by
  simp only [Spec.chain, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem chain_length (P : Spec.Params) (hn : P.n ≤ 32) (pk : Spec.Bytes) (hpk : pk.length = P.n)
    (x : Spec.Bytes) (hx : x.length = P.n) (s k : Nat) (A : Spec.Adrs) :
    (Spec.chain P x s k pk A).length = P.n := by
  cases k with
  | zero => simpa [Spec.chain] using hx
  | succ k => rw [chain_succ, F_eq]; exact th256_length _ hn pk hpk _ _

theorem runBlock_succ (n : Nat) (st : List Spec.SHA256.Word) (B : Spec.Bytes) (s k : Nat) :
    runBlock n st B s (s + (k + 1)) = stepBlock n st (runBlock n st B s (s + k)) (s + k) := by
  simp [runBlock, List.range_succ, List.foldl_append]

theorem runBlock_le (n : Nat) (st : List Spec.SHA256.Word) (B : Spec.Bytes) (s e : Nat) (h : e ≤ s) :
    runBlock n st B s e = B := by
  simp [runBlock, Nat.sub_eq_zero_of_le h]

theorem runBlock_one (n : Nat) (st : List Spec.SHA256.Word) (B : Spec.Bytes) (s : Nat) :
    runBlock n st B s (s + 1) = stepBlock n st B s := by
  simp [runBlock]

/-- `B` is the block holding the value `v` at an address that is `A` up to its last word. -/
def ValBlk (A : Spec.Adrs) (v B : Spec.Bytes) : Prop :=
  ∃ w, B = padFrom 64 ({ A with word3 := w }.compress ++ v)

/-- The seed state of the SHA-256 tweakable hashes for `PK.seed`. -/
def seedState (n : Nat) (pk : Spec.Bytes) : List Spec.SHA256.Word :=
  Spec.SHA256.compress Spec.SHA256.H0 (pk ++ List.replicate (64 - n) 0#8)

/-- One step with the seed state is `F` (or `PRF`) at the address of the step. -/
theorem stepBlock_thash (P : Spec.Params) (hn : P.n ≤ 32) (pk : Spec.Bytes) (hpk : pk.length = P.n)
    (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length = P.n) (t : Nat) :
    stepBlock P.n (seedState P.n pk) (padFrom 64 (A.compress ++ m)) t =
      padFrom 64 ({ A with word3 := t }.compress ++ Spec.F P pk { A with word3 := t } m) := by
  rw [stepBlock_short _ hn _ _ _ hm, seedState, th256_one _ pk hpk (by omega) _ _ (by omega), F_eq]

/-- A run of steps with the seed state is `chain`. -/
theorem runBlock_chain (P : Spec.Params) (hn : P.n ≤ 32) (pk : Spec.Bytes) (hpk : pk.length = P.n)
    (A : Spec.Adrs) (m B : Spec.Bytes) (hm : m.length = P.n) (hB : ValBlk A m B) (s k : Nat) :
    ValBlk A (Spec.chain P m s k pk A) (runBlock P.n (seedState P.n pk) B s (s + k)) := by
  induction k with
  | zero => simpa [runBlock, Spec.chain] using hB
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    rw [runBlock_succ, hw, stepBlock_thash P hn pk hpk _ _ (chain_length P hn pk hpk m hm s k A),
      chain_succ]
    exact ⟨s + k, rfl⟩

theorem ValBlk_value (n : Nat) (A : Spec.Adrs) (v B : Spec.Bytes) (hv : v.length = n) (hn : n ≤ 33)
    (hB : ValBlk A v B) : (B.drop 22).take n = v := by
  obtain ⟨w, rfl⟩ := hB
  rw [block_value _ _ _ (by omega), List.take_left' hv]

/-- The value of a block after its one step, numbered by its own last address
word: the SHA-256 tweakable hash of the block's message. -/
theorem stepBlock_pair_value (n : Nat) (hn : n ≤ 32) (pk : Spec.Bytes) (hpk : pk.length = n)
    (A : Spec.Adrs) (m : Spec.Bytes) (hm : m.length ≤ 33) :
    ((stepBlock n (seedState n pk) (padFrom 64 (A.compress ++ m)) A.word3).drop 22).take n =
      th256 n pk A m := by
  rw [stepBlock_value _ _ _ (padFrom_blk_length _ _ hm) hn, counter_self _ _ hm, seedState,
    th256_one n pk hpk (by omega) _ _ hm]

@[step]
theorem value_spec (N : Usize) (hN : N.val ≤ 32) (block : Array U8 64#usize) :
    hash.value N block ⦃ r => bytes r.val = ((bytes block.val).drop 22).take N.val ⦄ := by
  unfold hash.value
  step*
  · simp only [Slice.length, s_post, Array.repeat_val, List.length_replicate]; scalar_tac
  · have hv : (Array.from_slice (Array.repeat N 0#u8) s1).val = s1.val :=
      Array.from_slice_val _ _ (by scalar_tac)
    rw [to_slice_mut_back_post, s2_post, hv, s1_post]
    simp [List.slice, bytes, i_post]

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
theorem chain_blocks_inner_spec (N : Usize) (hN : N.val ≤ 32) (state : Array U32 8#usize) (blocks0 : Slice (Array U8 64#usize))
    («end» : Slice U32) (i : Usize) (s0 : Nat)
    (hi : i.val < blocks0.length) (he : i.val < «end».length)
    (blocks : Slice (Array U8 64#usize)) (t : U32)
    (hlen : blocks.length = blocks0.length)
    (hother : ∀ j, j ≠ i.val → blocks.val[j]! = blocks0.val[j]!)
    (hst : s0 ≤ t.val) (hte : t.val ≤ («end».val[i.val]!).val ∨ t.val = s0)
    (hcur : bytes (blocks.val[i.val]!).val =
      runBlock N.val (wv state.val) (bytes (blocks0.val[i.val]!).val) s0 t.val) :
    hash.chain_blocks_portable_loop0_loop0 N state blocks «end» i t ⦃ r =>
      r.length = blocks0.length ∧ (∀ j, j ≠ i.val → r.val[j]! = blocks0.val[j]!) ∧
      bytes (r.val[i.val]!).val =
        runBlock N.val (wv state.val) (bytes (blocks0.val[i.val]!).val) s0 («end».val[i.val]!).val ⦄ := by
  unfold hash.chain_blocks_portable_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Slice (Array U8 64#usize) × U32) => («end».val[i.val]!).val - p.2.val)
    (inv := fun p => p.1.length = blocks0.length ∧ (∀ j, j ≠ i.val → p.1.val[j]! = blocks0.val[j]!) ∧
      s0 ≤ p.2.val ∧ (p.2.val ≤ («end».val[i.val]!).val ∨ p.2.val = s0) ∧
      bytes (p.1.val[i.val]!).val =
        runBlock N.val (wv state.val) (bytes (blocks0.val[i.val]!).val) s0 p.2.val)
  · rintro ⟨blocks, t⟩ ⟨h1, h2, h3, h4, h5⟩
    simp only [hash.chain_blocks_portable_loop0_loop0.body]
    simp only at h1 h2 h3 h4 h5
    step*
    all_goals try (simp [*]; done)
    all_goals try (simp only [Slice.length, s2_post, Array.val_to_slice] at s1_post1 ⊢; scalar_tac)
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
      have hfin : bytes (index_mut_back5 s3).val = stepBlock N.val (wv state.val) (bytes (blocks.val[i.val]).val) t.val := by
        rw [s1_post2, s3_post, s2_post, e9, Array.val_to_slice]
        unfold stepBlock
        simp only []
        rw [← h7]
        rw [bytes_setSlice _ _ _ (by simp; omega), d_post, hst']
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
      · rw [h4, runBlock_le _ _ _ _ _ (by omega), runBlock_le _ _ _ _ _ (by omega)]
  · exact ⟨hlen, hother, hst, hte, hcur⟩

theorem chain_blocks_loop0_spec (N : Usize) (hN : N.val ≤ 32) (state : Array U32 8#usize) (blocks0 : Slice (Array U8 64#usize))
    (start «end» : Slice U32)
    (hs : blocks0.length ≤ start.length) (he : blocks0.length ≤ «end».length)
    (blocks : Slice (Array U8 64#usize)) (i : Usize)
    (hi : i.val ≤ blocks0.length) (hlen : blocks.length = blocks0.length)
    (hdone : ∀ j, j < i.val → bytes (blocks.val[j]!).val =
      runBlock N.val (wv state.val) (bytes (blocks0.val[j]!).val) (start.val[j]!).val («end».val[j]!).val)
    (hrest : ∀ j, i.val ≤ j → blocks.val[j]! = blocks0.val[j]!) :
    hash.chain_blocks_portable_loop0 N state blocks start «end» i ⦃ r =>
      r.length = blocks0.length ∧ ∀ j, j < blocks0.length → bytes (r.val[j]!).val =
        runBlock N.val (wv state.val) (bytes (blocks0.val[j]!).val) (start.val[j]!).val («end».val[j]!).val ⦄ := by
  unfold hash.chain_blocks_portable_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Slice (Array U8 64#usize) × Usize) => blocks0.length - p.2.val)
    (inv := fun p => p.2.val ≤ blocks0.length ∧ p.1.length = blocks0.length ∧
      (∀ j, j < p.2.val → bytes (p.1.val[j]!).val =
        runBlock N.val (wv state.val) (bytes (blocks0.val[j]!).val) (start.val[j]!).val («end».val[j]!).val) ∧
      (∀ j, p.2.val ≤ j → p.1.val[j]! = blocks0.val[j]!))
  · rintro ⟨blocks, i⟩ ⟨h1, h2, h3, h4⟩
    simp only [hash.chain_blocks_portable_loop0.body]
    simp only at h1 h2 h3 h4
    simp only [step_simps]
    spec_split
    · let* ⟨ t, t_post ⟩ ← Slice.index_usize_spec
      have hib : i.val < blocks0.length := by scalar_tac
      let* ⟨ b1, b1_len, b1_other, b1_cur ⟩ ← chain_blocks_inner_spec N hN state blocks «end» i t.val
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
theorem chain_blocks_portable_spec (N : Usize) (hN : N.val ≤ 32) (state : Array U32 8#usize) (blocks : Slice (Array U8 64#usize))
    (start «end» : Slice U32)
    (hs : blocks.length ≤ start.length) (he : blocks.length ≤ «end».length) :
    hash.chain_blocks_portable N state blocks start «end» ⦃ r =>
      r.length = blocks.length ∧ ∀ i, i < blocks.length → bytes (r.val[i]!).val =
        runBlock N.val (wv state.val) (bytes (blocks.val[i]!).val) (start.val[i]!).val («end».val[i]!).val ⦄ := by
  unfold hash.chain_blocks_portable
  exact chain_blocks_loop0_spec N hN state blocks start «end» hs he blocks 0#usize (by simp) rfl
    (fun j hj => by simp at hj) (fun _ _ => rfl)

/-! `T_len` on the values held in the chain blocks (`thash_values`). -/

/-- The `n`-byte value held in a 64-byte block (bytes 22..22 + n). -/
def blkVal (n : Nat) (b : Array U8 64#usize) : Spec.Bytes := ((bytes b.val).drop 22).take n

theorem blkVal_length (n : Nat) (hn : n ≤ 42) (b : Array U8 64#usize) : (blkVal n b).length = n := by
  simp [blkVal]; omega

theorem flatMap_blkVal_length (n : Nat) (hn : n ≤ 42) (blocks : List (Array U8 64#usize)) (i : Nat) :
    ((List.range i).flatMap fun (j : Nat) => blkVal n blocks[j]!).length = n * i := by
  induction i with
  | zero => simp
  | succ i ih => rw [List.range_succ, List.flatMap_append]; simp [blkVal_length n hn]; ring

theorem foldl_range_congr {β} (f g : β → Nat → β) (k : Nat) (b : β)
    (h : ∀ j b, j < k → f b j = g b j) :
    (List.range k).foldl f b = (List.range k).foldl g b := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih _ (fun j b hj => h j b (by omega))]
    simp [h k _ (by omega)]

/-- The buffer of `thash_values` with SHA-256: `ADRSc ‖ M`, zeros, and the
padding written at the right places; its first `total` bytes are the padded message. -/
theorem padbuf64 (X : Spec.Bytes) (B total : Nat) (htot : total = (X.length + 9 + 63) / 64 * 64)
    (hB : total ≤ B) (hbits : 8 * (64 + X.length) < 65536) :
    ((((X ++ List.replicate (B - X.length) 0#8).set X.length 0x80#8).set (total - 2)
      (BitVec.ofNat 8 ((8 * (64 + X.length)) >>> 8))).set (total - 1)
      (BitVec.ofNat 8 (8 * (64 + X.length)))).take total = padFrom 64 X := by
  have hk : B - X.length = (total - X.length - 3 + 3) + (B - total) := by omega
  rw [hk, List.replicate_add, ← List.append_assoc, List.set_append_left _ _ (by simp only [List.length_append, List.length_replicate, List.length_set]; omega),
    List.set_append_left _ _ (by simp only [List.length_append, List.length_replicate, List.length_set]; omega),
    List.set_append_left _ _ (by simp only [List.length_append, List.length_replicate, List.length_set]; omega),
    set3_tail _ _ _ _ _ _ _ _ _ rfl (by omega) (by omega),
    List.take_left' (by simp; omega)]
  rw [padFrom, toByte8_small _ hbits]
  have hz : total - X.length - 3 = (119 - X.length % 64) % 64 + 6 := by omega
  rw [hz]
  simp [List.replicate_add]

/-- The same with SHA-512. -/
theorem padbuf128 (X : Spec.Bytes) (B total : Nat) (htot : total = (X.length + 17 + 127) / 128 * 128)
    (hB : total ≤ B) (hbits : 8 * (128 + X.length) < 65536) :
    ((((X ++ List.replicate (B - X.length) 0#8).set X.length 0x80#8).set (total - 2)
      (BitVec.ofNat 8 ((8 * (128 + X.length)) >>> 8))).set (total - 1)
      (BitVec.ofNat 8 (8 * (128 + X.length)))).take total = S512.padFrom 128 X := by
  have hk : B - X.length = (total - X.length - 3 + 3) + (B - total) := by omega
  rw [hk, List.replicate_add, ← List.append_assoc, List.set_append_left _ _ (by simp only [List.length_append, List.length_replicate, List.length_set]; omega),
    List.set_append_left _ _ (by simp only [List.length_append, List.length_replicate, List.length_set]; omega),
    List.set_append_left _ _ (by simp only [List.length_append, List.length_replicate, List.length_set]; omega),
    set3_tail _ _ _ _ _ _ _ _ _ rfl (by omega) (by omega),
    List.take_left' (by simp; omega)]
  rw [S512.padFrom, toByte16_small _ hbits]
  have hz : total - X.length - 3 = (239 - X.length % 128) % 128 + 14 := by omega
  rw [hz]
  simp [List.replicate_add]

theorem thash_values_loop0_spec (N : Usize) (hN : NOk N) (blocks : Slice (Array U8 64#usize))
    (hb : N.val * blocks.length ≤ 618)
    (C : Spec.Bytes) (hC : C.length = 22) (buf : Array U8 640#usize) (i : Usize)
    (hi : i.val ≤ blocks.length)
    (hinv : bytes buf.val = C ++ (List.range i.val).flatMap (fun (j : Nat) => blkVal N.val blocks.val[j]!) ++
      List.replicate (618 - N.val * i.val) 0#8) :
    hash.thash_values_loop0 N blocks buf i ⦃ r =>
      bytes r.val = C ++ (List.range blocks.length).flatMap (fun (j : Nat) => blkVal N.val blocks.val[j]!) ++
        List.replicate (618 - N.val * blocks.length) 0#8 ⦄ := by
  have hN32 := hN.le32
  unfold hash.thash_values_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Array U8 640#usize × Usize) => blocks.length - p.2.val)
    (inv := fun p => p.2.val ≤ blocks.length ∧ bytes p.1.val = C ++
      (List.range p.2.val).flatMap (fun (j : Nat) => blkVal N.val blocks.val[j]!) ++
      List.replicate (618 - N.val * p.2.val) 0#8)
  · rintro ⟨buf, i⟩ ⟨h1, h2⟩
    simp only [hash.thash_values_loop0.body]
    simp only at h1 h2
    split
    · rename_i hlt
      have hil : i.val < blocks.length := by scalar_tac
      have hmul : N.val * i.val + N.val ≤ 618 := by
        have := le_trans (Nat.mul_le_mul_left N.val (show i.val + 1 ≤ blocks.length by omega)) hb
        rw [Nat.mul_succ] at this; exact this
      step*
      all_goals try (simp only [Slice.length] at *; scalar_tac)
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have hF := flatMap_blkVal_length N.val (by omega) blocks.val i.val
      have hlen : (C ++ (List.range i.val).flatMap (fun (j : Nat) => blkVal N.val blocks.val[j]!)).length =
          i3.val := by simp only [List.length_append, hC, hF, i3_post, i2_post]
      have hs1 : bytes s1.val = blkVal N.val blocks.val[i.val]! := by
        rw [s1_post, a_post, getElem!_eq _ _ (by scalar_tac)]
        simp [blkVal, List.slice, i6_post]
      have hs1len : s1.val.length = N.val := by scalar_tac
      have hbl : buf.val.length = 640 := by simp
      have hsl : i3.val + s1.val.length ≤ buf.val.length := by
        rw [hs1len, hbl, i3_post, i2_post]; omega
      rw [s_post2, s2_post, bytes_setSlice _ _ _ hsl, h2, hs1len, hs1,
        List.take_left' hlen, ← List.drop_drop, List.drop_left' hlen, i7_post,
        List.range_succ, List.flatMap_append, List.drop_replicate]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      congr 3
      rw [Nat.mul_add, Nat.mul_one, Nat.sub_sub]
    · rename_i hge
      have he : i.val = blocks.length := by scalar_tac
      simp only [step_simps]
      rw [he] at h2; exact h2
  · exact ⟨hi, hinv⟩

theorem thash_values_loop2_spec (N : Usize) (hN : NOk N) (blocks : Slice (Array U8 64#usize))
    (hb : N.val * blocks.length ≤ 2282)
    (C : Spec.Bytes) (hC : C.length = 22) (buf : Array U8 2304#usize) (i : Usize)
    (hi : i.val ≤ blocks.length)
    (hinv : bytes buf.val = C ++ (List.range i.val).flatMap (fun (j : Nat) => blkVal N.val blocks.val[j]!) ++
      List.replicate (2282 - N.val * i.val) 0#8) :
    hash.thash_values_loop2 N blocks buf i ⦃ r =>
      bytes r.val = C ++ (List.range blocks.length).flatMap (fun (j : Nat) => blkVal N.val blocks.val[j]!) ++
        List.replicate (2282 - N.val * blocks.length) 0#8 ⦄ := by
  have hN32 := hN.le32
  unfold hash.thash_values_loop2
  apply loop.spec_decr_nat
    (measure := fun (p : Array U8 2304#usize × Usize) => blocks.length - p.2.val)
    (inv := fun p => p.2.val ≤ blocks.length ∧ bytes p.1.val = C ++
      (List.range p.2.val).flatMap (fun (j : Nat) => blkVal N.val blocks.val[j]!) ++
      List.replicate (2282 - N.val * p.2.val) 0#8)
  · rintro ⟨buf, i⟩ ⟨h1, h2⟩
    simp only [hash.thash_values_loop2.body]
    simp only at h1 h2
    split
    · rename_i hlt
      have hil : i.val < blocks.length := by scalar_tac
      have hmul : N.val * i.val + N.val ≤ 2282 := by
        have := le_trans (Nat.mul_le_mul_left N.val (show i.val + 1 ≤ blocks.length by omega)) hb
        rw [Nat.mul_succ] at this; exact this
      step*
      all_goals try (simp only [Slice.length] at *; scalar_tac)
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have hF := flatMap_blkVal_length N.val (by omega) blocks.val i.val
      have hlen : (C ++ (List.range i.val).flatMap (fun (j : Nat) => blkVal N.val blocks.val[j]!)).length =
          i3.val := by simp only [List.length_append, hC, hF, i3_post, i2_post]
      have hs1 : bytes s1.val = blkVal N.val blocks.val[i.val]! := by
        rw [s1_post, a_post, getElem!_eq _ _ (by scalar_tac)]
        simp [blkVal, List.slice, i6_post]
      have hs1len : s1.val.length = N.val := by scalar_tac
      have hbl : buf.val.length = 2304 := by simp
      have hsl : i3.val + s1.val.length ≤ buf.val.length := by
        rw [hs1len, hbl, i3_post, i2_post]; omega
      rw [s_post2, s2_post, bytes_setSlice _ _ _ hsl, h2, hs1len, hs1,
        List.take_left' hlen, ← List.drop_drop, List.drop_left' hlen, i7_post,
        List.range_succ, List.flatMap_append, List.drop_replicate]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      congr 3
      rw [Nat.mul_add, Nat.mul_one, Nat.sub_sub]
    · rename_i hge
      have he : i.val = blocks.length := by scalar_tac
      simp only [step_simps]
      rw [he] at h2; exact h2
  · exact ⟨hi, hinv⟩

theorem hashFrom_take (S0 : List Spec.SHA256.Word) (P : Spec.Bytes) (t : Nat) (ht : t % 64 = 0)
    (hle : t ≤ P.length) :
    hashFrom S0 (P.take t) = (List.range (t / 64)).foldl
      (fun st k => Spec.SHA256.compress st (Spec.SHA256.blockAt P k)) S0 := by
  unfold hashFrom
  rw [List.length_take, Nat.min_eq_left hle]
  apply foldl_range_congr
  intro j b hj
  congr 1
  simp only [Spec.SHA256.blockAt, List.drop_take]
  rw [List.take_take, Nat.min_eq_left (by omega)]

theorem hashFrom512_take (S0 : List Spec.SHA512.Word) (P : Spec.Bytes) (t : Nat) (ht : t % 128 = 0)
    (hle : t ≤ P.length) :
    S512.hashFrom S0 (P.take t) = (List.range (t / 128)).foldl
      (fun st k => Spec.SHA512.compress st (Spec.SHA512.blockAt P k)) S0 := by
  unfold S512.hashFrom
  rw [List.length_take, Nat.min_eq_left hle]
  apply foldl_range_congr
  intro j b hj
  congr 1
  simp only [Spec.SHA512.blockAt, List.drop_take]
  rw [List.take_take, Nat.min_eq_left (by omega)]

theorem thash_values_loop1_spec (buf : Array U8 640#usize) (total : Usize) (S0 : List Spec.SHA256.Word)
    (st : Array U32 8#usize) (off : Usize) (ht : total.val % 64 = 0) (htle : total.val ≤ 640)
    (hoff : off.val % 64 = 0) (hle : off.val ≤ total.val)
    (hinv : wv st.val = (List.range (off.val / 64)).foldl
      (fun st k => Spec.SHA256.compress st (Spec.SHA256.blockAt (bytes buf.val) k)) S0) :
    hash.thash_values_loop1 buf total st off ⦃ r =>
      wv r.val = hashFrom S0 ((bytes buf.val).take total.val) ⦄ := by
  unfold hash.thash_values_loop1
  apply loop.spec_decr_nat
    (measure := fun (q : Array U32 8#usize × Usize) => total.val - q.2.val)
    (inv := fun q => q.2.val % 64 = 0 ∧ q.2.val ≤ total.val ∧
      wv q.1.val = (List.range (q.2.val / 64)).foldl
        (fun st k => Spec.SHA256.compress st (Spec.SHA256.blockAt (bytes buf.val) k)) S0)
  · rintro ⟨st, off⟩ ⟨hoff, hle, hinv⟩
    simp only [hash.thash_values_loop1.body]
    simp only at hoff hle hinv
    split
    · rename_i hlt
      have h64 : off.val + 64 ≤ total.val := by scalar_tac
      step*
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have e : off1.val / 64 = off.val / 64 + 1 := by scalar_tac
      have e2 : 64 * (off.val / 64) = off.val := by omega
      rw [e, List.range_succ, List.foldl_append, ← hinv, st1_post, s_post]
      simp [Spec.SHA256.blockAt, e2]
    · rename_i hge
      have : off.val = total.val := by scalar_tac
      simp only [step_simps]
      rw [this] at hinv
      rw [hinv, hashFrom_take _ _ _ ht (by simp; omega)]
  · exact ⟨hoff, hle, hinv⟩

theorem thash_values_loop3_spec (buf : Array U8 2304#usize) (total : Usize) (S0 : List Spec.SHA512.Word)
    (st : Array U64 8#usize) (off : Usize) (ht : total.val % 128 = 0) (htle : total.val ≤ 2304)
    (hoff : off.val % 128 = 0) (hle : off.val ≤ total.val)
    (hinv : S512.wv st.val = (List.range (off.val / 128)).foldl
      (fun st k => Spec.SHA512.compress st (Spec.SHA512.blockAt (bytes buf.val) k)) S0) :
    hash.thash_values_loop3 buf total st off ⦃ r =>
      S512.wv r.val = S512.hashFrom S0 ((bytes buf.val).take total.val) ⦄ := by
  unfold hash.thash_values_loop3
  apply loop.spec_decr_nat
    (measure := fun (q : Array U64 8#usize × Usize) => total.val - q.2.val)
    (inv := fun q => q.2.val % 128 = 0 ∧ q.2.val ≤ total.val ∧
      S512.wv q.1.val = (List.range (q.2.val / 128)).foldl
        (fun st k => Spec.SHA512.compress st (Spec.SHA512.blockAt (bytes buf.val) k)) S0)
  · rintro ⟨st, off⟩ ⟨hoff, hle, hinv⟩
    simp only [hash.thash_values_loop3.body]
    simp only at hoff hle hinv
    split
    · rename_i hlt
      have h128 : off.val + 128 ≤ total.val := by scalar_tac
      step*
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have e : off1.val / 128 = off.val / 128 + 1 := by scalar_tac
      have e2 : 128 * (off.val / 128) = off.val := by omega
      rw [e, List.range_succ, List.foldl_append, ← hinv, st1_post, s_post]
      simp [Spec.SHA512.blockAt, e2]
    · rename_i hge
      have : off.val = total.val := by scalar_tac
      simp only [step_simps]
      rw [this] at hinv
      rw [hinv, hashFrom512_take _ _ _ ht (by simp; omega)]
  · exact ⟨hoff, hle, hinv⟩

theorem len_cases {N : Usize} (hN : NOk N) :
    (N.val = 16 ∧ N.val * (2 * N.val + 3) = 560) ∨ (N.val = 24 ∧ N.val * (2 * N.val + 3) = 1224) ∨
    (N.val = 32 ∧ N.val * (2 * N.val + 3) = 2144) := by
  rcases hN with h | h | h <;> simp [h]

/-- `T_len` of the values held in the `len` chain blocks. -/
@[step]
theorem thash_values_spec {N : Usize} (P : Spec.Params) (hPN : P.n = N.val) (hN : NOk N)
    (seed : hash.Seed N) (hs : SeedOk seed) (adrs : address.Adrs)
    (blocks : Slice (Array U8 64#usize)) (hb : blocks.length = 2 * N.val + 3) :
    hash.thash_values seed adrs blocks ⦃ r =>
      bytes r.val = Spec.T P (bytes seed.pk_seed.val) (adrsS adrs)
        ((List.range blocks.length).flatMap fun (j : Nat) => blkVal N.val blocks.val[j]!) ⦄ := by
  unfold hash.thash_values
  have hN32 := hN.le32
  have hL := len_cases hN
  have hM := flatMap_blkVal_length N.val (by omega) blocks.val blocks.length
  have hbl : blocks.len.val = 2 * N.val + 3 := by simp [hb]
  let* ⟨ i1, i1_post ⟩ ← Usize.mul_spec
  · rw [hbl]; rcases hL with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> scalar_tac
  let* ⟨ mlen, mlen_post ⟩ ← Usize.add_spec
  · rw [i1_post, hbl]; rcases hL with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> scalar_tac
  have hmlen : mlen.val = 22 + N.val * blocks.length := by rw [mlen_post, i1_post, hbl, hb]
  split
  · rename_i h16
    have hn : N.val = 16 := by scalar_tac
    have hml : mlen.val = 582 := by rw [hmlen, hb, hn]
    step*
    have hb1 : bytes (index_mut_back s2).val = (adrsS adrs).compress ++ List.replicate 618 0#8 := by
      rw [s_post2, s2_post, s1_post, Array.val_to_slice, Array.repeat_val,
        setSlice_rep _ _ _ (by simp), bytes_append, a_post, bytes_replicate,
        show (640#usize).val - a.val.length = 618 by simp]
      rfl
    let* ⟨ buf2, buf2_post ⟩ ← thash_values_loop0_spec N hN blocks (by rw [hb, hn]; omega) (adrsS adrs).compress
      (adrs_compress_length _) (index_mut_back s2) 0#usize (by simp)
      (by rw [hb1, show (0#usize).val = 0 from rfl]
          simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero, Nat.sub_zero])
    step*
    · rcases System.Platform.numBits_eq with h | h <;> simp [h]
    · have htot : total.val = 640 := by
        rw [total_post, i4_post, i3_post, i2_post, hml]
      have hbits : bits.val = 8 * (64 + 582) := by rw [bits_post, i5_post, hml]
      have hP : (bytes a1.val).take total.val =
          padFrom 64 ((adrsS adrs).compress ++
            (List.range blocks.length).flatMap fun (j : Nat) => blkVal N.val blocks.val[j]!) := by
        have hX : ((adrsS adrs).compress ++
            (List.range blocks.length).flatMap fun (j : Nat) => blkVal N.val blocks.val[j]!).length = 582 := by
          rw [List.length_append, adrs_compress_length, hM, hb, hn]
        rw [← padbuf64 _ 640 total.val (by rw [hX, htot]) (by omega) (by rw [hX]; omega)]
        rw [a1_post, buf4_post, buf3_post]
        simp only [Array.set_val_eq, bytes_set]
        rw [buf2_post, hX, hml, i7_post, i9_post, htot, i8_post, i10_post, cast_u8_usize, cast_u8_usize,
          i6_post, hbits]
        congr 4
        all_goals (try simp only [hb, hn])
      let* ⟨ st, st_post ⟩ ← thash_values_loop1_spec a1 total (wv seed.state.val) seed.state 0#usize
        (by rw [htot]) (by rw [htot]) (by simp) (by simp) (by simp)
      let* ⟨ r, r_post ⟩ ← trunc_spec
      rw [r_post, st_post, hP, T_eq_H, H_eq, if_pos (by omega), hPN, th256_eq _ _ (by simp) (by omega),
        ← hs.1]
  · rename_i h16
    have hn : N.val ≠ 16 := fun h => h16 (by scalar_tac)
    have hml : mlen.val ≤ 2166 ∧ 1246 ≤ mlen.val := by
      rw [hmlen, hb]; rcases hL with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    step*
    have hb1 : bytes (index_mut_back s2).val = (adrsS adrs).compress ++ List.replicate 2282 0#8 := by
      rw [s_post2, s2_post, s1_post, Array.val_to_slice, Array.repeat_val,
        setSlice_rep _ _ _ (by simp), bytes_append, a_post, bytes_replicate,
        show (2304#usize).val - a.val.length = 2282 by simp]
      rfl
    let* ⟨ buf2, buf2_post ⟩ ← thash_values_loop2_spec N hN blocks
      (by rw [hb]; rcases hL with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega) (adrsS adrs).compress
      (adrs_compress_length _) (index_mut_back s2) 0#usize (by simp)
      (by rw [hb1, show (0#usize).val = 0 from rfl]
          simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero, Nat.sub_zero])
    step*
    · rcases System.Platform.numBits_eq with h | h <;> simp [h]
    · have htot : total.val = (mlen.val + 17 + 127) / 128 * 128 := by
        rw [total_post, i4_post, i3_post, i2_post]
      have htle : total.val ≤ 2304 := by
        rw [htot, hmlen, hb]; rcases hL with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      have hbits : bits.val = 8 * (128 + mlen.val) := by rw [bits_post, i5_post]; ring
      have hX : ((adrsS adrs).compress ++
          (List.range blocks.length).flatMap fun (j : Nat) => blkVal N.val blocks.val[j]!).length =
          mlen.val := by
        rw [List.length_append, adrs_compress_length, hM, hmlen]
      have hP : (bytes a1.val).take total.val =
          S512.padFrom 128 ((adrsS adrs).compress ++
            (List.range blocks.length).flatMap fun (j : Nat) => blkVal N.val blocks.val[j]!) := by
        rw [← padbuf128 _ 2304 total.val (by rw [hX, htot]) htle (by rw [hX]; omega)]
        rw [a1_post, buf4_post, buf3_post]
        simp only [Array.set_val_eq, bytes_set]
        rw [buf2_post, hX, i7_post, i9_post, i8_post, i10_post, cast_u8_usize, cast_u8_usize,
          i6_post, hbits]
        congr 4
        all_goals (try (congr 2; rw [hmlen]; omega))
      let* ⟨ st, st_post ⟩ ← thash_values_loop3_spec a1 total (S512.wv seed.state512.val)
        seed.state512 0#usize (by rw [htot]; omega) htle (by simp) (by simp) (by simp)
      let* ⟨ r, r_post ⟩ ← trunc512_spec
      rw [r_post, st_post, hP, T_eq_H, H_eq, if_neg (by omega), hPN,
        th512_eq _ _ (by simp) (by omega), ← hs.2 hn]
