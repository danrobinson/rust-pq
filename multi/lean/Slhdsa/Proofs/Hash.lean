import Slhdsa.Proofs.Sha512
import Slhdsa.Proofs.Params
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

theorem PRF_eq_F (p : Spec.Params) (pk sk : Spec.Bytes) (a : Spec.Adrs) :
    Spec.PRF p pk sk a = Spec.F p pk a sk := rfl

theorem T_eq_H (p : Spec.Params) (pk : Spec.Bytes) (a : Spec.Adrs) (m : Spec.Bytes) :
    Spec.T p pk a m = Spec.H p pk a m := rfl

theorem toByte_zero (k : Nat) : Spec.toByte 0 k = List.replicate k 0#8 := by
  apply List.ext_getElem
  · simp [Spec.toByte]
  · intro i h1 h2
    simp [Spec.toByte]

theorem zeros_slice (N : Usize) (i : Usize) (s : Slice U8) (hi : i.val ≤ N.val)
    (hs : s.val = List.slice 0 i.val (List.replicate N.val 0#u8)) :
    bytes s.val = Spec.toByte 0 i.val := by
  rw [hs, toByte_zero]
  simp [List.slice, bytes, List.take_replicate, hi]

theorem valid_n_le (p : params.Params) (hv : (paramsS p).Valid) : 16 ≤ p.n.val ∧ p.n.val ≤ 32 := by
  have h := hv.n_cases
  simp only [paramsS_n] at h
  omega

/-- `F` and `PRF` (the latter through `PRF_eq_F`). -/
@[step]
theorem thash_f_spec (p : params.Params) (pk : Slice U8) (a : address.Adrs) (m : Slice U8)
    (hv : (paramsS p).Valid) (hpk : pk.length = p.n.val) (hm : m.length ≤ 65536) :
    hash.thash_f p pk a m ⦃ r =>
      bytes r.val = Spec.F (paramsS p) (bytes pk.val) (adrsS a) (bytes m.val) ∧
      r.length = p.n.val ⦄ := by
  unfold hash.thash_f
  have hn := valid_n_le p hv
  let* ⟨ buf, buf_post, buf_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ i, i_post ⟩ ← Usize.sub_spec
  let* ⟨ s, s_post, s_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
  let* ⟨ buf1, buf1_post, buf1_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ a1, a1_post ⟩ ← adrs_compress_spec
  let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ buf2, buf2_post, buf2_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ buf3, buf3_post, buf3_len ⟩ ← hash_extend_from_slice_u8_spec
  have hl : buf3.length = 86 + m.length := by
    simp [buf3_len, buf2_len, buf1_len, buf_len, s_len, s1_post]; scalar_tac
  let* ⟨ d, d_post ⟩ ← sha256_spec
  · simp only [Room, vec_deref_length]; scalar_tac
  let* ⟨ s3, s3_post, s3_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
  let* ⟨ out, out_post, out_len ⟩ ← hash_extend_from_slice_u8_spec
  have hz := zeros_slice 64#usize i s (by scalar_tac) (by rw [s_post]; simp)
  refine ⟨?_, by simp [out_len, s3_len]⟩
  simp only [out_post, s3_post, List.slice]
  simp [Spec.F, d_post, buf3_post, buf2_post, buf1_post, buf_post, hz, i_post, a1_post, s1_post]

/-- `H` and `T_l` (the latter through `T_eq_H`). -/
@[step]
theorem thash_h_spec (p : params.Params) (pk : Slice U8) (a : address.Adrs) (m : Slice U8)
    (hv : (paramsS p).Valid) (hpk : pk.length = p.n.val) (hm : m.length ≤ 65536) :
    hash.thash_h p pk a m ⦃ r =>
      bytes r.val = Spec.H (paramsS p) (bytes pk.val) (adrsS a) (bytes m.val) ∧
      r.length = p.n.val ⦄ := by
  unfold hash.thash_h
  have hn := valid_n_le p hv
  split
  · rename_i h16
    have h16' : p.n.val = 16 := by scalar_tac
    let* ⟨ r, r_post, r_len ⟩ ← thash_f_spec
    refine ⟨?_, r_len⟩
    simp [r_post, Spec.H, Spec.F, h16']
  · rename_i h16
    have h16' : p.n.val ≠ 16 := by scalar_tac
    let* ⟨ buf, buf_post, buf_len ⟩ ← hash_extend_from_slice_u8_spec
    let* ⟨ i, i_post ⟩ ← Usize.sub_spec
    let* ⟨ s, s_post, s_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    let* ⟨ buf1, buf1_post, buf1_len ⟩ ← hash_extend_from_slice_u8_spec
    let* ⟨ a1, a1_post ⟩ ← adrs_compress_spec
    let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
    let* ⟨ buf2, buf2_post, buf2_len ⟩ ← hash_extend_from_slice_u8_spec
    let* ⟨ buf3, buf3_post, buf3_len ⟩ ← hash_extend_from_slice_u8_spec
    have hl : buf3.length = 150 + m.length := by
      simp [buf3_len, buf2_len, buf1_len, buf_len, s_len, s1_post]; scalar_tac
    let* ⟨ d, d_post ⟩ ← sha512_spec
    let* ⟨ s3, s3_post, s3_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    let* ⟨ out, out_post, out_len ⟩ ← hash_extend_from_slice_u8_spec
    have hz := zeros_slice 128#usize i s (by scalar_tac) (by rw [s_post]; simp)
    refine ⟨?_, by simp [out_len, s3_len]⟩
    simp only [out_post, s3_post, List.slice]
    simp [Spec.H, h16', d_post, buf3_post, buf2_post, buf1_post, buf_post, hz, i_post, a1_post,
      s1_post]

@[step]
theorem prf_msg_spec (p : params.Params) (sk_prf opt_rand m : Slice U8)
    (hv : (paramsS p).Valid) (hsk : sk_prf.length = p.n.val) (hr : opt_rand.length = p.n.val)
    (hm : Room m.length 304) :
    hash.prf_msg p sk_prf opt_rand m ⦃ r =>
      bytes r.val = Spec.PRFmsg (paramsS p) (bytes sk_prf.val) (bytes opt_rand.val) (bytes m.val) ∧
      r.length = p.n.val ⦄ := by
  unfold hash.prf_msg
  have hn := valid_n_le p hv
  have hR := hm
  simp only [Room] at hR
  let* ⟨ buf, buf_post, buf_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ buf1, buf1_post, buf1_len ⟩ ← hash_extend_from_slice_u8_spec
  have hl : buf1.length = p.n.val + m.length := by
    simp [buf1_len, buf_len, hr]
  split
  · rename_i h16
    have h16' : p.n.val = 16 := by scalar_tac
    let* ⟨ d, d_post ⟩ ← hmac_sha256_spec
    · simp only [Room, vec_deref_length]; scalar_tac
    let* ⟨ s3, s3_post, s3_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    let* ⟨ out, out_post, out_len ⟩ ← hash_extend_from_slice_u8_spec
    refine ⟨?_, by simp [out_len, s3_len]⟩
    simp only [out_post, s3_post, List.slice]
    simp [Spec.PRFmsg, h16', d_post, buf1_post, buf_post]
  · rename_i h16
    have h16' : p.n.val ≠ 16 := by scalar_tac
    let* ⟨ d, d_post ⟩ ← hmac_sha512_spec
    let* ⟨ s3, s3_post, s3_len ⟩ ← core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    let* ⟨ out, out_post, out_len ⟩ ← hash_extend_from_slice_u8_spec
    refine ⟨?_, by simp [out_len, s3_len]⟩
    simp only [out_post, s3_post, List.slice]
    simp [Spec.PRFmsg, h16', d_post, buf1_post, buf_post]

/-- The four-byte big-endian counter of MGF1. -/
theorem counter_bytes (c : U32) (i1 i3 i5 : U32) (i2 i4 i6 i7 : U8)
    (h1 : i1.bv = c.bv >>> 24) (h2 : i2 = UScalar.cast .U8 i1)
    (h3 : i3.bv = c.bv >>> 16) (h4 : i4 = UScalar.cast .U8 i3)
    (h5 : i5.bv = c.bv >>> 8) (h6 : i6 = UScalar.cast .U8 i5)
    (h7 : i7 = UScalar.cast .U8 c) :
    bytes [i2, i4, i6, i7] = Spec.toByte c.val 4 := by
  rw [← U32.bv_toNat, toByte4]
  simp [bytes, *]

theorem mgf1_sha256_loop_spec (seed : Slice U8) (len : Usize) (t : alloc.vec.Vec U8) (c : U32)
    (hs : Room seed.length 76) (hlen : len.val ≤ 65536)
    (hinv : bytes t.val = (List.range c.val).flatMap
      fun c => Spec.sha256 (bytes seed.val ++ Spec.toByte c 4))
    (htl : t.length = 32 * c.val) (hc : 32 * c.val < len.val + 32) :
    hash.mgf1_sha256_loop seed len t c ⦃ r =>
      bytes r.val = (List.range ((len.val + 32 - 1) / 32)).flatMap
        (fun c => Spec.sha256 (bytes seed.val ++ Spec.toByte c 4)) ∧
      len.val ≤ r.length ⦄ := by
  unfold hash.mgf1_sha256_loop
  have hR := hs
  simp only [Room] at hR
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32) => len.val + 32 - q.1.length)
    (inv := fun q => bytes q.1.val = (List.range q.2.val).flatMap
        (fun c => Spec.sha256 (bytes seed.val ++ Spec.toByte c 4)) ∧
      q.1.length = 32 * q.2.val ∧ 32 * q.2.val < len.val + 32)
  · rintro ⟨t, c⟩ ⟨hinv, htl, hc⟩
    simp only [hash.mgf1_sha256_loop.body]
    simp only at hinv htl hc
    simp only [alloc.vec.Vec.len]
    split
    · rename_i hlt
      let* ⟨ buf, buf_post, buf_len ⟩ ← hash_extend_from_slice_u8_spec
      let* ⟨ i1, i1_post, i1_bv ⟩ ← U32.ShiftRight_IScalar_spec
      let* ⟨ i2, i2_post ⟩ ← UScalar.cast.step_spec
      let* ⟨ i3, i3_post, i3_bv ⟩ ← U32.ShiftRight_IScalar_spec
      let* ⟨ i4, i4_post ⟩ ← UScalar.cast.step_spec
      let* ⟨ i5, i5_post, i5_bv ⟩ ← U32.ShiftRight_IScalar_spec
      let* ⟨ i6, i6_post ⟩ ← UScalar.cast.step_spec
      let* ⟨ i7, i7_post ⟩ ← UScalar.cast.step_spec
      let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ buf1, buf1_post, buf1_len ⟩ ← hash_extend_from_slice_u8_spec
      have hb : buf1.length = seed.length + 4 := by
        simp [buf1_len, buf_len, s_post]
      let* ⟨ d, d_post ⟩ ← sha256_spec
      · simp only [Room, vec_deref_length]; scalar_tac
      let* ⟨ s2, s2_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ t1, t1_post, t1_len ⟩ ← hash_extend_from_slice_u8_spec
      let* ⟨ c1, c1_post ⟩ ← U32.add_spec
      have hcb := counter_bytes c i1 i3 i5 i2 i4 i6 i7 i1_bv i2_post i3_bv i4_post i5_bv i6_post
        i7_post
      have hd : s2.length = 32 := by scalar_tac
      refine ⟨?_, by scalar_tac, by scalar_tac, by scalar_tac⟩
      rw [c1_post, List.range_succ, List.flatMap_append, ← hinv, t1_post, bytes_append, s2_post]
      simp [← hcb, d_post, buf1_post, buf_post, s_post]
    · rename_i hge
      simp only [WP.spec_ok]
      have h1 : len.val ≤ t.length := by scalar_tac
      have h2 : (len.val + 32 - 1) / 32 = c.val := by scalar_tac
      rw [h2]
      exact ⟨hinv, h1⟩
  · exact ⟨hinv, htl, hc⟩

@[step]
theorem mgf1_sha256_spec (seed : Slice U8) (len : Usize)
    (hs : Room seed.length 76) (hlen : len.val ≤ 65536) :
    hash.mgf1_sha256 seed len ⦃ r =>
      bytes r.val = Spec.mgf1 Spec.sha256 32 (bytes seed.val) len.val ∧ r.length = len.val ⦄ := by
  unfold hash.mgf1_sha256
  let* ⟨ t, t_post, t_len ⟩ ← mgf1_sha256_loop_spec
  · simp
  let* ⟨ s, s_post, s_len ⟩ ← alloc.vec.Vec.index_Range_spec
  let* ⟨ out, out_post, out_len ⟩ ← hash_extend_from_slice_u8_spec
  refine ⟨?_, by simp [out_len, s_len]⟩
  simp only [out_post, s_post, List.slice]
  simp [Spec.mgf1, t_post]

theorem mgf1_sha512_loop_spec (seed : Slice U8) (len : Usize) (t : alloc.vec.Vec U8) (c : U32)
    (hs : seed.length + 148 ≤ Usize.max) (hlen : len.val ≤ 65536)
    (hinv : bytes t.val = (List.range c.val).flatMap
      fun c => Spec.sha512 (bytes seed.val ++ Spec.toByte c 4))
    (htl : t.length = 64 * c.val) (hc : 64 * c.val < len.val + 64) :
    hash.mgf1_sha512_loop seed len t c ⦃ r =>
      bytes r.val = (List.range ((len.val + 64 - 1) / 64)).flatMap
        (fun c => Spec.sha512 (bytes seed.val ++ Spec.toByte c 4)) ∧
      len.val ≤ r.length ⦄ := by
  unfold hash.mgf1_sha512_loop
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32) => len.val + 64 - q.1.length)
    (inv := fun q => bytes q.1.val = (List.range q.2.val).flatMap
        (fun c => Spec.sha512 (bytes seed.val ++ Spec.toByte c 4)) ∧
      q.1.length = 64 * q.2.val ∧ 64 * q.2.val < len.val + 64)
  · rintro ⟨t, c⟩ ⟨hinv, htl, hc⟩
    simp only [hash.mgf1_sha512_loop.body]
    simp only at hinv htl hc
    simp only [alloc.vec.Vec.len]
    split
    · rename_i hlt
      let* ⟨ buf, buf_post, buf_len ⟩ ← hash_extend_from_slice_u8_spec
      let* ⟨ i1, i1_post, i1_bv ⟩ ← U32.ShiftRight_IScalar_spec
      let* ⟨ i2, i2_post ⟩ ← UScalar.cast.step_spec
      let* ⟨ i3, i3_post, i3_bv ⟩ ← U32.ShiftRight_IScalar_spec
      let* ⟨ i4, i4_post ⟩ ← UScalar.cast.step_spec
      let* ⟨ i5, i5_post, i5_bv ⟩ ← U32.ShiftRight_IScalar_spec
      let* ⟨ i6, i6_post ⟩ ← UScalar.cast.step_spec
      let* ⟨ i7, i7_post ⟩ ← UScalar.cast.step_spec
      let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ buf1, buf1_post, buf1_len ⟩ ← hash_extend_from_slice_u8_spec
      have hb : buf1.length = seed.length + 4 := by
        simp [buf1_len, buf_len, s_post]
      let* ⟨ d, d_post ⟩ ← sha512_spec
      let* ⟨ s2, s2_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ t1, t1_post, t1_len ⟩ ← hash_extend_from_slice_u8_spec
      let* ⟨ c1, c1_post ⟩ ← U32.add_spec
      have hcb := counter_bytes c i1 i3 i5 i2 i4 i6 i7 i1_bv i2_post i3_bv i4_post i5_bv i6_post
        i7_post
      have hd : s2.length = 64 := by scalar_tac
      refine ⟨?_, by scalar_tac, by scalar_tac, by scalar_tac⟩
      rw [c1_post, List.range_succ, List.flatMap_append, ← hinv, t1_post, bytes_append, s2_post]
      simp [← hcb, d_post, buf1_post, buf_post, s_post]
    · rename_i hge
      simp only [WP.spec_ok]
      have h1 : len.val ≤ t.length := by scalar_tac
      have h2 : (len.val + 64 - 1) / 64 = c.val := by scalar_tac
      rw [h2]
      exact ⟨hinv, h1⟩
  · exact ⟨hinv, htl, hc⟩

@[step]
theorem mgf1_sha512_spec (seed : Slice U8) (len : Usize)
    (hs : seed.length + 148 ≤ Usize.max) (hlen : len.val ≤ 65536) :
    hash.mgf1_sha512 seed len ⦃ r =>
      bytes r.val = Spec.mgf1 Spec.sha512 64 (bytes seed.val) len.val ∧ r.length = len.val ⦄ := by
  unfold hash.mgf1_sha512
  let* ⟨ t, t_post, t_len ⟩ ← mgf1_sha512_loop_spec
  · simp
  let* ⟨ s, s_post, s_len ⟩ ← alloc.vec.Vec.index_Range_spec
  let* ⟨ out, out_post, out_len ⟩ ← hash_extend_from_slice_u8_spec
  refine ⟨?_, by simp [out_len, s_len]⟩
  simp only [out_post, s_post, List.slice]
  simp [Spec.mgf1, t_post]

theorem valid_m_le (p : params.Params) (hv : (paramsS p).Valid) : p.m.val ≤ 65536 := by
  have h1 := hv.m_eq
  have h2 := hv.k_le
  have h3 := hv.a_le
  have h4 := hv.d_le
  have h5 := hv.hp_le
  have h6 := hv.h_eq
  simp only [paramsS_m, paramsS_k, paramsS_a, paramsS_d, paramsS_hp, paramsS_h,
    Spec.Params.mdBytes, Spec.Params.treeBytes, Spec.Params.leafBytes] at h1 h2 h3 h4 h5 h6
  have h7 : p.k.val * p.a.val ≤ 35 * 14 := Nat.mul_le_mul h2 h3
  have h8 : p.d.val * p.hp.val ≤ 22 * 9 := Nat.mul_le_mul h4 h5
  have h9 : p.h.val / p.d.val ≤ p.h.val := Nat.div_le_self _ _
  omega

@[step]
theorem h_msg_spec (p : params.Params) (r pk_seed pk_root m : Slice U8)
    (hv : (paramsS p).Valid) (hr : r.length = p.n.val) (hpk : pk_seed.length = p.n.val)
    (hroot : pk_root.length = p.n.val) (hm : Room m.length 304) :
    hash.h_msg p r pk_seed pk_root m ⦃ d =>
      bytes d.val = Spec.Hmsg (paramsS p) (bytes r.val) (bytes pk_seed.val) (bytes pk_root.val)
        (bytes m.val) ∧
      d.length = p.m.val ⦄ := by
  unfold hash.h_msg
  have hn := valid_n_le p hv
  have hmle := valid_m_le p hv
  have hR := hm
  simp only [Room] at hR
  let* ⟨ buf, buf_post, buf_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ buf1, buf1_post, buf1_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ buf2, buf2_post, buf2_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ buf3, buf3_post, buf3_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ seed, seed_post, seed_len ⟩ ← hash_extend_from_slice_u8_spec
  have hl : buf3.length = 3 * p.n.val + m.length := by
    simp [buf3_len, buf2_len, buf1_len, buf_len, hr, hpk, hroot]; omega
  have hl2 : seed.length = 2 * p.n.val := by
    simp [seed_len, buf_len, hr, hpk]; omega
  split
  · rename_i h16
    have h16' : p.n.val = 16 := by scalar_tac
    let* ⟨ inner, inner_post ⟩ ← sha256_spec
    · simp only [Room, vec_deref_length]; scalar_tac
    let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
    let* ⟨ seed1, seed1_post, seed1_len ⟩ ← hash_extend_from_slice_u8_spec
    have hl3 : seed1.length = 2 * p.n.val + 32 := by
      simp [seed1_len, hl2, s1_post]
    let* ⟨ d, d_post, d_len ⟩ ← mgf1_sha256_spec
    · simp only [Room, vec_deref_length]; scalar_tac
    refine ⟨?_, d_len⟩
    simp [d_post, Spec.Hmsg, h16', seed1_post, seed_post, s1_post, inner_post, buf3_post,
      buf2_post, buf1_post, buf_post]
  · rename_i h16
    have h16' : p.n.val ≠ 16 := by scalar_tac
    let* ⟨ inner, inner_post ⟩ ← sha512_spec
    let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
    let* ⟨ seed1, seed1_post, seed1_len ⟩ ← hash_extend_from_slice_u8_spec
    have hl3 : seed1.length = 2 * p.n.val + 64 := by
      simp [seed1_len, hl2, s1_post]
    let* ⟨ d, d_post, d_len ⟩ ← mgf1_sha512_spec
    refine ⟨?_, d_len⟩
    simp [d_post, Spec.Hmsg, h16', seed1_post, seed_post, s1_post, inner_post, buf3_post,
      buf2_post, buf1_post, buf_post]

end slhdsa
