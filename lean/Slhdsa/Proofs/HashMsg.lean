import Slhdsa.Proofs.Hash
open Aeneas Aeneas.Std Result

/-! `PRF_msg` (HMAC) and `H_msg` (MGF1 of the inner hash). -/

namespace slhdsa

attribute [local step] hash_extend_from_slice_u8_spec

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


/-- The key padded to a 64-byte block, `K ‖ toByte(0, 64 − n)`, as machine bytes. -/
def padKey {N : Usize} (sk_prf : Array U8 N) : List U8 := sk_prf.val ++ List.replicate (64 - N.val) 0#u8

theorem prf_msg_loop0_spec {N : Usize} (hN : N.val ≤ 32) (sk_prf : Array U8 N) (ipad opad : Array U8 64#usize) (i : Usize)
    (hi : i.val ≤ N.val)
    (hin : ipad.val = ((padKey sk_prf).map (· ^^^ 54#u8)).take i.val ++
      List.replicate (64 - i.val) 54#u8)
    (hout : opad.val = ((padKey sk_prf).map (· ^^^ 92#u8)).take i.val ++
      List.replicate (64 - i.val) 92#u8) :
    hash.prf_msg_loop0 sk_prf ipad opad i ⦃ r =>
      r.1.val = (padKey sk_prf).map (· ^^^ 54#u8) ∧ r.2.val = (padKey sk_prf).map (· ^^^ 92#u8) ⦄ := by
  have hKl : (padKey sk_prf).length = 64 := by simp [padKey]; omega
  unfold hash.prf_msg_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : Array U8 64#usize × Array U8 64#usize × Usize) => N.val - q.2.2.val)
    (inv := fun q => q.2.2.val ≤ N.val ∧
      q.1.val = ((padKey sk_prf).map (· ^^^ 54#u8)).take q.2.2.val ++
        List.replicate (64 - q.2.2.val) 54#u8 ∧
      q.2.1.val = ((padKey sk_prf).map (· ^^^ 92#u8)).take q.2.2.val ++
        List.replicate (64 - q.2.2.val) 92#u8)
  · rintro ⟨ipad, opad, i⟩ ⟨hi, hin, hout⟩
    simp only [hash.prf_msg_loop0.body]
    simp only at hi hin hout
    split
    · rename_i hlt
      have hlt' : i.val < N.val := by scalar_tac
      step*
      have hpk : (padKey sk_prf)[i.val]! = i1 := by
        rw [i1_post]; simp [padKey, List.getElem!_eq_getElem?_getD, List.getElem?_append_left, hlt']
      have key : ∀ c : U8, (((padKey sk_prf).map (· ^^^ c)).take i.val ++
          List.replicate (64 - i.val) c).set i.val (i1 ^^^ c) =
          ((padKey sk_prf).map (· ^^^ c)).take (i.val + 1) ++
          List.replicate (64 - (i.val + 1)) c := by
        intro c
        have hl : i.val < ((padKey sk_prf).map (· ^^^ c)).length := by simp [hKl]; omega
        rw [show 64 - i.val = (64 - (i.val + 1)) + 1 by omega, List.replicate_succ,
          set_mid _ _ _ _ _ (by simp [hKl]; omega), List.take_succ_eq_append_getElem hl]
        simp only [List.getElem_map, List.append_assoc, List.singleton_append]
        rw [← getElem!_eq _ _ (by omega), hpk]
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [i4_post, a_post, Array.set_val_eq, hin, ← key]
        congr 1; scalar_tac
      · rw [i4_post, a1_post, Array.set_val_eq, hout, ← key]
        congr 1; scalar_tac
    · have h16 : i.val = N.val := by scalar_tac
      simp only [step_simps]
      have tail : ∀ c : U8, 0#u8 ^^^ c = c →
          ((padKey sk_prf).map (· ^^^ c)).take N.val ++ List.replicate (64 - N.val) c =
          (padKey sk_prf).map (· ^^^ c) := by
        intro c hc
        simp [padKey, hc, List.take_append]
      rw [h16] at hin hout
      exact ⟨by rw [hin]; exact tail _ (by decide), by rw [hout]; exact tail _ (by decide)⟩
  · exact ⟨hi, hin, hout⟩

/-- The key padded to a 128-byte block, `K ‖ toByte(0, 128 − n)`, as machine bytes. -/
def padKey512 {N : Usize} (sk_prf : Array U8 N) : List U8 := sk_prf.val ++ List.replicate (128 - N.val) 0#u8

theorem prf_msg_loop1_spec {N : Usize} (hN : N.val ≤ 32) (sk_prf : Array U8 N) (ipad opad : Array U8 128#usize) (i : Usize)
    (hi : i.val ≤ N.val)
    (hin : ipad.val = ((padKey512 sk_prf).map (· ^^^ 54#u8)).take i.val ++
      List.replicate (128 - i.val) 54#u8)
    (hout : opad.val = ((padKey512 sk_prf).map (· ^^^ 92#u8)).take i.val ++
      List.replicate (128 - i.val) 92#u8) :
    hash.prf_msg_loop1 sk_prf ipad opad i ⦃ r =>
      r.1.val = (padKey512 sk_prf).map (· ^^^ 54#u8) ∧ r.2.val = (padKey512 sk_prf).map (· ^^^ 92#u8) ⦄ := by
  have hKl : (padKey512 sk_prf).length = 128 := by simp [padKey512]; omega
  unfold hash.prf_msg_loop1
  apply loop.spec_decr_nat
    (measure := fun (q : Array U8 128#usize × Array U8 128#usize × Usize) => N.val - q.2.2.val)
    (inv := fun q => q.2.2.val ≤ N.val ∧
      q.1.val = ((padKey512 sk_prf).map (· ^^^ 54#u8)).take q.2.2.val ++
        List.replicate (128 - q.2.2.val) 54#u8 ∧
      q.2.1.val = ((padKey512 sk_prf).map (· ^^^ 92#u8)).take q.2.2.val ++
        List.replicate (128 - q.2.2.val) 92#u8)
  · rintro ⟨ipad, opad, i⟩ ⟨hi, hin, hout⟩
    simp only [hash.prf_msg_loop1.body]
    simp only at hi hin hout
    split
    · rename_i hlt
      have hlt' : i.val < N.val := by scalar_tac
      step*
      have hpk : (padKey512 sk_prf)[i.val]! = i1 := by
        rw [i1_post]; simp [padKey512, List.getElem!_eq_getElem?_getD, List.getElem?_append_left, hlt']
      have key : ∀ c : U8, (((padKey512 sk_prf).map (· ^^^ c)).take i.val ++
          List.replicate (128 - i.val) c).set i.val (i1 ^^^ c) =
          ((padKey512 sk_prf).map (· ^^^ c)).take (i.val + 1) ++
          List.replicate (128 - (i.val + 1)) c := by
        intro c
        have hl : i.val < ((padKey512 sk_prf).map (· ^^^ c)).length := by simp [hKl]; omega
        rw [show 128 - i.val = (128 - (i.val + 1)) + 1 by omega, List.replicate_succ,
          set_mid _ _ _ _ _ (by simp [hKl]; omega), List.take_succ_eq_append_getElem hl]
        simp only [List.getElem_map, List.append_assoc, List.singleton_append]
        rw [← getElem!_eq _ _ (by omega), hpk]
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [i4_post, a_post, Array.set_val_eq, hin, ← key]
        congr 1; scalar_tac
      · rw [i4_post, a1_post, Array.set_val_eq, hout, ← key]
        congr 1; scalar_tac
    · have h16 : i.val = N.val := by scalar_tac
      simp only [step_simps]
      have tail : ∀ c : U8, 0#u8 ^^^ c = c →
          ((padKey512 sk_prf).map (· ^^^ c)).take N.val ++ List.replicate (128 - N.val) c =
          (padKey512 sk_prf).map (· ^^^ c) := by
        intro c hc
        simp [padKey512, hc, List.take_append]
      rw [h16] at hin hout
      exact ⟨by rw [hin]; exact tail _ (by decide), by rw [hout]; exact tail _ (by decide)⟩
  · exact ⟨hi, hin, hout⟩

/-- The message slack of the signing and verification theorems: what a
message of length `len` needs around it in memory for every hash it goes
through (SHA-256 for `n = 16`, SHA-512 otherwise). -/
def msgSlack (n : Nat) : Nat := if n = 16 then 152 else 304

theorem set2_tail {α} (X : List α) (k : Nat) (z u v : α) (i j : Nat) (hi : i = X.length)
    (hj : j = X.length + k + 1) :
    ((X ++ List.replicate (k + 3) z).set i u).set j v = X ++ u :: (List.replicate k z ++ [v, z]) := by
  subst hi hj
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.length_set, List.length_append, List.length_replicate] at h1
    simp only [List.getElem_set, List.getElem_append, List.getElem_cons, List.getElem_replicate,
      List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    split_ifs <;> (try subst_vars) <;> first | rfl | omega | skip

/-- The outer block of HMAC-SHA-256 after the key block: the 32-byte inner
digest and its padding. -/
theorem fin256 (X : Spec.Bytes) (hX : X.length = 32) :
    ((X ++ List.replicate 32 0#8).set 32 0x80#8).set 62 3#8 = padFrom 64 X := by
  rw [show List.replicate 32 (0#8 : Spec.Byte) = List.replicate (29 + 3) 0#8 from rfl,
    set2_tail _ _ _ _ _ _ _ (by rw [hX]) (by rw [hX]), padFrom, hX, toByte8_small _ (by norm_num)]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [show (29 : Nat) = 23 + 6 from rfl, List.replicate_add]
  simp

/-- The same for HMAC-SHA-512 and its 64-byte inner digest. -/
theorem fin512 (X : Spec.Bytes) (hX : X.length = 64) :
    ((X ++ List.replicate 64 0#8).set 64 0x80#8).set 126 6#8 = S512.padFrom 128 X := by
  rw [show List.replicate 64 (0#8 : Spec.Byte) = List.replicate (61 + 3) 0#8 from rfl,
    set2_tail _ _ _ _ _ _ _ (by rw [hX]) (by rw [hX]), S512.padFrom, hX,
    toByte16_small _ (by norm_num)]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [show (61 : Nat) = 47 + 14 from rfl, List.replicate_add]
  simp

theorem take_drop0 (l : Spec.Bytes) (k : Nat) (h : l.length = k) : (List.drop 0 l).take k = l := by
  rw [List.drop_zero, List.take_of_length_le (by omega)]

@[step]
theorem prf_msg_spec {N : Usize} (P : Spec.Params) [family : Fact (P.family = .sha2)] (hPN : P.n = N.val) (hN : NOk N)
    (sk_prf opt_rand : Array U8 N) (m : Slice U8) (hm : Room m.length (msgSlack N.val)) :
    hash.prf_msg sk_prf opt_rand m ⦃ r =>
      bytes r.val = Spec.PRFmsg P (bytes sk_prf.val) (bytes opt_rand.val) (bytes m.val) ⦄ := by
  unfold hash.prf_msg
  have hN32 := hN.le32
  have hR := hm
  simp only [Room, msgSlack] at hR
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ buf, buf_post, buf_len ⟩ ← hash_extend_from_slice_u8_spec
  let* ⟨ buf1, buf1_post, buf1_len ⟩ ← hash_extend_from_slice_u8_spec
  · have : buf.length = N.val := by simp [buf_len, s_post]
    split at hR <;> scalar_tac
  have hl : buf1.length = N.val + m.length := by
    simp [buf1_len, buf_len, s_post]
  have hbuf : bytes buf1.val = bytes opt_rand.val ++ bytes m.val := by
    simp [buf1_post, buf_post, s_post]
  have hkl : ¬ (bytes sk_prf.val).length > 64 := by simp; omega
  have hkl' : ¬ (bytes sk_prf.val).length > 128 := by simp; omega
  have e54 : (54#u8).bv = 0x36#8 := by decide
  have e92 : (92#u8).bv = 0x5c#8 := by decide
  split
  · rename_i h16
    have hn : N.val = 16 := by scalar_tac
    simp only [hn, if_true] at hR
    step with prf_msg_loop0_spec as ⟨ipad1, opad1, hin, hout⟩
    · simp [Array.repeat_val]
    · simp [Array.repeat_val]
    have hIl : bytes ipad1.val = (bytes sk_prf.val ++ List.replicate (64 - N.val) 0#8).map (· ^^^ 0x36#8) := by
      rw [hin, bytes_map_xor, show U8.bv 54#u8 = 0x36#8 by decide]; simp [padKey, bytes]
    have hOl : bytes opad1.val = (bytes sk_prf.val ++ List.replicate (64 - N.val) 0#8).map (· ^^^ 0x5c#8) := by
      rw [hout, bytes_map_xor, show U8.bv 92#u8 = 0x5c#8 by decide]; simp [padKey, bytes]
    step*
    all_goals try (simp only [Room, vec_deref_length, hl]; scalar_tac)
    all_goals try (simp; omega)
    all_goals try (simp only [Slice.length, s8_post, Array.repeat_val, List.length_replicate] at s9_post1 ⊢; scalar_tac)
    · have hfin : bytes fin3.val = padFrom 64 (bytes inner.val) := by
        rw [fin3_post, fin2_post]
        simp only [Array.set_val_eq, bytes_set]
        rw [s4_post2, s6_post, s5_post, Array.val_to_slice, Array.repeat_val,
          setSlice_rep _ _ _ (by simp), bytes_append, bytes_replicate,
          show (64#usize).val - inner.val.length = 32 by simp]
        exact fin256 _ (by simp)
      have hv : (Array.from_slice (Array.repeat N 0#u8) s9).val = s9.val :=
        Array.from_slice_val _ _ (by scalar_tac)
      simp only [to_slice_mut_back_post, s10_post, hv, s9_post, List.slice]
      rw [s7_post, Array.val_to_slice, take_drop0 _ _ (by simp), hfin] at a_post
      rw [s3_post, Array.val_to_slice, take_drop0 _ _ (by simp), H0_eq] at outer_state_post
      rw [s1_post, Array.val_to_slice, take_drop0 _ _ (by simp), H0_eq] at inner_state_post
      rw [outer_state_post, ← hashFrom_one _ _ (by rw [← hfin]; simp)] at a_post
      rw [inner_state_post, ← sha256_prefix64 _ _ (by simp), vec_deref_val, hbuf] at inner_post
      simp only [Array.val_to_slice, List.drop_zero, Nat.sub_zero, bytes_take, d_post, a_post]
      rw [← sha256_prefix64 _ _ (by simp), inner_post]
      have hNl : 64 - (bytes sk_prf.val).length = 64 - N.val := by simp
      simp only [Spec.PRFmsg, family.out, Spec.hmacSha256, hkl, ↓reduceIte, hPN, hn, hNl]
      rw [hIl, hOl, hn]
  · rename_i h16
    have hn : N.val ≠ 16 := fun h => h16 (by scalar_tac)
    simp only [hn, if_false] at hR
    step with prf_msg_loop1_spec as ⟨ipad1, opad1, hin, hout⟩
    · simp [Array.repeat_val]
    · simp [Array.repeat_val]
    have hIl : bytes ipad1.val = (bytes sk_prf.val ++ List.replicate (128 - N.val) 0#8).map (· ^^^ 0x36#8) := by
      rw [hin, bytes_map_xor, show U8.bv 54#u8 = 0x36#8 by decide]; simp [padKey512, bytes]
    have hOl : bytes opad1.val = (bytes sk_prf.val ++ List.replicate (128 - N.val) 0#8).map (· ^^^ 0x5c#8) := by
      rw [hout, bytes_map_xor, show U8.bv 92#u8 = 0x5c#8 by decide]; simp [padKey512, bytes]
    step*
    all_goals try (simp only [vec_deref_length, hl]; scalar_tac)
    all_goals try (simp; omega)
    all_goals try (simp only [Slice.length, s8_post, Array.repeat_val, List.length_replicate] at s9_post1 ⊢; scalar_tac)
    · have hfin : bytes fin3.val = S512.padFrom 128 (bytes inner.val) := by
        rw [fin3_post, fin2_post]
        simp only [Array.set_val_eq, bytes_set]
        rw [s4_post2, s6_post, s5_post, Array.val_to_slice, Array.repeat_val,
          setSlice_rep _ _ _ (by simp), bytes_append, bytes_replicate,
          show (128#usize).val - inner.val.length = 64 by simp]
        exact fin512 _ (by simp)
      have hv : (Array.from_slice (Array.repeat N 0#u8) s9).val = s9.val :=
        Array.from_slice_val _ _ (by scalar_tac)
      simp only [to_slice_mut_back_post, s10_post, hv, s9_post, List.slice]
      rw [s7_post, Array.val_to_slice, take_drop0 _ _ (by simp), hfin] at a_post
      rw [s3_post, Array.val_to_slice, take_drop0 _ _ (by simp), S512.H0_eq] at outer_state_post
      rw [s1_post, Array.val_to_slice, take_drop0 _ _ (by simp), S512.H0_eq] at inner_state_post
      rw [outer_state_post, ← hashFrom512_one _ _ (by rw [← hfin]; simp)] at a_post
      rw [inner_state_post, ← S512.sha512_prefix128 _ _ (by simp), vec_deref_val, hbuf] at inner_post
      simp only [Array.val_to_slice, List.drop_zero, Nat.sub_zero, bytes_take, d_post, a_post]
      rw [← S512.sha512_prefix128 _ _ (by simp), inner_post]
      have hNl : 128 - (bytes sk_prf.val).length = 128 - N.val := by simp
      simp only [Spec.PRFmsg, family.out, Spec.hmacSha512, hkl', ↓reduceIte, hPN, hn, hNl]
      rw [hIl, hOl]

/-- Four pieces written one after another into a zero block that they fill. -/
theorem build4 {α} (A L R M : List α) (z : α) (K i j l : Nat) (hi : i = A.length)
    (hj : j = A.length + L.length) (hl : l = A.length + L.length + R.length)
    (h : A.length + L.length + R.length + M.length = K) :
    ((((List.replicate K z).setSlice! 0 A).setSlice! i L).setSlice! j R).setSlice! l M =
      A ++ L ++ R ++ M := by
  rw [build3 A L R z K i j hi hj (by omega), setSlice_app _ _ _ _ _ (by simp [hl]; omega) (by omega)]
  simp [show K - A.length - L.length - R.length - M.length = 0 by omega]

/-- The inner hash of `H_msg` for `n = 16`: for a message of at least
`64 − 3n` bytes the first block is assembled and the rest hashed in place;
the result is SHA-256 either way. -/
@[step]
theorem h_msg_inner256_spec {N : Usize} (hN : 3 * N.val ≤ 64) (r pk_seed pk_root : Array U8 N)
    (m : Slice U8) (hm : Room (3 * N.val + m.length) 72) :
    hash.h_msg_inner256 r pk_seed pk_root m ⦃ d =>
      bytes d.val = Spec.sha256
        (bytes r.val ++ bytes pk_seed.val ++ bytes pk_root.val ++ bytes m.val) ⦄ := by
  unfold hash.h_msg_inner256
  have hR := hm
  simp only [Room] at hR
  have hrl : r.val.length = N.val := by simp
  have hsl : pk_seed.val.length = N.val := by simp
  have hol : pk_root.val.length = N.val := by simp
  let* ⟨ i, i_post ⟩ ← Usize.mul_spec
  let* ⟨ head, head_post ⟩ ← Usize.sub_spec
  split
  · rename_i hge
    step*
    all_goals try (subst_vars; scalar_tac)
    have hb4 : (index_mut_back3 s11).val = r.val ++ pk_seed.val ++ pk_root.val ++ m.val.take head.val := by
      rw [s9_post2, s11_post, s10_post, s6_post2, s8_post, s7_post, s3_post2, s5_post, s4_post,
        s_post2, s2_post, s1_post, Array.val_to_slice, Array.val_to_slice, Array.val_to_slice,
        Array.repeat_val, build4 _ _ _ _ _ _ _ _ _ (by simp [hrl]) (by simp [hrl, hsl, i2_post]; omega)
          (by simp [hrl, hsl, i_post]; omega) (by simp [hrl, hsl, hol, List.slice]; scalar_tac)]
      simp [List.slice]
    have hBl : (bytes (index_mut_back3 s11).val).length = 64 := by simp
    rw [s12_post, Array.val_to_slice, take_drop0 _ _ hBl, H0_eq] at st_post
    have hs13 : bytes s13.val = (bytes m.val).drop head.val := by
      simp [s13_post, List.slice]
    rw [d_post, st_post, hs13, ← sha256_prefix64 _ _ hBl, hb4]
    simp only [bytes_append, bytes_take, List.append_assoc, List.take_append_drop]
  · step*
    simp [*, vec_deref_val]

/-- The inner hash of `H_msg` for `n > 16`: for a message of at least
`128 − 3n` bytes the first block is assembled and the rest hashed in place;
the result is SHA-512 either way. -/
@[step]
theorem h_msg_inner512_spec {N : Usize} (hN : 3 * N.val ≤ 128) (r pk_seed pk_root : Array U8 N)
    (m : Slice U8) (hm : 3 * N.val + m.length + 144 ≤ Usize.max) :
    hash.h_msg_inner512 r pk_seed pk_root m ⦃ d =>
      bytes d.val = Spec.sha512
        (bytes r.val ++ bytes pk_seed.val ++ bytes pk_root.val ++ bytes m.val) ⦄ := by
  unfold hash.h_msg_inner512
  have hrl : r.val.length = N.val := by simp
  have hsl : pk_seed.val.length = N.val := by simp
  have hol : pk_root.val.length = N.val := by simp
  let* ⟨ i, i_post ⟩ ← Usize.mul_spec
  let* ⟨ head, head_post ⟩ ← Usize.sub_spec
  split
  · rename_i hge
    step*
    all_goals try (subst_vars; scalar_tac)
    have hb4 : (index_mut_back3 s11).val = r.val ++ pk_seed.val ++ pk_root.val ++ m.val.take head.val := by
      rw [s9_post2, s11_post, s10_post, s6_post2, s8_post, s7_post, s3_post2, s5_post, s4_post,
        s_post2, s2_post, s1_post, Array.val_to_slice, Array.val_to_slice, Array.val_to_slice,
        Array.repeat_val, build4 _ _ _ _ _ _ _ _ _ (by simp [hrl]) (by simp [hrl, hsl, i2_post]; omega)
          (by simp [hrl, hsl, i_post]; omega) (by simp [hrl, hsl, hol, List.slice]; scalar_tac)]
      simp [List.slice]
    have hBl : (bytes (index_mut_back3 s11).val).length = 128 := by simp
    rw [s12_post, Array.val_to_slice, take_drop0 _ _ hBl, S512.H0_eq] at st_post
    have hs13 : bytes s13.val = (bytes m.val).drop head.val := by
      simp [s13_post, List.slice]
    rw [d_post, st_post, hs13, ← S512.sha512_prefix128 _ _ hBl, hb4]
    simp only [bytes_append, bytes_take, List.append_assoc, List.take_append_drop]
  · step*
    simp [*, vec_deref_val]

theorem nok_of_valid {N : Usize} (p : params.Params) (hv : (paramsS p).Valid) (hPN : p.n = N) :
    NOk N := by
  have h := hv.n_cases
  simp only [paramsS_n] at h
  rw [hPN] at h
  exact h

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
theorem h_msg_spec {N : Usize} (p : params.Params) (hv : (paramsS p).Valid) (hPN : p.n = N)
    (r pk_seed pk_root : Array U8 N) (m : Slice U8) (hm : Room m.length (msgSlack N.val)) :
    hash.h_msg p r pk_seed pk_root m ⦃ d =>
      bytes d.val = Spec.Hmsg (paramsS p) (bytes r.val) (bytes pk_seed.val) (bytes pk_root.val)
        (bytes m.val) ∧ d.length = p.m.val ⦄ := by
  unfold hash.h_msg
  have hN := nok_of_valid p hv hPN
  have hN32 := hN.le32
  have hmle := valid_m_le p hv
  have hpn : (paramsS p).n = N.val := by simp [hPN]
  have hR := hm
  simp only [Room, msgSlack] at hR
  step*
  all_goals try (simp only [Room, vec_deref_length] at *; split at hR <;> scalar_tac)
  all_goals try (simp [Room, vec_deref_length, seed2_post1, seed1_post1, seed_post1, s2_post,
    s1_post, s_post]; constructor <;> scalar_tac)
  · have hn : N.val = 16 := by scalar_tac
    refine ⟨?_, by assumption⟩
    rw [d_post]
    simp [Spec.Hmsg, hPN, hn, seed2_post, seed1_post, seed_post, s2_post, s1_post, s_post, inner_post,
      vec_deref_val]
  · have hn : N.val ≠ 16 := by
      rename_i h _ _ _; intro h'; apply h; scalar_tac
    refine ⟨?_, by assumption⟩
    rw [d_post]
    simp [Spec.Hmsg, hPN, hn, seed2_post, seed1_post, seed_post, s2_post, s1_post, s_post, inner_post,
      vec_deref_val]

end slhdsa
