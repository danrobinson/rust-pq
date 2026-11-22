import Slhdsa.Proofs.Basic
open Aeneas Aeneas.Std Result

/-! The crate's byte encodings, module `encoding`: what a caller's bytes are accepted as, and
the PKCS#8 and `SubjectPublicKeyInfo` wrappers (a fixed prefix followed by the key). -/

namespace slhdsa

theorem pkcs8_prefix_val : encoding.PKCS8_PREFIX.val =
    [0x30#u8, 0x52#u8, 0x02#u8, 0x01#u8, 0x00#u8, 0x30#u8, 0x0b#u8, 0x06#u8, 0x09#u8, 0x60#u8,
     0x86#u8, 0x48#u8, 0x01#u8, 0x65#u8, 0x03#u8, 0x04#u8, 0x03#u8, 0x14#u8, 0x04#u8, 0x40#u8] := by
  simp [encoding.PKCS8_PREFIX]

theorem spki_prefix_val : encoding.SPKI_PREFIX.val =
    [0x30#u8, 0x30#u8, 0x30#u8, 0x0b#u8, 0x06#u8, 0x09#u8, 0x60#u8, 0x86#u8, 0x48#u8, 0x01#u8,
     0x65#u8, 0x03#u8, 0x04#u8, 0x03#u8, 0x14#u8, 0x03#u8, 0x21#u8, 0x00#u8] := by
  simp [encoding.SPKI_PREFIX]

@[step]
theorem secret_key_from_spec (b : Slice U8) :
    encoding.secret_key_from b ⦃ r => r.map (·.val) = if b.length = 64 then some b.val else none ⦄ := by
  unfold encoding.secret_key_from
  simp only [global_simps]
  step*
  · have h := ‹(b.len != 64#usize) = true›
    simp at h
    simp [Slice.length, h]
  · have h := ‹¬(b.len != 64#usize) = true›
    simp at h
    rw [to_slice_mut_back_post, s1_post]
    simp [Slice.length, h, Array.from_slice_val (Array.repeat 64#usize 0#u8) b (by simp [h])]

@[step]
theorem public_key_from_spec (b : Slice U8) :
    encoding.public_key_from b ⦃ r => r.map (·.val) = if b.length = 32 then some b.val else none ⦄ := by
  unfold encoding.public_key_from
  simp only [global_simps]
  step*
  · have h := ‹(b.len != 32#usize) = true›
    simp at h
    simp [Slice.length, h]
  · have h := ‹¬(b.len != 32#usize) = true›
    simp at h
    rw [to_slice_mut_back_post, s1_post]
    simp [Slice.length, h, Array.from_slice_val (Array.repeat 32#usize 0#u8) b (by simp [h])]

theorem signature_len_ok_eq (b : Slice U8) :
    encoding.signature_len_ok b = ok (decide (b.length = 7856)) := by
  unfold encoding.signature_len_ok
  simp only [global_simps]
  simp [UScalar.eq_equiv, Slice.length]

theorem or_xor_zero (d x y : U8) : (d ||| (x ^^^ y)) = 0#u8 ↔ d = 0#u8 ∧ x = y := by
  rw [UScalar.eq_equiv_bv_eq, UScalar.eq_equiv_bv_eq d, UScalar.eq_equiv_bv_eq x,
    UScalar.bv_or, UScalar.bv_xor]
  simp [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]

theorem secret_keys_equal_loop_spec (a b : Array U8 64#usize) (diff : U8) (i : Usize)
    (hi : i.val ≤ 64) (hd : diff = 0#u8 ↔ ∀ j < i.val, a.val[j]! = b.val[j]!) :
    encoding.secret_keys_equal_loop a b diff i ⦃ r => r = 0#u8 ↔ a = b ⦄ := by
  unfold encoding.secret_keys_equal_loop
  apply loop.spec_decr_nat (measure := fun (p : U8 × Usize) => 64 - p.2.val)
    (inv := fun p => p.2.val ≤ 64 ∧ (p.1 = 0#u8 ↔ ∀ j < p.2.val, a.val[j]! = b.val[j]!))
  · rintro ⟨diff, i⟩ ⟨hi, hd⟩
    simp only [encoding.secret_keys_equal_loop.body, global_simps]
    simp only at hi hd
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have e3 : i3 = i1 ^^^ i2 := (UScalar.eq_equiv _ _).2 i3_post
      have e1 : diff1 = diff ||| i3 := (UScalar.eq_equiv _ _).2 diff1_post
      have hi64 : i.val < 64 := by scalar_tac
      have hai : (↑a : List U8)[i.val]! = i1 := by
        rw [i1_post]; exact getElem!_eq _ _ (by simp; omega)
      have hbi : (↑b : List U8)[i.val]! = i2 := by
        rw [i2_post]; exact getElem!_eq _ _ (by simp; omega)
      rw [e1, e3, or_xor_zero, hd, i4_post, ← hai, ← hbi]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h1 j hj
        · exact h2
      · intro h
        exact ⟨fun j hj => h j (by omega), h i.val (by omega)⟩
    · have h64 : i.val = 64 := by scalar_tac
      rw [hd, h64]
      constructor
      · intro h
        apply Aeneas.Std.Array.ext
        apply List.ext_getElem (by simp)
        intro j hj _
        have := h j (by simpa using hj)
        rwa [getElem!_eq _ _ hj, getElem!_eq _ _ (by simpa using hj)] at this
      · rintro rfl j _; rfl
  · exact ⟨hi, hd⟩

@[step]
theorem secret_keys_equal_spec (a b : Array U8 64#usize) :
    encoding.secret_keys_equal a b ⦃ r => r = decide (a = b) ⦄ := by
  unfold encoding.secret_keys_equal
  let* ⟨ diff, h ⟩ ← secret_keys_equal_loop_spec a b 0#u8 0#usize (by simp) (by simp)
  simp [h]

@[step]
theorem pkcs8_encode_spec (sk : Array U8 64#usize) (out : Array U8 84#usize) :
    encoding.pkcs8_encode sk out ⦃ r => r.val = encoding.PKCS8_PREFIX.val ++ sk.val ⦄ := by
  unfold encoding.pkcs8_encode
  simp only [global_simps]
  step*
  have h1 : (index_mut_back s2).val = encoding.PKCS8_PREFIX.val ++ out.val.drop 20 := by
    rw [s_post2, s2_post, s1_post]
    simp [List.setSlice!, encoding.PKCS8_PREFIX]
  rw [s3_post2, s5_post, s4_post, h1]
  simp [List.setSlice!, encoding.PKCS8_PREFIX]

/-- A list of length `n` agreeing with `P` (of length `n`) below `n` is `P`. -/
theorem take_eq_of_getElem! (l P : List U8) (n : Nat) (hP : P.length = n) (hl : n ≤ l.length)
    (h : ∀ j < n, l[j]! = P[j]!) : l.take n = P := by
  apply List.ext_getElem (by simp; omega)
  intro j hj hj'
  have := h j (by omega)
  rw [getElem!_eq _ _ (by omega), getElem!_eq _ _ (by omega)] at this
  simpa using this

theorem pkcs8_decode_loop_spec (der : Slice U8) (sk : Array U8 64#usize) (i : Usize)
    (hl : der.length = 84) (hi : i.val ≤ 20)
    (hp : ∀ j < i.val, der.val[j]! = encoding.PKCS8_PREFIX.val[j]!) :
    encoding.pkcs8_decode_loop der sk i ⦃ r =>
      (r.1 = true → der.val = encoding.PKCS8_PREFIX.val ++ r.2.val) ∧
      (r.1 = false → r.2 = sk ∧
        ∀ key : Array U8 64#usize, der.val ≠ encoding.PKCS8_PREFIX.val ++ key.val) ⦄ := by
  unfold encoding.pkcs8_decode_loop
  have hP : encoding.PKCS8_PREFIX.val.length = 20 := by simp
  apply loop.spec_decr_nat (measure := fun (p : Usize) => 20 - p.val)
    (inv := fun p => p.val ≤ 20 ∧ ∀ j < p.val, der.val[j]! = encoding.PKCS8_PREFIX.val[j]!)
  · rintro i ⟨hi, hp⟩
    simp only [encoding.pkcs8_decode_loop.body, params.PKCS8_BYTES]
    step*
    · have hne : i1 ≠ i2 := by simpa using ‹(i1 != i2) = true›
      refine ⟨by simp, fun _ key h => hne ?_⟩
      have hi20 : i.val < 20 := by scalar_tac
      rw [i1_post, i2_post]
      simp only [h]
      rw [List.getElem_append_left]
    · have heq : i1 = i2 := (UScalar.eq_equiv _ _).2 (by simpa using ‹¬(i1 != i2) = true›)
      have hi20 : i.val < 20 := by scalar_tac
      refine ⟨by scalar_tac, fun j hj => ?_, by scalar_tac⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (i3_post ▸ hj) with hj | rfl
      · exact hp j hj
      · rw [getElem!_eq _ _ (by scalar_tac), getElem!_eq _ _ (by omega), ← i1_post, heq, i2_post]
    · have hi20 : i.val = 20 := by scalar_tac
      have ht := take_eq_of_getElem! der.val _ 20 hP (by scalar_tac) (fun j hj => hp j (by omega))
      refine ⟨fun _ => ?_, by simp⟩
      rw [to_slice_mut_back_post, s2_post, Array.from_slice_val _ _ (by scalar_tac), s1_post]
      conv_lhs => rw [← List.take_append_drop 20 der.val]
      rw [ht]
      simp [List.slice]
      scalar_tac
  · exact ⟨hi, hp⟩

@[step]
theorem pkcs8_decode_spec (der : Slice U8) (sk : Array U8 64#usize) :
    encoding.pkcs8_decode der sk ⦃ r =>
      (r.1 = true → der.val = encoding.PKCS8_PREFIX.val ++ r.2.val) ∧
      (r.1 = false → r.2 = sk ∧
        ∀ key : Array U8 64#usize, der.val ≠ encoding.PKCS8_PREFIX.val ++ key.val) ⦄ := by
  unfold encoding.pkcs8_decode
  simp only [params.PKCS8_BYTES]
  split
  · rename_i h
    have h : der.length ≠ 84 := by simpa [UScalar.eq_equiv] using h
    simp only [WP.spec_ok]
    refine ⟨by simp, fun _ => ⟨by simp, fun key hk => h ?_⟩⟩
    simp [Slice.length, hk]
  · rename_i h
    have h : der.length = 84 := by simpa [UScalar.eq_equiv] using h
    exact pkcs8_decode_loop_spec der sk 0#usize h (by simp) (by simp)

@[step]
theorem spki_encode_spec (pk : Array U8 32#usize) :
    encoding.spki_encode pk ⦃ r => r.val = encoding.SPKI_PREFIX.val ++ pk.val ⦄ := by
  unfold encoding.spki_encode
  simp only [global_simps]
  step*
  have h1 : (index_mut_back s2).val = encoding.SPKI_PREFIX.val ++ List.replicate 32 0#u8 := by
    rw [s_post2, s2_post, s1_post]
    simp [List.setSlice!, encoding.SPKI_PREFIX]
  rw [s3_post2, s5_post, s4_post, h1]
  simp [List.setSlice!, encoding.SPKI_PREFIX]

theorem spki_decode_loop_spec (der : Slice U8) (i : Usize)
    (hl : der.length = 50) (hi : i.val ≤ 18)
    (hp : ∀ j < i.val, der.val[j]! = encoding.SPKI_PREFIX.val[j]!) :
    encoding.spki_decode_loop der i ⦃ r =>
      (∀ key, r = some key → der.val = encoding.SPKI_PREFIX.val ++ key.val) ∧
      (r = none → ∀ key : Array U8 32#usize, der.val ≠ encoding.SPKI_PREFIX.val ++ key.val) ⦄ := by
  unfold encoding.spki_decode_loop
  have hP : encoding.SPKI_PREFIX.val.length = 18 := by simp
  apply loop.spec_decr_nat (measure := fun (p : Usize) => 18 - p.val)
    (inv := fun p => p.val ≤ 18 ∧ ∀ j < p.val, der.val[j]! = encoding.SPKI_PREFIX.val[j]!)
  · rintro i ⟨hi, hp⟩
    simp only [encoding.spki_decode_loop.body, params.SPKI_BYTES]
    step*
    · have hne : i1 ≠ i2 := by simpa using ‹(i1 != i2) = true›
      refine ⟨by simp, fun _ key h => hne ?_⟩
      have hi18 : i.val < 18 := by scalar_tac
      rw [i1_post, i2_post]
      simp only [h]
      rw [List.getElem_append_left]
    · have heq : i1 = i2 := (UScalar.eq_equiv _ _).2 (by simpa using ‹¬(i1 != i2) = true›)
      have hi18 : i.val < 18 := by scalar_tac
      refine ⟨by scalar_tac, fun j hj => ?_, by scalar_tac⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (i3_post ▸ hj) with hj | rfl
      · exact hp j hj
      · rw [getElem!_eq _ _ (by scalar_tac), getElem!_eq _ _ (by omega), ← i1_post, heq, i2_post]
    · have hi18 : i.val = 18 := by scalar_tac
      have ht := take_eq_of_getElem! der.val _ 18 hP (by scalar_tac) (fun j hj => hp j (by omega))
      refine ⟨fun key hk => ?_, by simp⟩
      simp only [Option.some.injEq] at hk
      subst hk
      rw [to_slice_mut_back_post, s2_post, Array.from_slice_val _ _ (by scalar_tac), s1_post]
      conv_lhs => rw [← List.take_append_drop 18 der.val]
      rw [ht]
      simp [List.slice]
      scalar_tac
  · exact ⟨hi, hp⟩

@[step]
theorem spki_decode_spec (der : Slice U8) :
    encoding.spki_decode der ⦃ r =>
      (∀ key, r = some key → der.val = encoding.SPKI_PREFIX.val ++ key.val) ∧
      (r = none → ∀ key : Array U8 32#usize, der.val ≠ encoding.SPKI_PREFIX.val ++ key.val) ⦄ := by
  unfold encoding.spki_decode
  simp only [params.SPKI_BYTES]
  split
  · rename_i h
    have h : der.length ≠ 50 := by simpa [UScalar.eq_equiv] using h
    simp only [WP.spec_ok]
    refine ⟨by simp, fun _ key hk => h ?_⟩
    simp [Slice.length, hk]
  · rename_i h
    have h : der.length = 50 := by simpa [UScalar.eq_equiv] using h
    exact spki_decode_loop_spec der 0#usize h (by simp) (by simp)

end slhdsa
