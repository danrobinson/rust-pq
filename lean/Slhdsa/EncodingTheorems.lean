import Slhdsa.Proofs.Encoding
open Aeneas Aeneas.Std Result

/-!
# Results about the byte encodings (module `encoding`)

For the Rust functions as translated by Aeneas, each statement says that the function returns
(no panic, for every input) and what it returns:

* `secret_key_from` / `public_key_from`: a key holding exactly the given bytes when there are
  64 / 32 of them, nothing otherwise; `signature_len_ok`: whether there are 7856 bytes;
* `secret_keys_equal`: whether the two keys are equal;
* `pkcs8_encode` / `spki_encode`: the fixed prefix of RFC 9909 followed by the key (the
  prefixes are written out as literals, so that they can be read against the RFC);
* `pkcs8_decode` / `spki_decode`: accept exactly the strings `prefix ++ key`, and return that
  key; the PKCS#8 decoder leaves its output buffer unchanged when it rejects;
* corollaries: decoding an encoding gives back the key; two keys with the same encoding are
  equal.

Aeneas translates the `&mut` output parameter of `pkcs8_encode` (`out`) and of `pkcs8_decode`
(`sk`) into an argument (the buffer's previous contents) and a result (its new contents).
-/

namespace slhdsa

/-! ## Raw bytes -/

/-- A private key from its bytes: exactly the 64-byte strings, unchanged. -/
theorem secret_key_from_correct (b : Slice U8) :
    ∃ r, encoding.secret_key_from b = ok r ∧
      r.map (·.val) = if b.length = 64 then some b.val else none :=
  spec_imp_exists (secret_key_from_spec b)

/-- A public key from its bytes: exactly the 32-byte strings, unchanged. -/
theorem public_key_from_correct (b : Slice U8) :
    ∃ r, encoding.public_key_from b = ok r ∧
      r.map (·.val) = if b.length = 32 then some b.val else none :=
  spec_imp_exists (public_key_from_spec b)

theorem signature_len_ok_correct (b : Slice U8) :
    encoding.signature_len_ok b = ok (decide (b.length = 7856)) :=
  signature_len_ok_eq b

theorem secret_keys_equal_correct (a b : Array U8 64#usize) :
    encoding.secret_keys_equal a b = ok (decide (a = b)) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (secret_keys_equal_spec a b)
  rw [h, hr]

/-! ## PKCS#8 (`OneAsymmetricKey`) -/

/-- The encoding is the 20-byte prefix followed by the key, whatever `out` held. -/
theorem pkcs8_encode_correct (sk : Array U8 64#usize) (out : Array U8 84#usize) :
    ∃ der, encoding.pkcs8_encode sk out = ok der ∧
      der.val = [0x30#u8, 0x52#u8, 0x02#u8, 0x01#u8, 0x00#u8, 0x30#u8, 0x0b#u8, 0x06#u8, 0x09#u8,
        0x60#u8, 0x86#u8, 0x48#u8, 0x01#u8, 0x65#u8, 0x03#u8, 0x04#u8, 0x03#u8, 0x14#u8, 0x04#u8,
        0x40#u8] ++ sk.val := by
  rw [← pkcs8_prefix_val]
  exact spec_imp_exists (pkcs8_encode_spec sk out)

/-- The decoder returns `(true, key)` exactly when `der` is the prefix followed by `key`, and
otherwise `(false, sk)`: the buffer is unchanged. -/
theorem pkcs8_decode_correct (der : Slice U8) (sk : Array U8 64#usize) :
    ∃ r, encoding.pkcs8_decode der sk = ok r ∧
      (∀ key : Array U8 64#usize, r = (true, key) ↔
        der.val = [0x30#u8, 0x52#u8, 0x02#u8, 0x01#u8, 0x00#u8, 0x30#u8, 0x0b#u8, 0x06#u8, 0x09#u8,
          0x60#u8, 0x86#u8, 0x48#u8, 0x01#u8, 0x65#u8, 0x03#u8, 0x04#u8, 0x03#u8, 0x14#u8, 0x04#u8,
          0x40#u8] ++ key.val) ∧
      ((¬ ∃ key : Array U8 64#usize,
        der.val = [0x30#u8, 0x52#u8, 0x02#u8, 0x01#u8, 0x00#u8, 0x30#u8, 0x0b#u8, 0x06#u8, 0x09#u8,
          0x60#u8, 0x86#u8, 0x48#u8, 0x01#u8, 0x65#u8, 0x03#u8, 0x04#u8, 0x03#u8, 0x14#u8, 0x04#u8,
          0x40#u8] ++ key.val) → r = (false, sk)) := by
  rw [← pkcs8_prefix_val]
  obtain ⟨⟨b, k⟩, h, h1, h2⟩ := spec_imp_exists (pkcs8_decode_spec der sk)
  refine ⟨(b, k), h, fun key => ⟨?_, fun hk => ?_⟩, fun hn => ?_⟩
  · rintro ⟨rfl, rfl⟩; exact h1 rfl
  · cases b
    · exact ((h2 rfl).2 key hk).elim
    · have e := (h1 rfl).symm.trans hk
      simp only [List.append_cancel_left_eq] at e
      rw [Aeneas.Std.Array.ext _ _ e]
  · cases b
    · have e := (h2 rfl).1
      simp only at e
      rw [e]
    · exact (hn ⟨k, h1 rfl⟩).elim

/-- Decoding an encoding gives back the key (whatever the decoder's buffer held). -/
theorem pkcs8_decode_encode (sk sk' : Array U8 64#usize) (out der : Array U8 84#usize)
    (h : encoding.pkcs8_encode sk out = ok der) :
    encoding.pkcs8_decode der.to_slice sk' = ok (true, sk) := by
  obtain ⟨d, hd, hv⟩ := pkcs8_encode_correct sk out
  have e : d = der := by rw [h] at hd; simpa using hd.symm
  rw [e] at hv
  obtain ⟨r, hr, h1, -⟩ := pkcs8_decode_correct der.to_slice sk'
  rw [hr, (h1 sk).2 (by rw [Array.val_to_slice, hv])]

/-- Two keys with the same encoding are equal. -/
theorem pkcs8_encode_injective (a b : Array U8 64#usize) (out out' der : Array U8 84#usize)
    (ha : encoding.pkcs8_encode a out = ok der) (hb : encoding.pkcs8_encode b out' = ok der) :
    a = b := by
  obtain ⟨d, hd, hv⟩ := pkcs8_encode_correct a out
  obtain ⟨d', hd', hv'⟩ := pkcs8_encode_correct b out'
  have e : d = d' := by rw [ha] at hd; rw [hb] at hd'; rw [hd] at hd'; simpa using hd'
  subst e
  apply Aeneas.Std.Array.ext
  simpa using hv.symm.trans hv'

/-! ## `SubjectPublicKeyInfo` -/

/-- The encoding is the 18-byte prefix followed by the key. -/
theorem spki_encode_correct (pk : Array U8 32#usize) :
    ∃ der, encoding.spki_encode pk = ok der ∧
      der.val = [0x30#u8, 0x30#u8, 0x30#u8, 0x0b#u8, 0x06#u8, 0x09#u8, 0x60#u8, 0x86#u8, 0x48#u8,
        0x01#u8, 0x65#u8, 0x03#u8, 0x04#u8, 0x03#u8, 0x14#u8, 0x03#u8, 0x21#u8, 0x00#u8] ++ pk.val := by
  rw [← spki_prefix_val]
  exact spec_imp_exists (spki_encode_spec pk)

/-- The decoder returns `some key` exactly when `der` is the prefix followed by `key`, and
`none` otherwise. -/
theorem spki_decode_correct (der : Slice U8) :
    ∃ r, encoding.spki_decode der = ok r ∧
      (∀ key : Array U8 32#usize, r = some key ↔
        der.val = [0x30#u8, 0x30#u8, 0x30#u8, 0x0b#u8, 0x06#u8, 0x09#u8, 0x60#u8, 0x86#u8, 0x48#u8,
          0x01#u8, 0x65#u8, 0x03#u8, 0x04#u8, 0x03#u8, 0x14#u8, 0x03#u8, 0x21#u8, 0x00#u8] ++ key.val) ∧
      ((¬ ∃ key : Array U8 32#usize,
        der.val = [0x30#u8, 0x30#u8, 0x30#u8, 0x0b#u8, 0x06#u8, 0x09#u8, 0x60#u8, 0x86#u8, 0x48#u8,
          0x01#u8, 0x65#u8, 0x03#u8, 0x04#u8, 0x03#u8, 0x14#u8, 0x03#u8, 0x21#u8, 0x00#u8] ++ key.val) →
        r = none) := by
  rw [← spki_prefix_val]
  obtain ⟨r, h, h1, h2⟩ := spec_imp_exists (spki_decode_spec der)
  refine ⟨r, h, fun key => ⟨fun hk => h1 key hk, fun hk => ?_⟩, fun hn => ?_⟩
  · cases r with
    | none => exact (h2 rfl key hk).elim
    | some k =>
      have e := (h1 k rfl).symm.trans hk
      simp only [List.append_cancel_left_eq] at e
      rw [Aeneas.Std.Array.ext _ _ e]
  · cases r with
    | none => rfl
    | some k => exact (hn ⟨k, h1 k rfl⟩).elim

/-- Decoding an encoding gives back the key. -/
theorem spki_decode_encode (pk : Array U8 32#usize) (der : Array U8 50#usize)
    (h : encoding.spki_encode pk = ok der) :
    encoding.spki_decode der.to_slice = ok (some pk) := by
  obtain ⟨d, hd, hv⟩ := spki_encode_correct pk
  have e : d = der := by rw [h] at hd; simpa using hd.symm
  rw [e] at hv
  obtain ⟨r, hr, h1, -⟩ := spki_decode_correct der.to_slice
  rw [hr, (h1 pk).2 (by rw [Array.val_to_slice, hv])]

/-- Two keys with the same encoding are equal. -/
theorem spki_encode_injective (a b : Array U8 32#usize) (der : Array U8 50#usize)
    (ha : encoding.spki_encode a = ok der) (hb : encoding.spki_encode b = ok der) : a = b := by
  obtain ⟨d, hd, hv⟩ := spki_encode_correct a
  obtain ⟨d', hd', hv'⟩ := spki_encode_correct b
  have e : d = d' := by rw [ha] at hd; rw [hb] at hd'; rw [hd] at hd'; simpa using hd'
  subst e
  apply Aeneas.Std.Array.ext
  simpa using hv.symm.trans hv'

end slhdsa

#print axioms slhdsa.secret_key_from_correct
#print axioms slhdsa.public_key_from_correct
#print axioms slhdsa.signature_len_ok_correct
#print axioms slhdsa.secret_keys_equal_correct
#print axioms slhdsa.pkcs8_encode_correct
#print axioms slhdsa.pkcs8_decode_correct
#print axioms slhdsa.pkcs8_decode_encode
#print axioms slhdsa.pkcs8_encode_injective
#print axioms slhdsa.spki_encode_correct
#print axioms slhdsa.spki_decode_correct
#print axioms slhdsa.spki_decode_encode
#print axioms slhdsa.spki_encode_injective
