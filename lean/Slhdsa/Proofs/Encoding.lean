import Slhdsa.Proofs.Params
open Aeneas Aeneas.Std Result

/-! The crate's byte encodings, module `encoding`, generic in the key length and the DER
prefix: what a caller's bytes are accepted as, and `prefix ‖ key` with its exact decoder. The
per-set wrappers, with their literal prefixes, are in `Sets.lean`. -/

namespace slhdsa

@[step]
theorem enc_secret_key_from_spec (b sk : Slice U8) :
    encoding.secret_key_from b sk ⦃ r =>
      r.1 = decide (b.length = sk.length) ∧ (r.1 = true → r.2.val = b.val) ∧ (r.1 = false → r.2 = sk) ⦄ := by
  unfold encoding.secret_key_from
  step*
  all_goals done

@[step]
theorem enc_public_key_from_spec (b pk : Slice U8) :
    encoding.public_key_from b pk ⦃ r =>
      r.1 = decide (b.length = pk.length) ∧ (r.1 = true → r.2.val = b.val) ∧ (r.1 = false → r.2 = pk) ⦄ := by
  unfold encoding.public_key_from
  step*
  all_goals done

@[step]
theorem enc_signature_len_ok_spec (p : params.Params) (hv : (paramsS p).Valid) (b : Slice U8) :
    encoding.signature_len_ok p b ⦃ r => r = decide (b.length = (paramsS p).sigBytes) ⦄ := by
  unfold encoding.signature_len_ok
  step*

theorem or_xor_zero (d x y : U8) : (d ||| (x ^^^ y)) = 0#u8 ↔ d = 0#u8 ∧ x = y := by
  rw [UScalar.eq_equiv_bv_eq, UScalar.eq_equiv_bv_eq d, UScalar.eq_equiv_bv_eq x,
    UScalar.bv_or, UScalar.bv_xor]
  simp [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]

theorem secret_keys_equal_loop_spec (a b : Slice U8) (hab : a.length = b.length) (diff : U8) (i : Usize)
    (hi : i.val ≤ a.length) (hd : diff = 0#u8 ↔ ∀ j < i.val, a.val[j]! = b.val[j]!) :
    encoding.secret_keys_equal_loop a b diff i ⦃ r => r = 0#u8 ↔ a.val = b.val ⦄ := by
  unfold encoding.secret_keys_equal_loop
  apply loop.spec_decr_nat (measure := fun (q : U8 × Usize) => a.length - q.2.val)
    (inv := fun q => q.2.val ≤ a.length ∧ (q.1 = 0#u8 ↔ ∀ j < q.2.val, a.val[j]! = b.val[j]!))
  · rintro ⟨diff, i⟩ ⟨hi, hd⟩
    simp only [encoding.secret_keys_equal_loop.body]
    simp only at hi hd
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have e4 : i4 = i2 ^^^ i3 := (UScalar.eq_equiv _ _).2 i4_post
      have e1 : diff1 = diff ||| i4 := (UScalar.eq_equiv _ _).2 diff1_post
      have hia : i.val < a.length := by scalar_tac
      have hai : (↑a : List U8)[i.val]! = i2 := by
        rw [i2_post]; exact getElem!_eq _ _ (by simp only [Slice.length] at hia; omega)
      have hbi : (↑b : List U8)[i.val]! = i3 := by
        rw [i3_post]; exact getElem!_eq _ _ (by simp only [Slice.length] at hia hab; omega)
      rw [e1, e4, or_xor_zero, hd, i5_post, ← hai, ← hbi]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h1 j hj
        · exact h2
      · intro h
        exact ⟨fun j hj => h j (by omega), h i.val (by omega)⟩
    · have hia : i.val = a.length := by scalar_tac
      rw [hd, hia]
      constructor
      · intro h
        apply List.ext_getElem (by simp only [Slice.length] at hab; omega)
        intro j hj _
        have := h j (by simpa [Slice.length] using hj)
        rwa [getElem!_eq _ _ hj, getElem!_eq _ _ (by simp only [Slice.length] at hab; omega)] at this
      · intro h j _; rw [h]
  · exact ⟨hi, hd⟩

@[step]
theorem enc_secret_keys_equal_spec (a b : Slice U8) (hab : a.length = b.length) :
    encoding.secret_keys_equal a b ⦃ r => r = decide (a.val = b.val) ⦄ := by
  unfold encoding.secret_keys_equal
  let* ⟨ diff, h ⟩ ← secret_keys_equal_loop_spec a b hab 0#u8 0#usize (by simp) (by simp)
  simp [h]

theorem setSlice_mid' {α} (A B C s : List α) (i : Nat) (hi : i = A.length)
    (hs : s.length = B.length) :
    (A ++ B ++ C).setSlice! i s = A ++ s ++ C := by
  subst hi
  simp [List.setSlice!, hs]

theorem setSlice_prefix {α} (X Y s : List α) (hs : s.length = X.length) :
    (X ++ Y).setSlice! 0 s = s ++ Y := by
  have hm : min s.length (X.length + Y.length) = s.length := by omega
  simp [List.setSlice!, hm, List.drop_append, hs]

@[step]
theorem enc_der_encode_spec («prefix» key out : Slice U8)
    (h : out.length = «prefix».length + key.length) :
    encoding.der_encode «prefix» key out ⦃ r => r.val = «prefix».val ++ key.val ⦄ := by
  unfold encoding.der_encode
  step*
  have hl : out.val.length = «prefix».val.length + key.val.length := h
  rw [s2_post2, s3_post, s_post2, s1_post]
  simp only [Slice.setSlice!_val]
  have e1 : out.val.setSlice! 0 «prefix».val = «prefix».val ++ out.val.drop «prefix».val.length := by
    conv_lhs => rw [← List.take_append_drop «prefix».val.length out.val]
    exact setSlice_prefix _ _ _ (by simp; omega)
  rw [e1]
  have : (List.drop «prefix».val.length out.val).length = key.val.length := by simp; omega
  rw [show «prefix».val ++ List.drop «prefix».val.length out.val =
    «prefix».val ++ List.drop «prefix».val.length out.val ++ [] by simp]
  rw [setSlice_mid' _ _ _ _ _ (by simp [Slice.length]) (by simp [this])]
  simp

/-- A list of length `n` agreeing with `P` (of length `n`) below `n` is `P`. -/
theorem take_eq_of_getElem! (l P : List U8) (n : Nat) (hP : P.length = n) (hl : n ≤ l.length)
    (h : ∀ j < n, l[j]! = P[j]!) : l.take n = P := by
  apply List.ext_getElem (by simp; omega)
  intro j hj hj'
  have := h j (by omega)
  rw [getElem!_eq _ _ (by omega), getElem!_eq _ _ (by omega)] at this
  simpa using this

theorem der_decode_loop_spec («prefix» der key : Slice U8) (l i : Usize) (hl : l.val = «prefix».length)
    (hlen : der.length = «prefix».length + key.length) (hi : i.val ≤ l.val)
    (hp : ∀ j < i.val, der.val[j]! = «prefix».val[j]!) :
    encoding.der_decode_loop «prefix» der key l i ⦃ r =>
      (r.1 = true → der.val = «prefix».val ++ r.2.val ∧ r.2.length = key.length) ∧
      (r.1 = false → r.2 = key ∧
        ∀ k : List U8, k.length = key.length → der.val ≠ «prefix».val ++ k) ⦄ := by
  unfold encoding.der_decode_loop
  apply loop.spec_decr_nat (measure := fun (q : Usize) => l.val - q.val)
    (inv := fun q => q.val ≤ l.val ∧ ∀ j < q.val, der.val[j]! = «prefix».val[j]!)
  · rintro i ⟨hi, hp⟩
    simp only [encoding.der_decode_loop.body]
    simp only [Slice.length] at hl hlen
    step*
    · have hne : i1 ≠ i2 := by simpa using ‹(i1 != i2) = true›
      refine ⟨by simp, fun _ k _ h => hne ?_⟩
      have hil : i.val < «prefix».val.length := by scalar_tac
      rw [i1_post, i2_post]
      simp only [h]
      rw [List.getElem_append_left]
    · have heq : i1 = i2 := (UScalar.eq_equiv _ _).2 (by simpa using ‹¬(i1 != i2) = true›)
      refine ⟨by scalar_tac, fun j hj => ?_, by scalar_tac⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (i3_post ▸ hj) with hj | rfl
      · exact hp j hj
      · rw [getElem!_eq _ _ (by scalar_tac), getElem!_eq _ _ (by scalar_tac), ← i1_post, heq, i2_post]
    · simp only [Slice.length, s_post, List.slice]; simp; omega
    · have hil : i.val = l.val := by scalar_tac
      have ht := take_eq_of_getElem! der.val _ «prefix».val.length rfl (by omega)
        (fun j hj => hp j (by omega))
      refine ⟨fun _ => ⟨?_, ?_⟩, by simp⟩
      · rw [key1_post, s_post]
        conv_lhs => rw [← List.take_append_drop «prefix».val.length der.val]
        rw [ht]
        simp [List.slice, hl]
      · rw [key1_post]; simp [Slice.length, s_post, List.slice]; omega
  · exact ⟨hi, hp⟩

@[step]
theorem enc_der_decode_spec («prefix» der key : Slice U8)
    (hpk : «prefix».length + key.length ≤ Usize.max) :
    encoding.der_decode «prefix» der key ⦃ r =>
      (r.1 = true → der.val = «prefix».val ++ r.2.val ∧ r.2.length = key.length) ∧
      (r.1 = false → r.2 = key ∧
        ∀ k : List U8, k.length = key.length → der.val ≠ «prefix».val ++ k) ⦄ := by
  unfold encoding.der_decode
  step*
  exact der_decode_loop_spec «prefix» der key _ 0#usize (by simp [Slice.length])
    (by simp [UScalar.eq_equiv] at *; scalar_tac) (by simp) (by simp)

end slhdsa
