import Slhdsa.Proofs.Params
open Aeneas Aeneas.Std Result

/-! Byte-string helpers: `block`, `toInt`, `base_2^b`. -/

namespace slhdsa

/-- Appending a slice of bytes to a vector of bytes. -/
@[local step]
theorem util_extend_from_slice_u8_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r =>
      r.val = v.val ++ s.val ∧ r.length = v.length + s.length ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply WP.spec_bind (List.clone_spec (by intros; simp [liftFun1]))
  intro l hl
  simp [hl]

@[step]
theorem block_spec (N : Usize) (s : Slice U8) (i : Usize) (h : (i.val + 1) * N.val ≤ s.length) :
    util.block N s i ⦃ r => r.val = (s.val.drop (i.val * N.val)).take N.val ⦄ := by
  unfold util.block
  have hmul : (i.val + 1) * N.val = i.val * N.val + N.val := by
    rw [Nat.add_mul, Nat.one_mul]
  have hs : s.length ≤ Usize.max := by scalar_tac
  step*
  · simp only [Slice.length, s1_post, Array.repeat_val, List.length_replicate]; scalar_tac
  · have hv : (Array.from_slice (Array.repeat N 0#u8) s2).val = s2.val :=
      Array.from_slice_val _ _ (by scalar_tac)
    simp only [to_slice_mut_back_post, s3_post, hv, s2_post, i2_post, i1_post]
    simp [List.slice]

/-- `block_spec` in the specification's terms. -/
theorem bytes_block (p : Spec.Params) (s r : List U8) (i : Nat)
    (h : r = (s.drop (i * p.n)).take p.n) :
    bytes r = Spec.block p (bytes s) i := by
  subst h
  simp [Spec.block]

theorem bytes_inj (l l' : List U8) : bytes l = bytes l' ↔ l = l' := by
  constructor
  · intro h
    apply List.map_injective_iff.2 _ h
    intro a b hab
    exact U8.bv_eq_imp_eq _ _ hab
  · rintro rfl; rfl

theorem bytes_eq_loop_spec (x y : Slice U8) (hlen : x.length = y.length) :
    util.bytes_eq_loop x y 0#u8 0#usize ⦃ r => (r = 0#u8 ↔ x.val = y.val) ⦄ := by
  unfold util.bytes_eq_loop
  apply loop.spec_decr_nat (measure := fun (p : U8 × Usize) => x.length - p.2.val)
    (inv := fun p => p.2.val ≤ x.length ∧
      (p.1.bv = 0#8 ↔ x.val.take p.2.val = y.val.take p.2.val))
  · rintro ⟨diff, i⟩ ⟨hi, hinv⟩
    simp only [util.bytes_eq_loop.body]
    simp only at hi hinv
    step*
    · have hx : i.val < x.val.length := by scalar_tac
      have hy : i.val < y.val.length := by scalar_tac
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have hd : diff1.bv = diff.bv ||| ((x.val)[i.val].bv ^^^ (y.val)[i.val].bv) := by
        simp [diff1_post1, i4_post1, i2_post, i3_post]
      rw [hd, i5_post, List.take_succ_eq_append_getElem hx, List.take_succ_eq_append_getElem hy,
        BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, hinv]
      constructor
      · rintro ⟨h1, h2⟩
        rw [h1, U8.bv_eq_imp_eq _ _ h2]
      · intro h
        have h' := List.append_inj h (by simp; omega)
        exact ⟨h'.1, by simpa using congrArg UScalar.bv (List.singleton_inj.1 h'.2)⟩
    · have h1 : x.val.take i.val = x.val := List.take_of_length_le (by scalar_tac)
      have h2 : y.val.take i.val = y.val := List.take_of_length_le (by scalar_tac)
      rw [h1, h2] at hinv
      rw [← hinv]
      constructor
      · rintro rfl; rfl
      · intro h; exact U8.bv_eq_imp_eq _ _ h
  · exact ⟨by scalar_tac, by simp⟩

@[step]
theorem bytes_eq_spec (x y : Slice U8) :
    util.bytes_eq x y ⦃ r => r = (bytes x.val == bytes y.val) ⦄ := by
  unfold util.bytes_eq
  by_cases hlen : x.length = y.length
  · have hl := bytes_eq_loop_spec x y hlen
    have hne : ¬ (Slice.len x != Slice.len y) = true := by
      simp; scalar_tac
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    step with hl
    by_cases hxy : x.val = y.val
    · simp [diff_post.2 hxy, hxy]
    · have h1 : ¬ diff = 0#u8 := fun h => hxy (diff_post.1 h)
      have h2 : ¬ bytes x.val = bytes y.val := fun h => hxy ((bytes_inj _ _).1 h)
      simp [h1, h2]
  · have hne : (Slice.len x != Slice.len y) = true := by
      simp; scalar_tac
    simp only [hne, ↓reduceIte]
    have h2 : ¬ bytes x.val = bytes y.val := fun h => hlen (by
      have := congrArg List.length h
      simpa using this)
    simp [h2]

theorem toInt_snoc (l : Spec.Bytes) (b : Spec.Byte) :
    Spec.toInt (l ++ [b]) = 256 * Spec.toInt l + b.toNat := by
  simp [Spec.toInt, List.foldl_append]

theorem shl8_or_eq (t : BitVec 64) (b : BitVec 8) (ht : t.toNat < 2 ^ 56) :
    (t <<< 8 ||| BitVec.setWidth 64 b).toNat = 256 * t.toNat + b.toNat := by
  have h1 : t <<< 8 ||| BitVec.setWidth 64 b = t * 256#64 + BitVec.setWidth 64 b := by
    have h : t * 256#64 = t <<< 8 := by
      rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl
    rw [h, BitVec.add_eq_or_of_and_eq_zero]
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getElem_zero]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [BitVec.getLsbD_of_ge b i (by omega)]
  rw [h1]
  have hb := b.isLt
  simp [BitVec.toNat_add, BitVec.toNat_mul]
  omega

theorem to_int_loop_spec (x : Slice U8) (total : U64) (i : Usize) (h : x.length ≤ 8)
    (hi : i.val ≤ x.length) (ht : total.val < 2 ^ (8 * i.val))
    (hinv : total.val = Spec.toInt (bytes (x.val.take i.val))) :
    util.to_int_loop x total i ⦃ r => r.val = Spec.toInt (bytes x.val) ⦄ := by
  unfold util.to_int_loop
  apply loop.spec_decr_nat (measure := fun (p : U64 × Usize) => x.length - p.2.val)
    (inv := fun p => p.2.val ≤ x.length ∧ p.1.val < 2 ^ (8 * p.2.val) ∧
      p.1.val = Spec.toInt (bytes (x.val.take p.2.val)))
  · rintro ⟨total, i⟩ ⟨hi, ht, hinv⟩
    simp only [util.to_int_loop.body]
    simp only at hi ht hinv
    step*
    · have hlt : i.val < x.val.length := by scalar_tac
      have hi7 : i.val ≤ 7 := by scalar_tac
      have hp : 2 ^ (8 * i.val) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by omega) (by omega)
      have htt : total.bv.toNat < 2 ^ 56 := by simp; omega
      have key : total1.val = 256 * total.val + ((x.val)[i.val]).val := by
        have e1 := shl8_or_eq total.bv ((x.val)[i.val]).bv htt
        have h2 : total1.bv = total.bv <<< 8 ||| BitVec.setWidth 64 ((x.val)[i.val]).bv := by
          simp [total1_post1, i2_post1, i4_post, i3_post]
        rw [← h2] at e1
        simpa using e1
      have hb : ((x.val)[i.val]).val < 256 := by scalar_tac
      have hp2 : 2 ^ (8 * (i.val + 1)) = 256 * 2 ^ (8 * i.val) := by
        rw [Nat.mul_add, Nat.pow_add]; omega
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [i5_post, hp2]; omega
      · rw [i5_post, List.take_succ_eq_append_getElem hlt, bytes_append, bytes_cons, bytes_nil,
          toInt_snoc, key, hinv]
        simp
    · have : x.val.take i.val = x.val := List.take_of_length_le (by scalar_tac)
      rw [hinv, this]
  · exact ⟨hi, ht, hinv⟩

@[step]
theorem to_int_spec (x : Slice U8) (h : x.length ≤ 8) :
    util.to_int x ⦃ r => r.val = Spec.toInt (bytes x.val) ⦄ := by
  unfold util.to_int
  apply to_int_loop_spec x _ _ h
  · scalar_tac
  · simp
  · simp [Spec.toInt]

theorem fill_step (xs : Spec.Bytes) (b inp bits T : Nat) (h : bits < b) :
    Spec.base2bFill xs b inp bits T =
      Spec.base2bFill xs b (inp + 1) (bits + 8) ((T <<< 8) + xs[inp]!.toNat) := by
  conv_lhs => rw [Spec.base2bFill]
  simp [h]

theorem fill_done (xs : Spec.Bytes) (b inp bits T : Nat) (h : ¬ bits < b) :
    Spec.base2bFill xs b inp bits T = (inp, bits, T) := by
  rw [Spec.base2bFill]
  simp [h]

theorem go_succ (xs : Spec.Bytes) (b n inp bits T inp' bits' T' : Nat)
    (hf : Spec.base2bFill xs b inp bits T = (inp', bits', T')) :
    Spec.base2bGo xs b (n + 1) inp bits T =
      (T' >>> (bits' - b)) % 2 ^ b :: Spec.base2bGo xs b n inp' (bits' - b) T' := by
  simp [Spec.base2bGo, hf]

theorem digit_eq (T s b t : Nat) (ht : t = T % 2 ^ 32) (hs : s + b ≤ 32) :
    (t >>> s) &&& (2 ^ b - 1) = (T >>> s) % 2 ^ b := by
  subst ht
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h32 : 2 ^ 32 = 2 ^ s * 2 ^ (32 - s) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h32, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))

theorem shl8_or_eq32 (t : BitVec 32) (b : BitVec 8) (T : Nat) (ht : t.toNat = T % 2 ^ 32) :
    (t <<< 8 ||| BitVec.setWidth 32 b).toNat = ((T <<< 8) + b.toNat) % 2 ^ 32 := by
  have h1 : t <<< 8 ||| BitVec.setWidth 32 b = t * 256#32 + BitVec.setWidth 32 b := by
    have h : t * 256#32 = t <<< 8 := by
      rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl
    rw [h, BitVec.add_eq_or_of_and_eq_zero]
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getElem_zero]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [BitVec.getLsbD_of_ge b i (by omega)]
  rw [h1, Nat.shiftLeft_eq]
  have hb := b.isLt
  simp [BitVec.toNat_add, BitVec.toNat_mul, ht]

theorem base_2b_inner_spec (x : Slice U8) (b : U32) (input : Usize) (bits total : U32)
    (T c : Nat) (hb : 1 ≤ b.val ∧ b.val ≤ 16) (hbits : bits.val < b.val + 8)
    (ht : total.val = T % 2 ^ 32) (hc : 8 * input.val = c + bits.val)
    (hroom : c + b.val ≤ 8 * x.length) :
    util.base_2b_loop0_loop0 x b input bits total ⦃ r => ∃ T',
      Spec.base2bFill (bytes x.val) b.val input.val bits.val T = (r.1.val, r.2.1.val, T') ∧
      r.2.2.val = T' % 2 ^ 32 ∧ 8 * r.1.val = c + r.2.1.val ∧
      b.val ≤ r.2.1.val ∧ r.2.1.val < b.val + 8 ⦄ := by
  unfold util.base_2b_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (p : Usize × U32 × U32) => b.val - p.2.1.val)
    (inv := fun p => ∃ T',
      Spec.base2bFill (bytes x.val) b.val input.val bits.val T =
        Spec.base2bFill (bytes x.val) b.val p.1.val p.2.1.val T' ∧
      p.2.2.val = T' % 2 ^ 32 ∧ 8 * p.1.val = c + p.2.1.val ∧ p.2.1.val < b.val + 8)
  · rintro ⟨input, bits, total⟩ ⟨T', hf, ht, hc, hbits⟩
    simp only [util.base_2b_loop0_loop0.body]
    simp only at hf ht hc hbits
    step*
    · have hlt : input.val < x.val.length := by scalar_tac
      have hbl : bits.val < b.val := by scalar_tac
      refine ⟨⟨(T' <<< 8) + ((x.val)[input.val]).bv.toNat, ?_, ?_, by scalar_tac, by scalar_tac⟩,
        by scalar_tac⟩
      · rw [hf, fill_step _ _ _ _ _ hbl, bytes_getElem! _ _ hlt, input1_post, bits1_post]
      · have e1 := shl8_or_eq32 total.bv ((x.val)[input.val]).bv T' (by simpa using ht)
        have h2 : total1.bv = total.bv <<< 8 ||| BitVec.setWidth 32 ((x.val)[input.val]).bv := by
          simp [total1_post1, i_post1, i2_post, i1_post]
        rw [← h2] at e1
        simpa using e1
    · have hbl : ¬ bits.val < b.val := by scalar_tac
      exact ⟨T', by rw [hf, fill_done _ _ _ _ _ hbl], ht, hc, by scalar_tac, hbits⟩
  · exact ⟨T, rfl, ht, hc, hbits⟩

theorem base_2b_loop_spec (x : Slice U8) (b : U32) (out_len input : Usize) (bits total : U32)
    (out : alloc.vec.Vec U32) (i : Usize) (T : Nat)
    (hb : 1 ≤ b.val ∧ b.val ≤ 16) (hx : out_len.val * b.val ≤ 8 * x.length)
    (ht : total.val = T % 2 ^ 32) (hc : 8 * input.val = i.val * b.val + bits.val)
    (hbits : bits.val ≤ 7) (hi : i.val ≤ out_len.val) (hlen : out.length = i.val)
    (hbound : ∀ d ∈ out.val, d.val < 2 ^ b.val) :
    util.base_2b_loop0 x b out_len input bits total out i ⦃ r =>
      nats r.val = nats out.val ++
        Spec.base2bGo (bytes x.val) b.val (out_len.val - i.val) input.val bits.val T ∧
      r.length = out_len.val ∧ ∀ d ∈ r.val, d.val < 2 ^ b.val ⦄ := by
  unfold util.base_2b_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : Usize × U32 × U32 × alloc.vec.Vec U32 × Usize) => out_len.val - p.2.2.2.2.val)
    (inv := fun p => ∃ T', p.2.2.1.val = T' % 2 ^ 32 ∧
      8 * p.1.val = p.2.2.2.2.val * b.val + p.2.1.val ∧ p.2.1.val ≤ 7 ∧
      p.2.2.2.2.val ≤ out_len.val ∧ p.2.2.2.1.length = p.2.2.2.2.val ∧
      (∀ d ∈ p.2.2.2.1.val, d.val < 2 ^ b.val) ∧
      nats p.2.2.2.1.val ++
        Spec.base2bGo (bytes x.val) b.val (out_len.val - p.2.2.2.2.val) p.1.val p.2.1.val T' =
      nats out.val ++
        Spec.base2bGo (bytes x.val) b.val (out_len.val - i.val) input.val bits.val T)
  · rintro ⟨input, bits, total, out', i'⟩ ⟨T', ht, hc, hbits, hi, hlen, hbound, hgo⟩
    simp only [util.base_2b_loop0.body]
    simp only at ht hc hbits hi hlen hbound hgo
    spec_split
    · have hroom : i'.val * b.val + b.val ≤ 8 * x.length := by
        have h1 : (i'.val + 1) * b.val ≤ out_len.val * b.val :=
          Nat.mul_le_mul_right _ (by scalar_tac)
        rw [Nat.add_mul] at h1
        omega
      have hin := base_2b_inner_spec x b input bits total T' (i'.val * b.val) hb
        (by scalar_tac) ht hc hroom
      step with hin
      let* ⟨ bits2, bits2_post, bits2_post1 ⟩ ← U32.sub_spec
      let* ⟨ i1, i1_post, i1_post1 ⟩ ← U32.ShiftRight_spec
      let* ⟨ i2, i2_post1, i2_post ⟩ ← U32.ShiftLeft_spec
      have hpow : 2 ^ b.val ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) hb.2
      have hpos : 0 < 2 ^ b.val := Nat.pow_pos (by omega)
      have hi2 : i2.val = 2 ^ b.val := by
        rw [i2_post1, Nat.shiftLeft_eq, Nat.one_mul]
        apply Nat.mod_eq_of_lt
        scalar_tac
      let* ⟨ i3, i3_post, i3_post1 ⟩ ← U32.sub_spec
      let* ⟨ i4, i4_post, i4_post1 ⟩ ← UScalar.and_spec
      let* ⟨ out1, out1_post ⟩ ← alloc.vec.Vec.push_spec
      let* ⟨ i5, i5_post ⟩ ← Usize.add_spec
      have hd : i4.val = (T' >>> bits2.val) % 2 ^ b.val := by
        rw [i4_post, UScalar.val_and, i1_post, i3_post, hi2]
        exact digit_eq T' bits2.val b.val total1.val input1_post1 (by scalar_tac)
      have hn : out_len.val - i'.val = (out_len.val - i5.val) + 1 := by scalar_tac
      have hmul : i5.val * b.val = i'.val * b.val + b.val := by
        rw [i5_post, Nat.add_mul, Nat.one_mul]
      refine ⟨⟨T', input1_post1, by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac, ?_, ?_⟩,
        by scalar_tac⟩
      · intro d hd'
        simp only [out1_post, List.mem_append, List.mem_singleton] at hd'
        rcases hd' with hd' | hd'
        · exact hbound d hd'
        · subst hd'; rw [hd]; exact Nat.mod_lt _ hpos
      · rw [← hgo, hn, go_succ _ _ _ _ _ _ _ _ _ input1_post, out1_post, ← bits2_post, ← hd]
        simp [nats]
    · simp only [step_simps]
      have hn : out_len.val - i'.val = 0 := by scalar_tac
      rw [hn] at hgo
      simp only [Spec.base2bGo, List.append_nil] at hgo
      exact ⟨hgo, by scalar_tac, hbound⟩
  · exact ⟨T, ht, hc, hbits, hi, hlen, hbound, rfl⟩

@[step]
theorem base_2b_spec (x : Slice U8) (b : U32) (out_len : Usize)
    (hb : 1 ≤ b.val ∧ b.val ≤ 16) (hx : out_len.val * b.val ≤ 8 * x.length) :
    util.base_2b x b out_len ⦃ r =>
      nats r.val = Spec.base2b (bytes x.val) b.val out_len.val ∧
      r.length = out_len.val ∧ ∀ d ∈ r.val, d.val < 2 ^ b.val ⦄ := by
  unfold util.base_2b
  have h := base_2b_loop_spec x b out_len 0#usize 0#u32 0#u32 (alloc.vec.Vec.new U32) 0#usize 0
    hb hx (by simp) (by simp) (by simp) (by scalar_tac) (by simp) (by simp)
  simpa [Spec.base2b, nats] using h

end slhdsa
