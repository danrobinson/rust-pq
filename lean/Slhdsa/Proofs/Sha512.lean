import Slhdsa.Proofs.Compress512Top
open Aeneas Aeneas.Std Result

/-! SHA-512 and HMAC-SHA-512: the Rust functions compute the specification's
(continuing `Sha512Core.lean`). -/

namespace slhdsa

namespace S512
open Spec.SHA512

attribute [local step] extend_u8_spec

theorem usize_max_le : Usize.max ≤ 18446744073709551615 := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> scalar_tac

/-- Padding of the tail `m` of a message whose first `pre` bytes (a multiple
of 128) have already been compressed. -/
def padFrom (pre : Nat) (m : Spec.Bytes) : Spec.Bytes :=
  m ++ [0x80#8] ++ List.replicate ((239 - m.length % 128) % 128) 0#8 ++
    Spec.toByte (8 * (pre + m.length)) 16

theorem padFrom_zero (m : Spec.Bytes) : padFrom 0 m = pad m := by
  simp [padFrom, pad]

theorem padFrom_length (pre : Nat) (m : Spec.Bytes) : (padFrom pre m).length % 128 = 0 := by
  simp [padFrom, Spec.toByte]
  omega

/-- The hash state after compressing the blocks of `p`, starting from `st`. -/
def hashFrom (st : List Word) (p : Spec.Bytes) : List Word :=
  (List.range (p.length / 128)).foldl (fun st k => compress st (blockAt p k)) st

@[step]
theorem pad_spec (msg : Slice U8) (pre : Usize) (h : pre.val + msg.length + 144 ≤ Usize.max) :
    sha512.pad msg pre ⦃ r => bytes r.val = padFrom pre.val (bytes msg.val) ⦄ := by
  unfold sha512.pad
  step as ⟨p, hp⟩
  step as ⟨p1, hp1⟩
  have hp1l : p1.length = msg.length + 1 := by
    simp [alloc.vec.Vec.length, hp1, hp]
  step with pad_loop0_spec as ⟨p2, hp2⟩
  have hp2l : p2.length = msg.length + 1 + (240 - (msg.length + 1) % 128) % 128 := by
    simp only [alloc.vec.Vec.length] at hp1l ⊢
    simp [hp2, hp1l]
  have hp2v : p2.length ≤ msg.length + 128 := by omega
  have hz : (240 - p1.length % 128) % 128 = (239 - msg.length % 128) % 128 := by omega
  have hval : bytes p2.val = bytes msg.val ++ [0x80#8] ++
      List.replicate ((239 - msg.length % 128) % 128) 0#8 := by
    rw [hp2, hp1, hp, hz]
    simp [bytes]
  clear hp2 hp1 hp hp1l hp2l hz
  have hmax : Usize.max ≤ 18446744073709551615 := usize_max_le
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = pre.val + msg.length := by simp [hi2, hi1]; scalar_tac
  step as ⟨bitlen, hb⟩
  have hbv : bitlen.val = 8 * (pre.val + msg.length) := by scalar_tac
  have hfin := pad_loop1_spec p2 p2 bitlen 0#u32 (by scalar_tac) (by simp) (by simp)
  step with hfin as ⟨r, hr⟩
  simp only [padFrom, bytes_length, hr, hval, hbv]

theorem hashFrom_append128 (st : List Word) (B P : Spec.Bytes) (hB : B.length = 128) :
    hashFrom st (B ++ P) = hashFrom (compress st B) P := by
  have hl : (B ++ P).length / 128 = P.length / 128 + 1 := by simp [hB]
  simp only [hashFrom, hl, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  have h0 : blockAt (B ++ P) 0 = B := by
    simp [blockAt, hB]
  have hk : ∀ k, blockAt (B ++ P) (k + 1) = blockAt P k := by
    intro k
    simp only [blockAt]
    have : 128 * (k + 1) = B.length + 128 * k := by rw [hB]; ring
    rw [this, List.drop_append, List.drop_eq_nil_of_le (by omega)]
    simp
  simp only [h0, hk]

/-- Padding commutes with splitting off a whole first block. -/
theorem padFrom_append128 (pre : Nat) (B m : Spec.Bytes) (hB : B.length = 128) :
    padFrom pre (B ++ m) = B ++ padFrom (pre + 128) m := by
  have e1 : (239 - (128 + m.length) % 128) % 128 = (239 - m.length % 128) % 128 := by omega
  have e2 : 8 * (pre + (128 + m.length)) = 8 * (pre + 128 + m.length) := by ring
  simp [padFrom, hB, e2]

theorem sha512_from_loop0_spec (msg : Slice U8) (pre : Nat) (S0 : List Word)
    (st : Array U64 8#usize) (off : Usize)
    (hmax : msg.length + 128 ≤ Usize.max) (hmod : off.val % 128 = 0) (hle : off.val ≤ msg.length)
    (hinv : hashFrom S0 (padFrom pre (bytes msg.val)) =
      hashFrom (wv st.val) (padFrom (pre + off.val) ((bytes msg.val).drop off.val))) :
    sha512.sha512_from_loop0 msg st off ⦃ r =>
      r.2.val % 128 = 0 ∧ r.2.val ≤ msg.length ∧
      hashFrom S0 (padFrom pre (bytes msg.val)) =
        hashFrom (wv r.1.val) (padFrom (pre + r.2.val) ((bytes msg.val).drop r.2.val)) ⦄ := by
  unfold sha512.sha512_from_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : Array U64 8#usize × Usize) => msg.length - q.2.val)
    (inv := fun q => q.2.val % 128 = 0 ∧ q.2.val ≤ msg.length ∧
      hashFrom S0 (padFrom pre (bytes msg.val)) =
        hashFrom (wv q.1.val) (padFrom (pre + q.2.val) ((bytes msg.val).drop q.2.val)))
  · rintro ⟨st, off⟩ ⟨hmod, hle, hinv⟩
    simp only [sha512.sha512_from_loop0.body]
    simp only at hmod hle hinv
    step*
    · refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have hB : (((bytes msg.val).drop off.val).take 128).length = 128 := by
        simp; scalar_tac
      have hsplit : (bytes msg.val).drop off.val =
          ((bytes msg.val).drop off.val).take 128 ++ (bytes msg.val).drop (off.val + 128) := by
        rw [← List.drop_drop, List.take_append_drop]
      rw [hinv, hsplit, padFrom_append128 _ _ _ hB, hashFrom_append128 _ _ _ hB]
      rw [st1_post, i_post, ← Nat.add_assoc]
  · exact ⟨hmod, hle, hinv⟩

theorem sha512_from_loop1_spec (p : alloc.vec.Vec U8) (S0 : List Word) (state : Array U64 8#usize)
    (off : Usize)
    (hp : p.length % 128 = 0) (hoff : off.val % 128 = 0) (hle : off.val ≤ p.length)
    (hinv : wv state.val = (List.range (off.val / 128)).foldl
      (fun st k => compress st (blockAt (bytes p.val) k)) S0) :
    sha512.sha512_from_loop1 state p off ⦃ r =>
      wv r.val = (List.range (p.length / 128)).foldl
        (fun st k => compress st (blockAt (bytes p.val) k)) S0 ⦄ := by
  unfold sha512.sha512_from_loop1
  apply loop.spec_decr_nat
    (measure := fun (q : Array U64 8#usize × Usize) => p.length - q.2.val)
    (inv := fun q => q.2.val % 128 = 0 ∧ q.2.val ≤ p.length ∧
      wv q.1.val = (List.range (q.2.val / 128)).foldl
        (fun st k => compress st (blockAt (bytes p.val) k)) S0)
  · rintro ⟨state, off⟩ ⟨hoff, hle, hinv⟩
    simp only [sha512.sha512_from_loop1.body]
    simp only at hoff hle hinv
    have h128 : off.val = p.length ∨ off.val + 128 ≤ p.length := by omega
    have hpm : p.length ≤ Usize.max := by scalar_tac
    step*
    · simp [alloc.vec.Vec.deref]; scalar_tac
    · refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have e : o1.val / 128 = off.val / 128 + 1 := by scalar_tac
      rw [e, List.range_succ, List.foldl_append, ← hinv]
      have e2 : 128 * (off.val / 128) = off.val := by omega
      simp [blockAt, alloc.vec.Vec.deref, *]
  · exact ⟨hoff, hle, hinv⟩

theorem take_set8 {α} (l : List α) (i : Nat) (a b c d e f g h : α) (hl : i + 7 < l.length) :
    ((((((((l.set i a).set (i + 1) b).set (i + 2) c).set (i + 3) d).set (i + 4) e).set
      (i + 5) f).set (i + 6) g).set (i + 7) h).take (i + 8) =
      l.take i ++ [a, b, c, d, e, f, g, h] := by
  rw [show i + 8 = i + 7 + 1 from rfl, take_set_succ _ _ _ (by simpa using hl),
    show i + 7 = i + 6 + 1 from rfl, take_set_succ _ _ _ (by simp; omega),
    show i + 6 = i + 5 + 1 from rfl, take_set_succ _ _ _ (by simp; omega),
    show i + 5 = i + 4 + 1 from rfl, take_set_succ _ _ _ (by simp; omega),
    show i + 4 = i + 3 + 1 from rfl, take_set_succ _ _ _ (by simp; omega),
    show i + 3 = i + 2 + 1 from rfl, take_set_succ _ _ _ (by simp; omega),
    show i + 2 = i + 1 + 1 from rfl, take_set_succ _ _ _ (by simp; omega),
    take_set_succ _ _ _ (by omega)]
  simp

/-- Big-endian serialisation of the hash state. -/
def ser (l : List Word) : Spec.Bytes := l.flatMap fun w => Spec.toByte w.toNat 8

theorem digest_loop_spec (state : Array U64 8#usize) (out : Array U8 64#usize) (i : Usize)
    (hi : i.val ≤ 8)
    (hinv : bytes (out.val.take (8 * i.val)) = ser (wv (state.val.take i.val))) :
    sha512.digest_loop state out i ⦃ r => bytes r.val = ser (wv state.val) ⦄ := by
  unfold sha512.digest_loop
  apply loop.spec_decr_nat
    (measure := fun (q : Array U8 64#usize × Usize) => 8 - q.2.val)
    (inv := fun q => q.2.val ≤ 8 ∧
      bytes (q.1.val.take (8 * q.2.val)) = ser (wv (state.val.take q.2.val)))
  · rintro ⟨out, i⟩ ⟨hi, hinv⟩
    simp only [sha512.digest_loop.body]
    simp only at hi hinv
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have hl : out.val.length = 64 := by scalar_tac
      have hs : state.val.length = 8 := by scalar_tac
      have e : 8 * i24.val = 8 * i.val + 8 := by scalar_tac
      rw [e, i24_post, a_post, out7_post, out6_post, out5_post, out4_post, out3_post, out2_post,
        out1_post]
      simp only [Array.set_val_eq, i22_post, i20_post, i17_post, i14_post, i11_post, i8_post,
        i5_post, i2_post]
      rw [take_set8 _ _ _ _ _ _ _ _ _ _ (by scalar_tac)]
      rw [List.take_succ_eq_append_getElem (by scalar_tac)]
      simp only [bytes_append, hinv, wv, ser, List.map_append, List.flatMap_append,
        List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        toByte8]
      simp [bytes, *]
    · have h8 : i.val = 8 := by scalar_tac
      have h1 : out.val.length = 64 := by scalar_tac
      have h2 : state.val.length = 8 := by scalar_tac
      rw [h8, List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hinv
      exact hinv
  · exact ⟨hi, hinv⟩

@[step]
theorem digest_spec (state : Array U64 8#usize) :
    sha512.digest state ⦃ r => bytes r.val = ser (wv state.val) ⦄ := by
  unfold sha512.digest
  apply digest_loop_spec
  · simp
  · simp [ser, wv]

@[step]
theorem sha512_from_spec (state : Array U64 8#usize) (pre : Usize) (msg : Slice U8)
    (h : pre.val + msg.length + 144 ≤ Usize.max) :
    sha512.sha512_from state pre msg ⦃ r =>
      bytes r.val = ser (hashFrom (wv state.val) (padFrom pre.val (bytes msg.val))) ⦄ := by
  unfold sha512.sha512_from
  step with sha512_from_loop0_spec msg pre.val (wv state.val) state 0#usize
    (by scalar_tac) (by simp) (by simp) (by simp) as ⟨st, off, hmod, hle, hinv⟩
  step as ⟨s, hs⟩
  step as ⟨i1, hi1⟩
  have hsv : bytes s.val = (bytes msg.val).drop off.val := by
    simp [hs, List.slice]
  have hsl : s.length = msg.length - off.val := by
    simp [Slice.length, hs, List.slice]
  step as ⟨p, hp⟩
  have hpl : p.length % 128 = 0 := by
    have := padFrom_length i1.val (bytes s.val)
    rw [← hp] at this
    simpa [alloc.vec.Vec.length] using this
  step with sha512_from_loop1_spec p (wv st.val) as ⟨st1, hst⟩
  · simp
  step as ⟨r, hr⟩
  rw [hr, hst, hinv, hashFrom, ← hsv, ← hi1, ← hp]
  simp [alloc.vec.Vec.length]

theorem sha512_spec (msg : Slice U8) (h : msg.length + 144 ≤ Usize.max) :
    sha512.sha512 msg ⦃ r => bytes r.val = Spec.sha512 (bytes msg.val) ⦄ := by
  unfold sha512.sha512
  step with sha512_from_spec as ⟨r, hr⟩
  rw [hr, H0_eq, padFrom_zero]
  simp only [ser, hashFrom, Spec.SHA512.sha512]

theorem hmac_sha512_loop_spec (key : Slice U8) (inner outer : alloc.vec.Vec U8) (i : Usize)
    (K0 : List U8) (hK0 : K0 = key.val ++ List.replicate (128 - key.length) 0#u8)
    (hk : key.length ≤ 128) (hi : i.val ≤ 128)
    (hin : inner.val = (K0.take i.val).map (· ^^^ 54#u8))
    (hout : outer.val = (K0.take i.val).map (· ^^^ 92#u8)) :
    sha512.hmac_sha512_loop key inner outer i ⦃ r =>
      r.1.val = K0.map (· ^^^ 54#u8) ∧ r.2.val = K0.map (· ^^^ 92#u8) ⦄ := by
  have hKl : K0.length = 128 := by simp [hK0]; scalar_tac
  unfold sha512.hmac_sha512_loop
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × alloc.vec.Vec U8 × Usize) => 128 - q.2.2.val)
    (inv := fun q => q.2.2.val ≤ 128 ∧ q.1.val = (K0.take q.2.2.val).map (· ^^^ 54#u8) ∧
      q.2.1.val = (K0.take q.2.2.val).map (· ^^^ 92#u8))
  · rintro ⟨inner, outer, i⟩ ⟨hi, hin, hout⟩
    simp only [sha512.hmac_sha512_loop.body]
    simp only at hi hin hout
    have hil : inner.val.length = i.val := by simp [hin]; omega
    have hol : outer.val.length = i.val := by simp [hout]; omega
    step*
    · have hkk : (if i < key.len then key.index_usize i else ok 0#u8) ⦃ k => k = K0[i.val]! ⦄ := by
        split
        · rename_i hlt
          step as ⟨k, hk'⟩
          have : i.val < key.val.length := by scalar_tac
          rw [hk', hK0]
          simp [List.getElem?_append_left, this]
        · rename_i hlt
          have : key.val.length ≤ i.val := by scalar_tac
          have h2 : i.val - key.val.length < 128 - key.val.length := by scalar_tac
          simp [hK0, List.getElem?_append_right, this, h2]
      step with hkk as ⟨k, hk'⟩
      step*
      have ht : K0.take i4.val = K0.take i.val ++ [k] := by
        have : i.val < K0.length := by scalar_tac
        rw [i4_post, List.take_succ_eq_append_getElem this, hk', getElem!_eq _ _ this]
      have e2 : i2 = k ^^^ 54#u8 := by scalar_tac
      have e3 : i3 = k ^^^ 92#u8 := by scalar_tac
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [ht, inner1_post, hin, e2]; simp
      · rw [ht, outer1_post, hout, e3]; simp
    · have h128 : i.val = 128 := by scalar_tac
      rw [h128, List.take_of_length_le (by omega)] at hin hout
      exact ⟨hin, hout⟩
  · exact ⟨hi, hin, hout⟩

theorem pad_append128 (B m : Spec.Bytes) (hB : B.length = 128) :
    pad (B ++ m) = B ++ padFrom 128 m := by
  simp [pad, padFrom, hB]

/-- SHA-512 of `B ‖ m`, for a 128-byte first block `B`, continues from the
compression of `B`. -/
theorem sha512_prefix128 (B m : Spec.Bytes) (hB : B.length = 128) :
    Spec.sha512 (B ++ m) = ser (hashFrom (compress H0 B) (padFrom 128 m)) := by
  show ser (hashFrom H0 (pad (B ++ m))) = _
  rw [pad_append128 _ _ hB, hashFrom_append128 _ _ _ hB]

end S512

/-- The Rust SHA-512 computes `Spec.sha512`, for every message that fits in memory. -/
@[step]
theorem sha512_spec (msg : Slice U8) (h : msg.length + 144 ≤ Usize.max) :
    sha512.sha512 msg ⦃ r => bytes r.val = Spec.sha512 (bytes msg.val) ⦄ :=
  S512.sha512_spec msg h

/-- The Rust HMAC-SHA-512 computes `Spec.hmacSha512`, for keys of at most one block. -/
@[step]
theorem hmac_sha512_spec (key msg : Slice U8) (hk : key.length ≤ 128)
    (h : msg.length + 272 ≤ Usize.max) :
    sha512.hmac_sha512 key msg ⦃ r => bytes r.val = Spec.hmacSha512 (bytes key.val) (bytes msg.val) ⦄ := by
  unfold sha512.hmac_sha512
  step with S512.hmac_sha512_loop_spec key _ _ _
    (key.val ++ List.replicate (128 - key.length) 0#u8) rfl as ⟨inner, outer, hin, hout⟩
  · simp
  · simp
  have hil : inner.val.length = 128 := by simp [hin]; scalar_tac
  have hol : outer.val.length = 128 := by simp [hout]; scalar_tac
  step with S512.extend_u8_spec as ⟨inner1, hinner1⟩
  step as ⟨ih, hih⟩
  · simp [alloc.vec.Vec.deref, hinner1, hil]; scalar_tac
  step as ⟨s1, s1_post⟩
  step with S512.extend_u8_spec as ⟨outer1, outer1_post⟩
  step as ⟨r, r_post⟩
  · simp [alloc.vec.Vec.deref, *]; scalar_tac
  have hkl : ¬ (bytes key.val).length > 128 := by simp; scalar_tac
  rw [r_post]
  simp only [Spec.hmacSha512, hkl, ↓reduceIte]
  simp only [alloc.vec.Vec.deref] at hih ⊢
  have e1 : (0#u8 ^^^ 92#u8).bv = 92#8 := by decide
  have e2 : (0#u8 ^^^ 54#u8).bv = 54#8 := by decide
  simp [outer1_post, s1_post, hout, hih, hinner1, hin, bytes_map_xor]
  simp [bytes, e1, e2]

end slhdsa
