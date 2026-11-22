import Slhdsa.Proofs.CompressTop
open Aeneas Aeneas.Std Result

/-! The Rust SHA-256 computes `Spec.sha256`. -/

namespace slhdsa
open Spec.SHA256

theorem pad_loop_spec (p0 : alloc.vec.Vec U8) (hlen : p0.length + 64 ≤ Usize.max) :
    sha256.pad_loop p0 ⦃ r =>
      r.val = p0.val ++ List.replicate ((120 - p0.length % 64) % 64) 0#u8 ⦄ := by
  unfold sha256.pad_loop
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec U8) =>
      p0.length + (120 - p0.length % 64) % 64 - p.length)
    (inv := fun p => ∃ j, j ≤ (120 - p0.length % 64) % 64 ∧
      p.val = p0.val ++ List.replicate j 0#u8)
  · rintro p ⟨j, hj, hp⟩
    simp only [sha256.pad_loop.body]
    have hl : p.length = p0.length + j := by
      simp only [alloc.vec.Vec.length, hp, List.length_append, List.length_replicate]
    step*
    · rename_i hne
      have hne' : (p0.length + j) % 64 ≠ 56 := by
        rw [← hl]; simp at hne; scalar_tac
      have hlt : j < (120 - p0.length % 64) % 64 := by omega
      refine ⟨⟨j + 1, by omega, ?_⟩, ?_⟩
      · rw [p1_post, hp, List.replicate_succ']; simp
      · have : p1.length = p.length + 1 := by simp [alloc.vec.Vec.length, p1_post]
        omega
  · exact ⟨0, by omega, by simp⟩

/-- Appending a slice of bytes to a vector. -/
@[local step]
theorem extend_from_slice_u8_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  simp only [alloc.vec.Vec.extend_from_slice, h, ↓reduceDIte]
  have hc : List.clone core.clone.CloneU8.clone s.val ⦃ l' => l'.val = s.val ∧ l'.val.length = s.val.length ⦄ :=
    List.clone_spec (by intro x _; rfl)
  step with hc as ⟨l', h1, h2⟩
  simp [h1]

theorem ofNat_shiftRight {n : Nat} (v : BitVec n) (k : Nat) :
    BitVec.ofNat 8 (v.toNat >>> k) = BitVec.setWidth 8 (v >>> k) := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem ofNat_toNat8 {n : Nat} (v : BitVec n) : BitVec.ofNat 8 v.toNat = BitVec.setWidth 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem toByte8 (v : BitVec 64) : Spec.toByte v.toNat 8 =
    [BitVec.setWidth 8 (v >>> 56), BitVec.setWidth 8 (v >>> 48), BitVec.setWidth 8 (v >>> 40),
      BitVec.setWidth 8 (v >>> 32), BitVec.setWidth 8 (v >>> 24), BitVec.setWidth 8 (v >>> 16),
      BitVec.setWidth 8 (v >>> 8), BitVec.setWidth 8 v] := by
  simp only [Spec.toByte, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.map_cons,
    List.map_nil, ofNat_shiftRight]
  simp

theorem toByte4 (v : BitVec 32) : Spec.toByte v.toNat 4 =
    [BitVec.setWidth 8 (v >>> 24), BitVec.setWidth 8 (v >>> 16), BitVec.setWidth 8 (v >>> 8),
      BitVec.setWidth 8 v] := by
  simp only [Spec.toByte, show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons,
    List.map_nil, ofNat_shiftRight]
  simp

/-- Padding of the tail `m` of a message whose first `pre` bytes (a multiple
of 64) have already been compressed. -/
def padFrom (pre : Nat) (m : Spec.Bytes) : Spec.Bytes :=
  m ++ [0x80#8] ++ List.replicate ((119 - m.length % 64) % 64) 0#8 ++ Spec.toByte (8 * (pre + m.length)) 8

theorem padFrom_zero (m : Spec.Bytes) : padFrom 0 m = pad m := by
  simp [padFrom, pad]

theorem padFrom_length (pre : Nat) (m : Spec.Bytes) : (padFrom pre m).length % 64 = 0 := by
  simp [padFrom, Spec.toByte]
  omega

/-- The hash state after compressing the blocks of `p`, starting from `st`. -/
def hashFrom (st : List Word) (p : Spec.Bytes) : List Word :=
  (List.range (p.length / 64)).foldl (fun st k => compress st (blockAt p k)) st

@[step]
theorem pad_spec (msg : Slice U8) (pre : Usize) (hpre : pre.val % 64 = 0)
    (h : Room (pre.val + msg.length) 72) :
    sha256.pad msg pre ⦃ r => bytes r.val = padFrom pre.val (bytes msg.val) ⦄ := by
  unfold sha256.pad
  obtain ⟨h1, h2⟩ := h
  step as ⟨p, hp⟩
  step as ⟨p1, hp1⟩
  have hp1l : p1.length = msg.length + 1 := by
    simp [alloc.vec.Vec.length, hp1, hp]
  step with pad_loop_spec as ⟨p2, hp2⟩
  have hp2l : p2.length = msg.length + 1 + (120 - (msg.length + 1) % 64) % 64 := by
    simp only [alloc.vec.Vec.length] at hp1l ⊢
    simp [hp2, hp1l]
  have hp2v : p2.val.length ≤ msg.length + 64 := by
    simp only [alloc.vec.Vec.length] at hp2l; omega
  have hz : (120 - p1.length % 64) % 64 = (119 - msg.length % 64) % 64 := by omega
  have hval : bytes p2.val = bytes msg.val ++ [0x80#8] ++
      List.replicate ((119 - msg.length % 64) % 64) 0#8 := by
    rw [hp2, hp1, hp, hz]
    simp [bytes]
  clear hp2 hp1 hp hp1l hp2l hz
  step*
  all_goals try (simp only [List.length_append, List.length_cons, List.length_nil, *]; scalar_tac)
  have hb : bitlen.bv.toNat = 8 * (pre.val + msg.length) := by
    have : bitlen.val = 8 * (pre.val + msg.length) := by simp [*]; scalar_tac
    exact this
  have ht : Spec.toByte (8 * (pre.val + msg.length)) 8 =
      [i4.bv, i6.bv, i8.bv, i10.bv, i12.bv, i14.bv, i16.bv, i17.bv] := by
    rw [← hb, toByte8]
    simp [*]
  simp only [padFrom, bytes_length, ht, ← hval]
  simp [*, bytes]

theorem hashFrom_append64 (st : List Word) (B P : Spec.Bytes) (hB : B.length = 64) :
    hashFrom st (B ++ P) = hashFrom (compress st B) P := by
  have hl : (B ++ P).length / 64 = P.length / 64 + 1 := by simp [hB]
  simp only [hashFrom, hl, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  have h0 : blockAt (B ++ P) 0 = B := by
    simp [blockAt, hB]
  have hk : ∀ k, blockAt (B ++ P) (k + 1) = blockAt P k := by
    intro k
    simp only [blockAt]
    have : 64 * (k + 1) = B.length + 64 * k := by rw [hB]; ring
    rw [this, List.drop_append, List.drop_eq_nil_of_le (by omega)]
    simp
  simp only [h0, hk]

/-- Padding commutes with splitting off a whole first block. -/
theorem padFrom_append64 (pre : Nat) (B m : Spec.Bytes) (hB : B.length = 64) :
    padFrom pre (B ++ m) = B ++ padFrom (pre + 64) m := by
  have e1 : (119 - (64 + m.length) % 64) % 64 = (119 - m.length % 64) % 64 := by omega
  have e2 : 8 * (pre + (64 + m.length)) = 8 * (pre + 64 + m.length) := by ring
  simp [padFrom, hB, e2]

/-- The first loop of `sha256_from`: whole blocks, straight from the message. -/
theorem sha256_from_loop0_spec (msg : Slice U8) (pre : Nat) (S0 : List Word)
    (st : Array U32 8#usize) (off : Usize)
    (hmax : msg.length + 64 ≤ Usize.max) (hmod : off.val % 64 = 0) (hle : off.val ≤ msg.length)
    (hinv : hashFrom S0 (padFrom pre (bytes msg.val)) =
      hashFrom (wv st.val) (padFrom (pre + off.val) ((bytes msg.val).drop off.val))) :
    sha256.sha256_from_loop0 msg st off ⦃ r =>
      r.2.val % 64 = 0 ∧ r.2.val ≤ msg.length ∧
      hashFrom S0 (padFrom pre (bytes msg.val)) =
        hashFrom (wv r.1.val) (padFrom (pre + r.2.val) ((bytes msg.val).drop r.2.val)) ⦄ := by
  unfold sha256.sha256_from_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : Array U32 8#usize × Usize) => msg.length - q.2.val)
    (inv := fun q => q.2.val % 64 = 0 ∧ q.2.val ≤ msg.length ∧
      hashFrom S0 (padFrom pre (bytes msg.val)) =
        hashFrom (wv q.1.val) (padFrom (pre + q.2.val) ((bytes msg.val).drop q.2.val)))
  · rintro ⟨st, off⟩ ⟨hmod, hle, hinv⟩
    simp only [sha256.sha256_from_loop0.body]
    simp only at hmod hle hinv
    step*
    · refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have hB : (((bytes msg.val).drop off.val).take 64).length = 64 := by
        simp; scalar_tac
      have hsplit : (bytes msg.val).drop off.val =
          ((bytes msg.val).drop off.val).take 64 ++ (bytes msg.val).drop (off.val + 64) := by
        rw [← List.drop_drop, List.take_append_drop]
      rw [hinv, hsplit, padFrom_append64 _ _ _ hB, hashFrom_append64 _ _ _ hB]
      rw [st1_post, i_post, ← Nat.add_assoc]
  · exact ⟨hmod, hle, hinv⟩

theorem sha256_from_loop1_spec (p : alloc.vec.Vec U8) (S0 : List Word) (state : Array U32 8#usize)
    (off : Usize)
    (hp : p.length % 64 = 0) (hoff : off.val % 64 = 0) (hle : off.val ≤ p.length)
    (hinv : wv state.val = (List.range (off.val / 64)).foldl
      (fun st k => compress st (blockAt (bytes p.val) k)) S0) :
    sha256.sha256_from_loop1 state p off ⦃ r =>
      wv r.val = (List.range (p.length / 64)).foldl
        (fun st k => compress st (blockAt (bytes p.val) k)) S0 ⦄ := by
  unfold sha256.sha256_from_loop1
  apply loop.spec_decr_nat
    (measure := fun (q : Array U32 8#usize × Usize) => p.length - q.2.val)
    (inv := fun q => q.2.val % 64 = 0 ∧ q.2.val ≤ p.length ∧
      wv q.1.val = (List.range (q.2.val / 64)).foldl
        (fun st k => compress st (blockAt (bytes p.val) k)) S0)
  · rintro ⟨state, off⟩ ⟨hoff, hle, hinv⟩
    simp only [sha256.sha256_from_loop1.body]
    simp only at hoff hle hinv
    have h64 : off.val = p.length ∨ off.val + 64 ≤ p.length := by omega
    have hpm : p.length ≤ Usize.max := by scalar_tac
    step*
    · simp [alloc.vec.Vec.deref]; scalar_tac
    · refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have e : o1.val / 64 = off.val / 64 + 1 := by scalar_tac
      rw [e, List.range_succ, List.foldl_append, ← hinv]
      have e2 : 64 * (off.val / 64) = off.val := by omega
      simp [blockAt, alloc.vec.Vec.deref, *]
  · exact ⟨hoff, hle, hinv⟩

theorem take_set4 {α} (l : List α) (i : Nat) (a b c d : α) (h : i + 3 < l.length) :
    ((((l.set i a).set (i + 1) b).set (i + 2) c).set (i + 3) d).take (i + 4) =
      l.take i ++ [a, b, c, d] := by
  rw [show i + 4 = i + 3 + 1 from rfl, take_set_succ _ _ _ (by simpa using h),
    show i + 3 = i + 2 + 1 from rfl, take_set_succ _ _ _ (by simp; omega),
    show i + 2 = i + 1 + 1 from rfl, take_set_succ _ _ _ (by simp; omega),
    take_set_succ _ _ _ (by omega)]
  simp

/-- Big-endian serialisation of the hash state. -/
def ser (l : List Word) : Spec.Bytes := l.flatMap fun w => Spec.toByte w.toNat 4

theorem digest_loop_spec (state : Array U32 8#usize) (out : Array U8 32#usize) (i : Usize)
    (hi : i.val ≤ 8)
    (hinv : bytes (out.val.take (4 * i.val)) = ser (wv (state.val.take i.val))) :
    sha256.digest_loop state out i ⦃ r => bytes r.val = ser (wv state.val) ⦄ := by
  unfold sha256.digest_loop
  apply loop.spec_decr_nat
    (measure := fun (q : Array U8 32#usize × Usize) => 8 - q.2.val)
    (inv := fun q => q.2.val ≤ 8 ∧
      bytes (q.1.val.take (4 * q.2.val)) = ser (wv (state.val.take q.2.val)))
  · rintro ⟨out, i⟩ ⟨hi, hinv⟩
    simp only [sha256.digest_loop.body]
    simp only at hi hinv
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have hl : out.val.length = 32 := by scalar_tac
      have hs : state.val.length = 8 := by scalar_tac
      have e : 4 * i12.val = 4 * i.val + 4 := by scalar_tac
      rw [e, i12_post, a_post, out3_post, out2_post, out1_post]
      simp only [Array.set_val_eq, i10_post, i8_post, i5_post, i2_post]
      rw [take_set4 _ _ _ _ _ _ (by scalar_tac)]
      rw [List.take_succ_eq_append_getElem (by scalar_tac)]
      simp only [bytes_append, hinv, wv, ser, List.map_append, List.flatMap_append,
        List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        toByte4]
      simp [bytes, *]
    · have h8 : i.val = 8 := by scalar_tac
      have h1 : out.val.length = 32 := by scalar_tac
      have h2 : state.val.length = 8 := by scalar_tac
      rw [h8, List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hinv
      exact hinv
  · exact ⟨hi, hinv⟩

@[step]
theorem digest_spec (state : Array U32 8#usize) :
    sha256.digest state ⦃ r => bytes r.val = ser (wv state.val) ⦄ := by
  unfold sha256.digest
  apply digest_loop_spec
  · simp
  · simp [ser, wv]

@[step]
theorem sha256_from_spec (state : Array U32 8#usize) (pre : Usize) (msg : Slice U8)
    (hpre : pre.val % 64 = 0) (h : Room (pre.val + msg.length) 72) :
    sha256.sha256_from state pre msg ⦃ r =>
      bytes r.val = ser (hashFrom (wv state.val) (padFrom pre.val (bytes msg.val))) ⦄ := by
  unfold sha256.sha256_from
  have hR := h
  simp only [Room] at hR
  step with sha256_from_loop0_spec msg pre.val (wv state.val) state 0#usize
    (by scalar_tac) (by simp) (by simp) (by simp) as ⟨st, off, hmod, hle, hinv⟩
  step as ⟨s, hs⟩
  step as ⟨i1, hi1⟩
  have hsv : bytes s.val = (bytes msg.val).drop off.val := by
    simp [hs, List.slice]
  have hsl : s.length = msg.length - off.val := by
    simp [Slice.length, hs, List.slice]
  step as ⟨p, hp⟩
  have hpl : p.length % 64 = 0 := by
    have := padFrom_length i1.val (bytes s.val)
    rw [← hp] at this
    simpa [alloc.vec.Vec.length] using this
  step with sha256_from_loop1_spec p (wv st.val) as ⟨st1, hst⟩
  · simp
  step as ⟨r, hr⟩
  rw [hr, hst, hinv, hashFrom, ← hsv, ← hi1, ← hp]
  simp [alloc.vec.Vec.length]

@[step]
theorem sha256_spec (msg : Slice U8) (h : Room msg.length 72) :
    sha256.sha256 msg ⦃ r => bytes r.val = Spec.sha256 (bytes msg.val) ⦄ := by
  unfold sha256.sha256
  step with sha256_from_spec as ⟨r, hr⟩
  rw [hr, H0_eq, padFrom_zero]
  simp only [ser, hashFrom, Spec.SHA256.sha256]

theorem hmac_sha256_loop_spec (key : Slice U8) (inner outer : alloc.vec.Vec U8) (i : Usize)
    (K0 : List U8) (hK0 : K0 = key.val ++ List.replicate (64 - key.length) 0#u8)
    (hk : key.length ≤ 64) (hi : i.val ≤ 64)
    (hin : inner.val = (K0.take i.val).map (· ^^^ 54#u8))
    (hout : outer.val = (K0.take i.val).map (· ^^^ 92#u8)) :
    sha256.hmac_sha256_loop key inner outer i ⦃ r =>
      r.1.val = K0.map (· ^^^ 54#u8) ∧ r.2.val = K0.map (· ^^^ 92#u8) ⦄ := by
  have hKl : K0.length = 64 := by simp [hK0]; scalar_tac
  unfold sha256.hmac_sha256_loop
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × alloc.vec.Vec U8 × Usize) => 64 - q.2.2.val)
    (inv := fun q => q.2.2.val ≤ 64 ∧ q.1.val = (K0.take q.2.2.val).map (· ^^^ 54#u8) ∧
      q.2.1.val = (K0.take q.2.2.val).map (· ^^^ 92#u8))
  · rintro ⟨inner, outer, i⟩ ⟨hi, hin, hout⟩
    simp only [sha256.hmac_sha256_loop.body]
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
          have h2 : i.val - key.val.length < 64 - key.val.length := by scalar_tac
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
    · have h64 : i.val = 64 := by scalar_tac
      rw [h64, List.take_of_length_le (by omega)] at hin hout
      exact ⟨hin, hout⟩
  · exact ⟨hi, hin, hout⟩

theorem bytes_map_xor (l : List U8) (c : U8) :
    bytes (l.map (· ^^^ c)) = (bytes l).map (· ^^^ c.bv) := by
  simp [bytes]

@[step]
theorem hmac_sha256_spec (key msg : Slice U8) (hk : key.length ≤ 64) (h : Room msg.length 136) :
    sha256.hmac_sha256 key msg ⦃ r => bytes r.val = Spec.hmacSha256 (bytes key.val) (bytes msg.val) ⦄ := by
  unfold sha256.hmac_sha256
  obtain ⟨h1, h2⟩ := h
  step with hmac_sha256_loop_spec key _ _ _ (key.val ++ List.replicate (64 - key.length) 0#u8) rfl
    as ⟨inner, outer, hin, hout⟩
  · simp
  · simp
  have hil : inner.val.length = 64 := by simp [hin]; scalar_tac
  have hol : outer.val.length = 64 := by simp [hout]; scalar_tac
  step as ⟨inner1, hinner1⟩
  step as ⟨ih, hih⟩
  · simp [Room, alloc.vec.Vec.deref, hinner1, hil]; scalar_tac
  step*
  · simp [Room, alloc.vec.Vec.deref, *]; scalar_tac
  have hkl : ¬ (bytes key.val).length > 64 := by simp; scalar_tac
  rw [r_post]
  simp only [Spec.hmacSha256, hkl, ↓reduceIte]
  simp only [alloc.vec.Vec.deref] at hih ⊢
  have e1 : (0#u8 ^^^ 92#u8).bv = 92#8 := by decide
  have e2 : (0#u8 ^^^ 54#u8).bv = 54#8 := by decide
  simp [outer1_post, s1_post, hout, hih, hinner1, hin, bytes_map_xor]
  simp [bytes, e1, e2]

/-! Hashing a message whose first block is already compressed. -/

theorem pad_append64 (B m : Spec.Bytes) (hB : B.length = 64) :
    pad (B ++ m) = B ++ padFrom 64 m := by
  simp [pad, padFrom, hB]

/-- SHA-256 of `B ‖ m`, for a 64-byte first block `B`, continues from the
compression of `B`. -/
theorem sha256_prefix64 (B m : Spec.Bytes) (hB : B.length = 64) :
    Spec.sha256 (B ++ m) = ser (hashFrom (compress H0 B) (padFrom 64 m)) := by
  show ser (hashFrom H0 (pad (B ++ m))) = _
  rw [pad_append64 _ _ hB, hashFrom_append64 _ _ _ hB]

/-! Lists updated at one position. -/

theorem getElem!_set_ne' {α} [Inhabited α] (l : List α) (i j : Nat) (x : α) (h : i ≠ j) :
    (l.set i x)[j]! = l[j]! := by
  simp [List.getElem!_eq_getElem?_getD, h]

theorem getElem!_set_self' {α} [Inhabited α] (l : List α) (i : Nat) (x : α) (h : i < l.length) :
    (l.set i x)[i]! = x := by
  simp [h]

end slhdsa
