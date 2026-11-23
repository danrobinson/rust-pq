import Slhdsa.Proofs.Sha256
open Aeneas Aeneas.Std Result

/-! SHA-512: the schedule, the portable compression function and the padding loops.

The rest of SHA-512 and HMAC-SHA-512 is in `Sha512.lean`, which goes through
`sha512::compress` (`Compress512Top.lean`, the one SHA-512 proof file that
depends on the build). -/

namespace slhdsa

/-! The helper lemmas live in `slhdsa.S512`, so that their names do not clash with the
SHA-256 analogues in `slhdsa`. -/
namespace S512
open Spec.SHA512

/-- Appending a slice of bytes to a vector. -/
@[local step]
theorem extend_u8_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ :=
  extend_from_slice_u8_spec v s h

set_option maxHeartbeats 4000000 in
theorem be64_eq (a b c d e f g h : BitVec 8) :
    BitVec.setWidth 64 a <<< 56 ||| BitVec.setWidth 64 b <<< 48 ||| BitVec.setWidth 64 c <<< 40
      ||| BitVec.setWidth 64 d <<< 32 ||| BitVec.setWidth 64 e <<< 24
      ||| BitVec.setWidth 64 f <<< 16 ||| BitVec.setWidth 64 g <<< 8
      ||| BitVec.setWidth 64 h = a ++ b ++ c ++ d ++ e ++ f ++ g ++ h := by
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
    BitVec.getLsbD_eq_getElem?_getD]
  by_cases h1 : i < 8
  · simp [h1]; grind
  · by_cases h2 : i < 16
    · simp [h1, h2]; grind
    · by_cases h3 : i < 24
      · simp [h1, h2, h3]; grind
      · by_cases h4 : i < 32
        · simp [h1, h2, h3, h4]; grind
        · by_cases h5 : i < 40
          · simp [h1, h2, h3, h4, h5]; grind
          · by_cases h6 : i < 48
            · simp [h1, h2, h3, h4, h5, h6]; grind
            · by_cases h7 : i < 56
              · simp [h1, h2, h3, h4, h5, h6, h7]; grind
              · simp [h1, h2, h3, h4, h5, h6, h7]; grind

set_option maxHeartbeats 4000000 in
@[step]
theorem load_be64_spec (data : Slice U8) (off : Usize) (h : off.val + 7 < data.length) :
    sha512.load_be64 data off ⦃ r => r.bv = word (bytes data.val) off.val ⦄ := by
  unfold sha512.load_be64
  step*
  simp only [word]
  rw [bytes_getElem! _ _ (by scalar_tac), bytes_getElem! _ _ (by scalar_tac),
    bytes_getElem! _ _ (by scalar_tac), bytes_getElem! _ _ (by scalar_tac),
    bytes_getElem! _ _ (by scalar_tac), bytes_getElem! _ _ (by scalar_tac),
    bytes_getElem! _ _ (by scalar_tac), bytes_getElem! _ _ (by scalar_tac)]
  simp [*, be64_eq]

theorem schedule_loop0_spec (data : Slice U8) (off : Usize) (w : Array U64 80#usize) (i : Usize)
    (hoff : off.val + 128 ≤ data.length) (hi : i.val ≤ 16)
    (hinv : ∀ j < i.val, (w.val[j]!).bv = word (bytes data.val) (off.val + 8 * j)) :
    sha512.schedule_loop0 data off w i ⦃ r =>
      r.2.val = 16 ∧ ∀ j < 16, (r.1.val[j]!).bv = word (bytes data.val) (off.val + 8 * j) ⦄ := by
  unfold sha512.schedule_loop0
  apply loop.spec_decr_nat (measure := fun (p : Array U64 80#usize × Usize) => 16 - p.2.val)
    (inv := fun p => p.2.val ≤ 16 ∧
      ∀ j < p.2.val, (p.1.val[j]!).bv = word (bytes data.val) (off.val + 8 * j))
  · rintro ⟨w, i⟩ ⟨hi, hinv⟩
    simp only [sha512.schedule_loop0.body]
    simp only at hi hinv
    step*
    · subst a_post
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro j hj
      by_cases hji : j = i.val
      · subst hji; simp_lists; simp [*]
      · have : j < i.val := by scalar_tac
        have h' := hinv j this
        rw [getElem!_eq _ _ (by scalar_tac)] at h'
        simp_lists; exact h'
  · exact ⟨hi, hinv⟩

/-- The spec-level view of a list of machine words. -/
def wv (l : List U64) : List Word := l.map (·.bv)

@[simp] theorem wv_length (l : List U64) : (wv l).length = l.length := by simp [wv]

theorem wv_getElem! (l : List U64) (i : Nat) (h : i < l.length) :
    (wv l)[i]! = (l[i]'h).bv := by
  simp [wv, h]

@[simp] theorem rotr_bv (x : U64) (s : U32) :
    (core.num.U64.rotate_right x s).bv = x.bv.rotateRight s.val := rfl

theorem schedule_loop1_spec (B : List Word) (w : Array U64 80#usize) (i : Usize)
    (hi : 16 ≤ i.val ∧ i.val ≤ 80)
    (hinv : wv (w.val.take i.val) = Nat.repeat scheduleStep (i.val - 16) B) :
    sha512.schedule_loop1 w i ⦃ r => wv r.val = Nat.repeat scheduleStep 64 B ⦄ := by
  unfold sha512.schedule_loop1
  apply loop.spec_decr_nat (measure := fun (p : Array U64 80#usize × Usize) => 80 - p.2.val)
    (inv := fun p => (16 ≤ p.2.val ∧ p.2.val ≤ 80) ∧
      wv (p.1.val.take p.2.val) = Nat.repeat scheduleStep (p.2.val - 16) B)
  · rintro ⟨w, i⟩ ⟨hi, hinv⟩
    simp only [sha512.schedule_loop1.body]
    simp only at hi hinv
    step*
    · subst a_post
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have e : i18.val - 16 = (i.val - 16) + 1 := by scalar_tac
      rw [e, repeat_succ, ← hinv, i18_post]
      simp only [Array.set_val_eq]
      rw [take_set_succ _ _ _ (by scalar_tac)]
      simp only [scheduleStep, wv_length, List.length_take]
      have hl : min i.val w.val.length = i.val := by scalar_tac
      rw [hl]
      rw [wv_getElem! _ _ (by simp; scalar_tac), wv_getElem! _ _ (by simp; scalar_tac),
        wv_getElem! _ _ (by simp; scalar_tac), wv_getElem! _ _ (by simp; scalar_tac)]
      simp only [wv, List.map_append, List.map_cons, List.map_nil, List.getElem_take]
      congr 2
      simp [*, ssig0, ssig1]
      ac_rfl
    · have h1 : i.val = 80 := by scalar_tac
      have h2 : w.val.length = 80 := by scalar_tac
      rw [h1, List.take_of_length_le (by omega)] at hinv
      simpa [h1] using hinv
  · exact ⟨hi, hinv⟩

theorem word_block (l : Spec.Bytes) (off i : Nat) (hi : i + 7 < 128) :
    word ((l.drop off).take 128) i = word l (off + i) := by
  simp only [word]
  rw [getElem!_take_drop _ _ _ _ (by omega), getElem!_take_drop _ _ _ _ (by omega),
    getElem!_take_drop _ _ _ _ (by omega), getElem!_take_drop _ _ _ _ (by omega),
    getElem!_take_drop _ _ _ _ (by omega), getElem!_take_drop _ _ _ _ (by omega),
    getElem!_take_drop _ _ _ _ (by omega), getElem!_take_drop _ _ _ _ (by omega)]
  simp [Nat.add_assoc]

@[step]
theorem schedule_spec (data : Slice U8) (off : Usize) (hoff : off.val + 128 ≤ data.length) :
    sha512.schedule data off ⦃ r =>
      wv r.val = schedule (((bytes data.val).drop off.val).take 128) ⦄ := by
  unfold sha512.schedule
  step with schedule_loop0_spec as ⟨w1, i, hi, hw⟩
  simp only [schedule]
  apply schedule_loop1_spec
  · scalar_tac
  · simp only [hi, Nat.sub_self]
    show wv (List.take 16 w1.val) = blockWords _
    apply List.ext_getElem
    · simp [blockWords]
    · intro j h1 h2
      have hj : j < 16 := by simp at h1; omega
      have := hw j hj
      rw [getElem!_eq _ _ (by scalar_tac)] at this
      simp only [wv, blockWords, List.getElem_map, List.getElem_take, List.getElem_range]
      rw [this, word_block _ _ _ (by omega)]

theorem K_eq : wv sha512.K.val = K := by
  unfold sha512.K
  rfl

theorem H0_eq : wv sha512.H0.val = H0 := by
  unfold sha512.H0
  rfl

/-- The spec-level view of the eight working variables. -/
def st8 (p : U64 × U64 × U64 × U64 × U64 × U64 × U64 × U64) : State :=
  (p.1.bv, p.2.1.bv, p.2.2.1.bv, p.2.2.2.1.bv, p.2.2.2.2.1.bv, p.2.2.2.2.2.1.bv,
    p.2.2.2.2.2.2.1.bv, p.2.2.2.2.2.2.2.bv)

theorem compress_loop_spec (W : List Word) (init : State) (w : Array U64 80#usize)
    (a b c d e f g h : U64) (i : Usize) (hW : wv w.val = W) (hi : i.val ≤ 80)
    (hinv : st8 (a, b, c, d, e, f, g, h) = (List.range i.val).foldl (round W) init) :
    sha512.compress_portable_loop w a b c d e f g h i ⦃ r =>
      st8 r = (List.range 80).foldl (round W) init ⦄ := by
  unfold sha512.compress_portable_loop
  apply loop.spec_decr_nat
    (measure := fun (p : U64 × U64 × U64 × U64 × U64 × U64 × U64 × U64 × Usize) =>
      80 - p.2.2.2.2.2.2.2.2.val)
    (inv := fun p => p.2.2.2.2.2.2.2.2.val ≤ 80 ∧
      st8 (p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
        p.2.2.2.2.2.2.2.1) = (List.range p.2.2.2.2.2.2.2.2.val).foldl (round W) init)
  · rintro ⟨a, b, c, d, e, f, g, h, i⟩ ⟨hi, hinv⟩
    simp only [sha512.compress_portable_loop.body]
    simp only at hi hinv
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [i21_post, List.range_succ, List.foldl_append, ← hinv]
      have hk : K[i.val]! = (sha512.K.val[i.val]'(by scalar_tac)).bv := by
        rw [← K_eq, wv_getElem!]
      have hw : W[i.val]! = (w.val[i.val]'(by scalar_tac)).bv := by
        rw [← hW, wv_getElem!]
      simp [st8, round, bsig0, bsig1, Spec.SHA512.ch, Spec.SHA512.maj, *]
  · exact ⟨hi, hinv⟩

@[step]
theorem compress_portable_spec (state : Array U64 8#usize) (data : Slice U8) (off : Usize)
    (hoff : off.val + 128 ≤ data.length) :
    sha512.compress_portable state data off ⦃ r =>
      wv r.val = compress (wv state.val) (((bytes data.val).drop off.val).take 128) ⦄ := by
  unfold sha512.compress_portable
  step as ⟨w, hw⟩
  step*
  step with compress_loop_spec (wv w.val) (st8 (a, b, c, d, e, f, g, h))
    as ⟨a1, b1, c1, d1, e1, f1, g1, h1, hr⟩
  · simp
  step*
  simp only [Spec.SHA512.compress, ← hw]
  have hs : ∀ j (hj : j < 8), (wv state.val)[j]! = (state.val[j]'(by scalar_tac)).bv :=
    fun j hj => wv_getElem! _ _ _
  rw [hs 0 (by omega), hs 1 (by omega), hs 2 (by omega), hs 3 (by omega), hs 4 (by omega),
    hs 5 (by omega), hs 6 (by omega), hs 7 (by omega)]
  simp only [st8] at hr
  simp only [a_post, b_post, c_post, d_post, e_post, f_post, g_post, h_post] at hr
  rw [← hr]
  simp [wv, *]

theorem pad_loop0_spec (p0 : alloc.vec.Vec U8) (hlen : p0.length + 128 ≤ Usize.max) :
    sha512.pad_loop0 p0 ⦃ r =>
      r.val = p0.val ++ List.replicate ((240 - p0.length % 128) % 128) 0#u8 ⦄ := by
  unfold sha512.pad_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec U8) =>
      p0.length + (240 - p0.length % 128) % 128 - p.length)
    (inv := fun p => ∃ j, j ≤ (240 - p0.length % 128) % 128 ∧
      p.val = p0.val ++ List.replicate j 0#u8)
  · rintro p ⟨j, hj, hp⟩
    simp only [sha512.pad_loop0.body]
    have hl : p.length = p0.length + j := by
      simp only [alloc.vec.Vec.length, hp, List.length_append, List.length_replicate]
    step*
    · rename_i hne
      have hne' : (p0.length + j) % 128 ≠ 112 := by
        rw [← hl]; simp at hne; scalar_tac
      have hlt : j < (240 - p0.length % 128) % 128 := by omega
      refine ⟨⟨j + 1, by omega, ?_⟩, ?_⟩
      · rw [p1_post, hp, List.replicate_succ']; simp
      · have : p1.length = p.length + 1 := by simp [alloc.vec.Vec.length, p1_post]
        omega
  · exact ⟨0, by omega, by simp⟩

theorem pad_loop1_spec (p0 p : alloc.vec.Vec U8) (bitlen : U128) (i : U32)
    (hlen : p0.length + 16 ≤ Usize.max) (hi : i.val ≤ 16)
    (hinv : bytes p.val = bytes p0.val ++
      (List.range i.val).map fun j => BitVec.ofNat 8 (bitlen.val >>> (8 * (16 - 1 - j)))) :
    sha512.pad_loop1 p bitlen i ⦃ r =>
      bytes r.val = bytes p0.val ++ Spec.toByte bitlen.val 16 ⦄ := by
  unfold sha512.pad_loop1
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec U8 × U32) => 16 - q.2.val)
    (inv := fun q => q.2.val ≤ 16 ∧ bytes q.1.val = bytes p0.val ++
      (List.range q.2.val).map fun j => BitVec.ofNat 8 (bitlen.val >>> (8 * (16 - 1 - j))))
  · rintro ⟨p, i⟩ ⟨hi, hinv⟩
    simp only [sha512.pad_loop1.body]
    simp only at hi hinv
    have hl : p.val.length = p0.val.length + i.val := by
      have := congrArg List.length hinv
      simpa using this
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [i5_post, List.range_succ, List.map_append, ← List.append_assoc, ← hinv, p1_post]
    simp only [bytes_append, bytes_cons, bytes_nil, List.map_cons, List.map_nil]
    · congr 2
      have e : i3.val = bitlen.val >>> (8 * (16 - 1 - i.val)) := by
        rw [i3_post]; congr 1; scalar_tac
      rw [← e, i4_post, ← U128.bv_toNat, ofNat_toNat8]
      simp
    · have h16 : i.val = 16 := by scalar_tac
      rw [h16] at hinv
      exact hinv
  · exact ⟨hi, hinv⟩


end S512

end slhdsa
