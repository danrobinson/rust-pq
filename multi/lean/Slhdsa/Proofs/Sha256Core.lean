import Slhdsa.Proofs.Basic
open Aeneas Aeneas.Std Result

/-! The Rust SHA-256 computes `Spec.sha256`. -/

namespace slhdsa
open Spec.SHA256

theorem be32_eq (a b c d : BitVec 8) :
    BitVec.setWidth 32 a <<< 24 ||| BitVec.setWidth 32 b <<< 16 ||| BitVec.setWidth 32 c <<< 8
      ||| BitVec.setWidth 32 d = a ++ b ++ c ++ d := by
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
    BitVec.getLsbD_eq_getElem?_getD]
  by_cases h1 : i < 8
  · simp [h1]; grind
  · by_cases h2 : i < 16
    · simp [h1, h2]; grind
    · by_cases h3 : i < 24
      · simp [h1, h2, h3]; grind
      · simp [h1, h2, h3]; grind

@[step]
theorem load_be32_spec (data : Slice U8) (off : Usize) (h : off.val + 3 < data.length) :
    sha256.load_be32 data off ⦃ r => r.bv = word (bytes data.val) off.val ⦄ := by
  unfold sha256.load_be32
  step*
  simp only [word]
  rw [bytes_getElem! _ _ (by scalar_tac), bytes_getElem! _ _ (by scalar_tac),
    bytes_getElem! _ _ (by scalar_tac), bytes_getElem! _ _ (by scalar_tac)]
  simp [*, be32_eq]

theorem schedule_loop0_spec (data : Slice U8) (off : Usize) (w : Array U32 64#usize) (i : Usize)
    (hoff : off.val + 64 ≤ data.length) (hi : i.val ≤ 16)
    (hinv : ∀ j < i.val, (w.val[j]!).bv = word (bytes data.val) (off.val + 4 * j)) :
    sha256.schedule_loop0 data off w i ⦃ r =>
      r.2.val = 16 ∧ ∀ j < 16, (r.1.val[j]!).bv = word (bytes data.val) (off.val + 4 * j) ⦄ := by
  unfold sha256.schedule_loop0
  apply loop.spec_decr_nat (measure := fun (p : Array U32 64#usize × Usize) => 16 - p.2.val)
    (inv := fun p => p.2.val ≤ 16 ∧
      ∀ j < p.2.val, (p.1.val[j]!).bv = word (bytes data.val) (off.val + 4 * j))
  · rintro ⟨w, i⟩ ⟨hi, hinv⟩
    simp only [sha256.schedule_loop0.body]
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
def wv (l : List U32) : List Word := l.map (·.bv)

@[simp] theorem wv_length (l : List U32) : (wv l).length = l.length := by simp [wv]

theorem wv_getElem! (l : List U32) (i : Nat) (h : i < l.length) :
    (wv l)[i]! = (l[i]'h).bv := by
  simp [wv, h]

@[simp] theorem rotr_bv (x : U32) (s : U32) :
    (core.num.U32.rotate_right x s).bv = x.bv.rotateRight s.val := rfl

theorem take_set_succ {α} (l : List α) (i : Nat) (x : α) (h : i < l.length) :
    (l.set i x).take (i + 1) = l.take i ++ [x] := by
  rw [List.take_succ_eq_append_getElem (by simpa using h)]
  simp [List.take_set, List.set_eq_of_length_le]

theorem repeat_succ {α} (f : α → α) (n : Nat) (a : α) :
    Nat.repeat f (n + 1) a = f (Nat.repeat f n a) := rfl

theorem schedule_loop1_spec (B : List Word) (w : Array U32 64#usize) (i : Usize)
    (hi : 16 ≤ i.val ∧ i.val ≤ 64)
    (hinv : wv (w.val.take i.val) = Nat.repeat scheduleStep (i.val - 16) B) :
    sha256.schedule_loop1 w i ⦃ r => wv r.val = Nat.repeat scheduleStep 48 B ⦄ := by
  unfold sha256.schedule_loop1
  apply loop.spec_decr_nat (measure := fun (p : Array U32 64#usize × Usize) => 64 - p.2.val)
    (inv := fun p => (16 ≤ p.2.val ∧ p.2.val ≤ 64) ∧
      wv (p.1.val.take p.2.val) = Nat.repeat scheduleStep (p.2.val - 16) B)
  · rintro ⟨w, i⟩ ⟨hi, hinv⟩
    simp only [sha256.schedule_loop1.body]
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
    · have h1 : i.val = 64 := by scalar_tac
      have h2 : w.val.length = 64 := by scalar_tac
      rw [h1, List.take_of_length_le (by omega)] at hinv
      simpa [h1] using hinv
  · exact ⟨hi, hinv⟩

theorem getElem!_take_drop {α} [Inhabited α] (l : List α) (off n k : Nat) (hk : k < n) :
    ((l.drop off).take n)[k]! = l[off + k]! := by
  simp [List.getElem?_drop, hk]

theorem word_block (l : Spec.Bytes) (off i : Nat) (hi : i + 3 < 64) :
    word ((l.drop off).take 64) i = word l (off + i) := by
  simp only [word]
  rw [getElem!_take_drop _ _ _ _ (by omega), getElem!_take_drop _ _ _ _ (by omega),
    getElem!_take_drop _ _ _ _ (by omega), getElem!_take_drop _ _ _ _ (by omega)]
  simp [Nat.add_assoc]

@[step]
theorem schedule_spec (data : Slice U8) (off : Usize) (hoff : off.val + 64 ≤ data.length) :
    sha256.schedule data off ⦃ r =>
      wv r.val = schedule (((bytes data.val).drop off.val).take 64) ⦄ := by
  unfold sha256.schedule
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

theorem K_eq : wv sha256.K.val = K := by
  unfold sha256.K
  rfl

theorem H0_eq : wv sha256.H0.val = H0 := by
  unfold sha256.H0
  rfl

/-- The spec-level view of the eight working variables. -/
def st8 (p : U32 × U32 × U32 × U32 × U32 × U32 × U32 × U32) : State :=
  (p.1.bv, p.2.1.bv, p.2.2.1.bv, p.2.2.2.1.bv, p.2.2.2.2.1.bv, p.2.2.2.2.2.1.bv,
    p.2.2.2.2.2.2.1.bv, p.2.2.2.2.2.2.2.bv)

theorem compress_loop_spec (W : List Word) (init : State) (w : Array U32 64#usize)
    (a b c d e f g h : U32) (i : Usize) (hW : wv w.val = W) (hi : i.val ≤ 64)
    (hinv : st8 (a, b, c, d, e, f, g, h) = (List.range i.val).foldl (round W) init) :
    sha256.compress_portable_loop w a b c d e f g h i ⦃ r =>
      st8 r = (List.range 64).foldl (round W) init ⦄ := by
  unfold sha256.compress_portable_loop
  apply loop.spec_decr_nat
    (measure := fun (p : U32 × U32 × U32 × U32 × U32 × U32 × U32 × U32 × Usize) =>
      64 - p.2.2.2.2.2.2.2.2.val)
    (inv := fun p => p.2.2.2.2.2.2.2.2.val ≤ 64 ∧
      st8 (p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
        p.2.2.2.2.2.2.2.1) = (List.range p.2.2.2.2.2.2.2.2.val).foldl (round W) init)
  · rintro ⟨a, b, c, d, e, f, g, h, i⟩ ⟨hi, hinv⟩
    simp only [sha256.compress_portable_loop.body]
    simp only at hi hinv
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [i21_post, List.range_succ, List.foldl_append, ← hinv]
      have hk : K[i.val]! = (sha256.K.val[i.val]'(by scalar_tac)).bv := by
        rw [← K_eq, wv_getElem!]
      have hw : W[i.val]! = (w.val[i.val]'(by scalar_tac)).bv := by
        rw [← hW, wv_getElem!]
      simp [st8, round, bsig0, bsig1, Spec.SHA256.ch, Spec.SHA256.maj, *]
  · exact ⟨hi, hinv⟩

@[step]
theorem compress_portable_spec (state : Array U32 8#usize) (data : Slice U8) (off : Usize)
    (hoff : off.val + 64 ≤ data.length) :
    sha256.compress_portable state data off ⦃ r =>
      wv r.val = compress (wv state.val) (((bytes data.val).drop off.val).take 64) ⦄ := by
  unfold sha256.compress_portable
  step as ⟨w, hw⟩
  step*
  step with compress_loop_spec (wv w.val) (st8 (a, b, c, d, e, f, g, h))
    as ⟨a1, b1, c1, d1, e1, f1, g1, h1, hr⟩
  · simp
  step*
  simp only [Spec.SHA256.compress, ← hw]
  have hs : ∀ j (hj : j < 8), (wv state.val)[j]! = (state.val[j]'(by scalar_tac)).bv :=
    fun j hj => wv_getElem! _ _ _
  rw [hs 0 (by omega), hs 1 (by omega), hs 2 (by omega), hs 3 (by omega), hs 4 (by omega),
    hs 5 (by omega), hs 6 (by omega), hs 7 (by omega)]
  simp only [st8] at hr
  simp only [a_post, b_post, c_post, d_post, e_post, f_post, g_post, h_post] at hr
  rw [← hr]
  simp [wv, *]

end slhdsa
