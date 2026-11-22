import Link.Basic

/-!
# Word packing for SHA-256 (Spec-free part of the former `Link.Sha256`)

`Ideal/Sha/Instantiate.lean` imports `Link.Sha256` and uses two of its lemmas, `Link.be32` and
`Link.app4` (byte/word packing, no `Spec`).  The single-set tree's `Link.Sha256` (git commit
`26aa3d8`) also proved `Spec` = VCVio for SHA-256 / HMAC / MGF1 against that tree's single-set
`Spec`.  This module keeps, with the same names, bodies and comments, exactly the declarations of
that file that mention neither `Spec` nor the `Spec`-typed readings `sp` / `spA` (`W`, `W_get`,
`W_get'`, `W_length`, `W_set`, `app4`, `be32`, `take_set_succ`, `take_get`, `foldl_rel`,
`load_take`, `compress_size`); nothing was added (checked by diff before the single-set files were
removed: `STATUS.md`, "The stand-ins").  The six-set `Spec` = VCVio proofs for SHA-256 are
`MLink/Sha256.lean`.
-/

namespace Link

open VCVio.Algorithms.Sha2

/-! ### Word-level correspondence -/

/-- Read a `UInt32` array as a list of spec words. -/
def W (a : Array UInt32) : List (BitVec 32) := a.toList.map UInt32.toBitVec

theorem W_get (a : Array UInt32) (i : Nat) : (W a)[i]! = (a[i]!).toBitVec := by
  by_cases h : i < a.size <;> simp [W, h]
  rfl
theorem W_get' (a : Array UInt32) (i : Nat) :
    (W a)[i]?.getD default = (a[i]!).toBitVec := by
  rw [← W_get]; simp
@[simp] theorem W_length (a : Array UInt32) : (W a).length = a.size := by simp [W]
theorem W_set (a : Array UInt32) (i : Nat) (v : UInt32) :
    W (a.setIfInBounds i v) = (W a).set i v.toBitVec := by
  simp [W, List.map_set]

theorem app4 (a b c d : BitVec 8) (i : Nat) : (a ++ b ++ c ++ d : BitVec 32).getLsbD i =
   if i < 8 then d.getLsbD i else if i < 16 then c.getLsbD (i-8) else if i < 24 then b.getLsbD (i-16) else a.getLsbD (i-24) := by
  have : (a ++ b ++ c ++ d : BitVec 32) = BitVec.append (BitVec.append (BitVec.append a b) c) d := rfl
  rw [this]
  have h := @BitVec.getLsbD_append
  simp only [HAppend.hAppend] at h
  simp only [h]
  by_cases h1 : i < 8
  · simp [h1]
  · by_cases h2 : i < 16
    · simp [h1, h2, show i - 8 < 8 by omega]
    · by_cases h3 : i < 24
      · simp [h1, h2, h3, show ¬ (i - 8 < 8) by omega, show i - 8 - 8 = i - 16 by omega]
        intro; omega
      · simp [h1, h2, h3, show ¬ (i - 8 < 8) by omega, show ¬ (i - 8 - 8 < 8) by omega, show i - 8 - 8 - 8 = i - 24 by omega]
theorem be32 (a b c d : UInt8) :
    (a.toUInt32 <<< 24 ||| b.toUInt32 <<< 16 ||| c.toUInt32 <<< 8 ||| d.toUInt32).toBitVec
      = a.toBitVec ++ b.toBitVec ++ c.toBitVec ++ d.toBitVec := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [app4]
  have ge : ∀ (x : BitVec 8) (j : Nat), 8 ≤ j → x.getLsbD j = false := fun x j h => BitVec.getLsbD_of_ge x j h
  simp
  by_cases h1 : i < 8
  · simp [h1, show i < 16 by omega, show i < 24 by omega]
    intro; omega
  · by_cases h2 : i < 16
    · simp [h1, h2, hi, show i < 24 by omega, show i - 8 < 32 by omega, ge _ i (by omega)]
    · by_cases h3 : i < 24
      · simp [h1, h2, h3, hi, show i - 8 < 32 by omega, show i - 16 < 32 by omega, ge _ i (by omega), ge _ (i-8) (by omega)]
      · simp [h1, h2, h3, hi, show i - 8 < 32 by omega, show i - 16 < 32 by omega, show i - 24 < 32 by omega, ge _ i (by omega), ge _ (i-8) (by omega), ge _ (i-16) (by omega)]

/-! ### List helpers -/

theorem take_set_succ {α} (l : List α) (n : Nat) (v : α) (h : n < l.length) :
    (l.set n v).take (n + 1) = l.take n ++ [v] := by
  rw [List.take_add_one, List.take_set_of_le (Nat.le_refl _)]
  simp [h]

theorem take_get {α} [Inhabited α] (l : List α) (n i : Nat) (h : i < n) :
    (l.take n)[i]! = l[i]! := by
  simp [h]

theorem foldl_rel {α β γ} (r : α → β) (f : α → γ → α) (g : β → γ → β)
    (h : ∀ a c, r (f a c) = g (r a) c) (l : List γ) (a : α) :
    r (l.foldl f a) = l.foldl g (r a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [ih, h]

/-! ### Message schedule -/

theorem load_take (f : Nat → UInt32) (n : Nat) (w0 : Array UInt32) (h : n ≤ w0.size) :
    (List.foldl (fun b a => b.setIfInBounds a (f a)) w0 (List.range' 0 n)).size = w0.size ∧
    (W (List.foldl (fun b a => b.setIfInBounds a (f a)) w0 (List.range' 0 n))).take n
      = (List.range n).map (fun t => (f t).toBitVec) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append]
    refine ⟨by simp [h1], ?_⟩
    simp only [List.foldl_cons, List.foldl_nil, W_set, Nat.zero_add, Nat.one_mul]
    rw [take_set_succ _ _ _ (by simp [h1]; omega), h2, List.range_succ, List.map_append]
    rfl

theorem compress_size (st : Array UInt32) (m : ByteArray) (b : Nat) :
    (compress st m b).size = 8 := by
  simp [compress, feedForward256]

end Link
