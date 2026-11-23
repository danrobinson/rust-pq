import Slhdsa.Proofs.Hw.Wrappers
open Aeneas Aeneas.Std Result

/-! The SHA-512 intrinsic wrappers as plain functions.

`Slhdsa/FunsExternal.lean` defines each wrapper of `rust/src/sha512.rs`,
module `hw::arm`, as a function into Aeneas's `Result`. Here each is shown,
on a processor with the instructions (`Arm.haveSha512 = true`), to be a plain
function on lists and bit-vectors: an instruction of `Arm.lean`, or one of the
functions below, with a bounds check (`w64WordsIn`, `wBytesIn`) around it for
the two that read memory. Those plain functions and bounds checks are what
`ArmTest.lean` runs on the cases recorded from a processor. Without the
instructions (`Arm.haveSha512 = false`) every wrapper but `available` fails
(`wr512_*_undef`). -/

namespace slhdsa

/-- The bounds check of `load_words` (two words), on the length of the slice. -/
def w64WordsIn (n i : Nat) : Bool := 2 ≤ n && i ≤ n - 2

/-- `load_words` without its bounds check. -/
def w64LoadWords (w : List (BitVec 64)) (i : Nat) : Arm.V2 := ⟨w[i]!, w[i + 1]!⟩

/-- `store_words`. -/
def w64StoreWords (a b : Arm.V2) : List (BitVec 64) := [a.e0, a.e1, b.e0, b.e1]

/-- `load_be` without its bounds check. -/
def w64LoadBe (b : List (BitVec 8)) (i : Nat) : Arm.V2 :=
  ⟨Arm.beWord64 b[i]! b[i + 1]! b[i + 2]! b[i + 3]! b[i + 4]! b[i + 5]! b[i + 6]! b[i + 7]!,
    Arm.beWord64 b[i + 8]! b[i + 9]! b[i + 10]! b[i + 11]! b[i + 12]! b[i + 13]! b[i + 14]!
      b[i + 15]!⟩

theorem w64WordsIn_iff (n i : Nat) : w64WordsIn n i = true ↔ 2 ≤ n ∧ i ≤ n - 2 := by
  simp [w64WordsIn]

/-! ## With the instructions -/

section
variable (hw : Arm.haveSha512 = true)
include hw

theorem wr512_add (a b : Arm.V2) : sha512.hw.arm.add a b = ok (Arm.ADD2 a b) := by
  unfold sha512.hw.arm.add; simp only [hw, ↓reduceIte]; rfl
theorem wr512_ext1 (a b : Arm.V2) : sha512.hw.arm.ext1 a b = ok (Arm.EXT1 a b) := by
  unfold sha512.hw.arm.ext1; simp only [hw, ↓reduceIte]; rfl
theorem wr512_sha512h (a b c : Arm.V2) : sha512.hw.arm.sha512h a b c = ok (Arm.SHA512H a b c) := by
  unfold sha512.hw.arm.sha512h; simp only [hw, ↓reduceIte]; rfl
theorem wr512_sha512h2 (a b c : Arm.V2) :
    sha512.hw.arm.sha512h2 a b c = ok (Arm.SHA512H2 a b c) := by
  unfold sha512.hw.arm.sha512h2; simp only [hw, ↓reduceIte]; rfl
theorem wr512_sha512su0 (a b : Arm.V2) : sha512.hw.arm.sha512su0 a b = ok (Arm.SHA512SU0 a b) := by
  unfold sha512.hw.arm.sha512su0; simp only [hw, ↓reduceIte]; rfl
theorem wr512_sha512su1 (a b c : Arm.V2) :
    sha512.hw.arm.sha512su1 a b c = ok (Arm.SHA512SU1 a b c) := by
  unfold sha512.hw.arm.sha512su1; simp only [hw, ↓reduceIte]; rfl

theorem wr512_load_words (w : Slice U64) (i : Usize) :
    sha512.hw.arm.load_words w i =
      if w64WordsIn w.length i.val then ok (w64LoadWords (w.val.map (·.bv)) i.val)
      else fail .panic := by
  unfold sha512.hw.arm.load_words; simp only [hw, ↓reduceIte]
  unfold w64LoadWords
  simp only [w64WordsIn_iff]
  by_cases h : 2 ≤ w.length ∧ i.val ≤ w.length - 2
  · simp only [h, and_self, ↓reduceIte]
    have hl : w.val.length = w.length := rfl
    have g : ∀ k, k < 2 → (w.val.map (·.bv))[i.val + k]! = (w.val[i.val + k]!).bv := by
      intro k hk
      have : i.val + k < w.val.length := by omega
      simp [this]
    have g0 := g 0 (by omega)
    simp only [Nat.add_zero] at g0
    rw [g0, g 1 (by omega)]
    rfl
  · simp only [h, ↓reduceIte]; rfl

theorem wr512_store_words (a b : Arm.V2) :
    ∃ r, sha512.hw.arm.store_words a b = ok r ∧ r.val.map (·.bv) = w64StoreWords a b := by
  unfold sha512.hw.arm.store_words; simp only [hw, ↓reduceIte]
  exact ⟨_, rfl, rfl⟩

theorem wr512_load_be (b : Slice U8) (i : Usize) :
    sha512.hw.arm.load_be b i =
      if wBytesIn b.length i.val then ok (w64LoadBe (b.val.map (·.bv)) i.val)
      else fail .panic := by
  unfold sha512.hw.arm.load_be; simp only [hw, ↓reduceIte]
  unfold w64LoadBe
  simp only [wBytesIn_iff]
  by_cases h : 16 ≤ b.length ∧ i.val ≤ b.length - 16
  · simp only [h, and_self, ↓reduceIte]
    have hl : b.val.length = b.length := rfl
    have g : ∀ k, k < 16 → (b.val.map (·.bv))[i.val + k]! = (b.val[i.val + k]!).bv := by
      intro k hk
      have : i.val + k < b.val.length := by omega
      simp [this]
    have g0 := g 0 (by omega)
    simp only [Nat.add_zero] at g0
    simp only [g0, g 1 (by omega), g 2 (by omega), g 3 (by omega), g 4 (by omega), g 5 (by omega),
      g 6 (by omega), g 7 (by omega), g 8 (by omega), g 9 (by omega), g 10 (by omega),
      g 11 (by omega), g 12 (by omega), g 13 (by omega), g 14 (by omega), g 15 (by omega)]
    rfl
  · simp only [h, ↓reduceIte]; rfl

end

/-! ## Without the instructions

Each of the nine wrappers other than `available` fails, whatever its
arguments. -/

section
variable (hw : Arm.haveSha512 = false)
include hw

theorem wr512_load_words_undef (w : Slice U64) (i : Usize) :
    sha512.hw.arm.load_words w i = fail .undef := by
  simp [sha512.hw.arm.load_words, hw]
theorem wr512_store_words_undef (a b : Arm.V2) : sha512.hw.arm.store_words a b = fail .undef := by
  simp [sha512.hw.arm.store_words, hw]
theorem wr512_load_be_undef (b : Slice U8) (i : Usize) : sha512.hw.arm.load_be b i = fail .undef := by
  simp [sha512.hw.arm.load_be, hw]
theorem wr512_add_undef (a b : Arm.V2) : sha512.hw.arm.add a b = fail .undef := by
  simp [sha512.hw.arm.add, hw]
theorem wr512_ext1_undef (a b : Arm.V2) : sha512.hw.arm.ext1 a b = fail .undef := by
  simp [sha512.hw.arm.ext1, hw]
theorem wr512_sha512h_undef (a b c : Arm.V2) : sha512.hw.arm.sha512h a b c = fail .undef := by
  simp [sha512.hw.arm.sha512h, hw]
theorem wr512_sha512h2_undef (a b c : Arm.V2) : sha512.hw.arm.sha512h2 a b c = fail .undef := by
  simp [sha512.hw.arm.sha512h2, hw]
theorem wr512_sha512su0_undef (a b : Arm.V2) : sha512.hw.arm.sha512su0 a b = fail .undef := by
  simp [sha512.hw.arm.sha512su0, hw]
theorem wr512_sha512su1_undef (a b c : Arm.V2) : sha512.hw.arm.sha512su1 a b c = fail .undef := by
  simp [sha512.hw.arm.sha512su1, hw]

end

end slhdsa
