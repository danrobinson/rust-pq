import Slhdsa.Proofs.Basic
open Aeneas Aeneas.Std Result

/-! The intrinsic wrappers as plain functions.

`Slhdsa/FunsExternal.lean` defines each wrapper of `rust/src/sha256.rs`,
module `hw::arm`, as a function into Aeneas's `Result`. Here each is shown,
on a processor with the instructions (`Arm.haveSha2 = true`), to be a plain
function on lists and bit-vectors: an instruction of `Arm.lean`, or one of the
functions below, with a bounds check (`wWordsIn`, `wBytesIn`) around it for the
four that touch memory. Those plain functions and bounds checks are what
`ArmTest.lean` runs on the cases recorded from a processor, so that test is
about the definitions the proofs use. Without the instructions
(`Arm.haveSha2 = false`) every wrapper fails (`wr_*_undef`).

The proofs of the kernels use these lemmas, through `Compress.lean` and
`ChainLane.lean`. -/

namespace slhdsa

/-- `zero`. -/
def wZero : Arm.V := ⟨0, 0, 0, 0⟩

/-- `pair`. -/
def wPair (a b : BitVec 32) : Arm.V := ⟨a, b, 0, 0⟩

/-- The bounds check of `load_words`, on the length of the slice. -/
def wWordsIn (n i : Nat) : Bool := 4 ≤ n && i ≤ n - 4

/-- The bounds check of `load_be` and `store_be`, on the length of the slice. -/
def wBytesIn (n i : Nat) : Bool := 16 ≤ n && i ≤ n - 16

/-- `load_words` without its bounds check. -/
def wLoadWords (w : List (BitVec 32)) (i : Nat) : Arm.V := ⟨w[i]!, w[i + 1]!, w[i + 2]!, w[i + 3]!⟩

/-- `store_words`. -/
def wStoreWords (a e : Arm.V) : List (BitVec 32) := [a.e0, a.e1, a.e2, a.e3, e.e0, e.e1, e.e2, e.e3]

/-- `load_be` without its bounds check. -/
def wLoadBe (b : List (BitVec 8)) (i : Nat) : Arm.V :=
  ⟨Arm.beWord b[i]! b[i + 1]! b[i + 2]! b[i + 3]!, Arm.beWord b[i + 4]! b[i + 5]! b[i + 6]! b[i + 7]!,
    Arm.beWord b[i + 8]! b[i + 9]! b[i + 10]! b[i + 11]!,
    Arm.beWord b[i + 12]! b[i + 13]! b[i + 14]! b[i + 15]!⟩

/-- The sixteen bytes `store_be` writes. -/
def wBeBytes (v : Arm.V) : List (BitVec 8) :=
  Arm.beBytes v.e0 ++ Arm.beBytes v.e1 ++ Arm.beBytes v.e2 ++ Arm.beBytes v.e3

/-- `store_be` without its bounds check. -/
def wStoreBe (b : List (BitVec 8)) (i : Nat) (v : Arm.V) : List (BitVec 8) :=
  b.take i ++ wBeBytes v ++ b.drop (i + 16)

/-! ## With the instructions -/

theorem wWordsIn_iff (n i : Nat) : wWordsIn n i = true ↔ 4 ≤ n ∧ i ≤ n - 4 := by
  simp [wWordsIn]

theorem wBytesIn_iff (n i : Nat) : wBytesIn n i = true ↔ 16 ≤ n ∧ i ≤ n - 16 := by
  simp [wBytesIn]

section
variable (hw : Arm.haveSha2 = true)
include hw

theorem wr_zero : sha256.hw.arm.zero = ok wZero := by
  unfold sha256.hw.arm.zero; simp only [hw, ↓reduceIte]; rfl
theorem wr_pair (a b : U32) : sha256.hw.arm.pair a b = ok (wPair a.bv b.bv) := by
  unfold sha256.hw.arm.pair; simp only [hw, ↓reduceIte]; rfl

theorem wr_add (a b : Arm.V) : sha256.hw.arm.add a b = ok (Arm.ADD a b) := by
  unfold sha256.hw.arm.add; simp only [hw, ↓reduceIte]; rfl
theorem wr_or (a b : Arm.V) : sha256.hw.arm.or a b = ok (Arm.ORR a b) := by
  unfold sha256.hw.arm.or; simp only [hw, ↓reduceIte]; rfl
theorem wr_and (a b : Arm.V) : sha256.hw.arm.and a b = ok (Arm.AND a b) := by
  unfold sha256.hw.arm.and; simp only [hw, ↓reduceIte]; rfl
theorem wr_shr16 (a : Arm.V) : sha256.hw.arm.shr16 a = ok (Arm.USHR a 16) := by
  unfold sha256.hw.arm.shr16; simp only [hw, ↓reduceIte]; rfl
theorem wr_shl16 (a : Arm.V) : sha256.hw.arm.shl16 a = ok (Arm.SHL a 16) := by
  unfold sha256.hw.arm.shl16; simp only [hw, ↓reduceIte]; rfl
theorem wr_ext2 (a b : Arm.V) : sha256.hw.arm.ext2 a b = ok (Arm.EXT2 a b) := by
  unfold sha256.hw.arm.ext2; simp only [hw, ↓reduceIte]; rfl
theorem wr_ext3 (a b : Arm.V) : sha256.hw.arm.ext3 a b = ok (Arm.EXT3 a b) := by
  unfold sha256.hw.arm.ext3; simp only [hw, ↓reduceIte]; rfl
theorem wr_sha256h (abcd efgh wk : Arm.V) :
    sha256.hw.arm.sha256h abcd efgh wk = ok (Arm.SHA256H abcd efgh wk) := by
  unfold sha256.hw.arm.sha256h; simp only [hw, ↓reduceIte]; rfl
theorem wr_sha256h2 (efgh abcd wk : Arm.V) :
    sha256.hw.arm.sha256h2 efgh abcd wk = ok (Arm.SHA256H2 efgh abcd wk) := by
  unfold sha256.hw.arm.sha256h2; simp only [hw, ↓reduceIte]; rfl
theorem wr_sha256su0 (a b : Arm.V) : sha256.hw.arm.sha256su0 a b = ok (Arm.SHA256SU0 a b) := by
  unfold sha256.hw.arm.sha256su0; simp only [hw, ↓reduceIte]; rfl
theorem wr_sha256su1 (a b c : Arm.V) :
    sha256.hw.arm.sha256su1 a b c = ok (Arm.SHA256SU1 a b c) := by
  unfold sha256.hw.arm.sha256su1; simp only [hw, ↓reduceIte]; rfl

theorem wr_load_words (w : Slice U32) (i : Usize) :
    sha256.hw.arm.load_words w i =
      if wWordsIn w.length i.val then ok (wLoadWords (w.val.map (·.bv)) i.val)
      else fail .panic := by
  unfold sha256.hw.arm.load_words; simp only [hw, ↓reduceIte]
  unfold wLoadWords
  simp only [wWordsIn_iff]
  by_cases h : 4 ≤ w.length ∧ i.val ≤ w.length - 4
  · simp only [h, and_self, ↓reduceIte]
    have hl : w.val.length = w.length := rfl
    have g : ∀ k, k < 4 → (w.val.map (·.bv))[i.val + k]! = (w.val[i.val + k]!).bv := by
      intro k hk
      have : i.val + k < w.val.length := by omega
      simp [this]
    have g0 := g 0 (by omega)
    simp only [Nat.add_zero] at g0
    rw [g0, g 1 (by omega), g 2 (by omega), g 3 (by omega)]
    rfl
  · simp only [h, ↓reduceIte]; rfl

theorem wr_store_words (a e : Arm.V) :
    ∃ r, sha256.hw.arm.store_words a e = ok r ∧ r.val.map (·.bv) = wStoreWords a e := by
  unfold sha256.hw.arm.store_words; simp only [hw, ↓reduceIte]
  exact ⟨_, rfl, rfl⟩

theorem wr_load_be (b : Slice U8) (i : Usize) :
    sha256.hw.arm.load_be b i =
      if wBytesIn b.length i.val then ok (wLoadBe (b.val.map (·.bv)) i.val)
      else fail .panic := by
  unfold sha256.hw.arm.load_be; simp only [hw, ↓reduceIte]
  unfold wLoadBe
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

theorem wr_store_be (b : Slice U8) (i : Usize) (v : Arm.V) :
    (wBytesIn b.length i.val →
      ∃ r, sha256.hw.arm.store_be b i v = ok r ∧
        r.val.map (·.bv) = wStoreBe (b.val.map (·.bv)) i.val v) ∧
    (¬ wBytesIn b.length i.val → sha256.hw.arm.store_be b i v = fail .panic) := by
  simp only [wBytesIn_iff]
  constructor
  · intro h
    refine ⟨b.setSlice! i.val (sha256.hw.arm.be_bytes v), by simp [sha256.hw.arm.store_be, hw, h], ?_⟩
    have hl : b.val.length = b.length := rfl
    have hb : (sha256.hw.arm.be_bytes v).length = 16 := by
      simp [sha256.hw.arm.be_bytes, Arm.beBytes]
    have hm : (sha256.hw.arm.be_bytes v).map (·.bv) = wBeBytes v := by
      simp [sha256.hw.arm.be_bytes, wBeBytes, Arm.beBytes]
    have hi : i.val + 16 ≤ b.val.length := by omega
    have hmin : min 16 (b.val.length - i.val) = 16 := by omega
    rw [Slice.setSlice!_val, wStoreBe, ← hm]
    simp only [List.setSlice!, hb, hmin, List.map_append, List.map_take, List.map_drop]
    congr 2
  · intro h
    simp [sha256.hw.arm.store_be, hw, h]

end

/-! ## Without the instructions

Each of the seventeen wrappers fails, whatever its arguments. -/

section
variable (hw : Arm.haveSha2 = false)
include hw

theorem wr_zero_undef : sha256.hw.arm.zero = fail .undef := by
  simp [sha256.hw.arm.zero, hw]
theorem wr_pair_undef (a b : U32) : sha256.hw.arm.pair a b = fail .undef := by
  simp [sha256.hw.arm.pair, hw]
theorem wr_load_words_undef (w : Slice U32) (i : Usize) :
    sha256.hw.arm.load_words w i = fail .undef := by
  simp [sha256.hw.arm.load_words, hw]
theorem wr_store_words_undef (a e : Arm.V) : sha256.hw.arm.store_words a e = fail .undef := by
  simp [sha256.hw.arm.store_words, hw]
theorem wr_load_be_undef (b : Slice U8) (i : Usize) : sha256.hw.arm.load_be b i = fail .undef := by
  simp [sha256.hw.arm.load_be, hw]
theorem wr_store_be_undef (b : Slice U8) (i : Usize) (v : Arm.V) :
    sha256.hw.arm.store_be b i v = fail .undef := by
  simp [sha256.hw.arm.store_be, hw]
theorem wr_add_undef (a b : Arm.V) : sha256.hw.arm.add a b = fail .undef := by
  simp [sha256.hw.arm.add, hw]
theorem wr_or_undef (a b : Arm.V) : sha256.hw.arm.or a b = fail .undef := by
  simp [sha256.hw.arm.or, hw]
theorem wr_and_undef (a b : Arm.V) : sha256.hw.arm.and a b = fail .undef := by
  simp [sha256.hw.arm.and, hw]
theorem wr_shr16_undef (a : Arm.V) : sha256.hw.arm.shr16 a = fail .undef := by
  simp [sha256.hw.arm.shr16, hw]
theorem wr_shl16_undef (a : Arm.V) : sha256.hw.arm.shl16 a = fail .undef := by
  simp [sha256.hw.arm.shl16, hw]
theorem wr_ext2_undef (a b : Arm.V) : sha256.hw.arm.ext2 a b = fail .undef := by
  simp [sha256.hw.arm.ext2, hw]
theorem wr_ext3_undef (a b : Arm.V) : sha256.hw.arm.ext3 a b = fail .undef := by
  simp [sha256.hw.arm.ext3, hw]
theorem wr_sha256h_undef (a b c : Arm.V) : sha256.hw.arm.sha256h a b c = fail .undef := by
  simp [sha256.hw.arm.sha256h, hw]
theorem wr_sha256h2_undef (a b c : Arm.V) : sha256.hw.arm.sha256h2 a b c = fail .undef := by
  simp [sha256.hw.arm.sha256h2, hw]
theorem wr_sha256su0_undef (a b : Arm.V) : sha256.hw.arm.sha256su0 a b = fail .undef := by
  simp [sha256.hw.arm.sha256su0, hw]
theorem wr_sha256su1_undef (a b c : Arm.V) : sha256.hw.arm.sha256su1 a b c = fail .undef := by
  simp [sha256.hw.arm.sha256su1, hw]

end

end slhdsa
