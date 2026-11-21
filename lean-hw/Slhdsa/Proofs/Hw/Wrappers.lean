import Slhdsa.Proofs.Basic
open Aeneas Aeneas.Std Result

/-! The intrinsic wrappers as plain functions.

`Slhdsa/FunsExternal.lean` defines each wrapper of `rust/src/sha256.rs`,
module `hw::arm`, as a function into Aeneas's `Result`. Here each is shown to
be a bounds check (for the four that touch memory) around a plain function on
lists and bit-vectors. Those plain functions are what `ArmTest.lean` runs on
the cases recorded from a processor, so that test is about the definitions the
proofs use. -/

namespace slhdsa

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

theorem wr_zero : sha256.hw.arm.zero = ok (⟨0, 0, 0, 0⟩ : Arm.V) := rfl

theorem wr_pair (a b : U32) : sha256.hw.arm.pair a b = ok (⟨a.bv, b.bv, 0, 0⟩ : Arm.V) := rfl

theorem wr_add (a b : Arm.V) : sha256.hw.arm.add a b = ok (Arm.ADD a b) := rfl
theorem wr_or (a b : Arm.V) : sha256.hw.arm.or a b = ok (Arm.ORR a b) := rfl
theorem wr_and (a b : Arm.V) : sha256.hw.arm.and a b = ok (Arm.AND a b) := rfl
theorem wr_shr16 (a : Arm.V) : sha256.hw.arm.shr16 a = ok (Arm.USHR a 16) := rfl
theorem wr_shl16 (a : Arm.V) : sha256.hw.arm.shl16 a = ok (Arm.SHL a 16) := rfl
theorem wr_ext2 (a b : Arm.V) : sha256.hw.arm.ext2 a b = ok (Arm.EXT2 a b) := rfl
theorem wr_ext3 (a b : Arm.V) : sha256.hw.arm.ext3 a b = ok (Arm.EXT3 a b) := rfl
theorem wr_sha256h (abcd efgh wk : Arm.V) :
    sha256.hw.arm.sha256h abcd efgh wk = ok (Arm.SHA256H abcd efgh wk) := rfl
theorem wr_sha256h2 (efgh abcd wk : Arm.V) :
    sha256.hw.arm.sha256h2 efgh abcd wk = ok (Arm.SHA256H2 efgh abcd wk) := rfl
theorem wr_sha256su0 (a b : Arm.V) : sha256.hw.arm.sha256su0 a b = ok (Arm.SHA256SU0 a b) := rfl
theorem wr_sha256su1 (a b c : Arm.V) :
    sha256.hw.arm.sha256su1 a b c = ok (Arm.SHA256SU1 a b c) := rfl

theorem wr_load_words (w : Slice U32) (i : Usize) :
    sha256.hw.arm.load_words w i =
      if 4 ≤ w.length ∧ i.val ≤ w.length - 4 then ok (wLoadWords (w.val.map (·.bv)) i.val)
      else fail .panic := by
  unfold sha256.hw.arm.load_words wLoadWords
  split
  · rename_i h
    have hl : w.val.length = w.length := rfl
    have g : ∀ k, k < 4 → (w.val.map (·.bv))[i.val + k]! = (w.val[i.val + k]!).bv := by
      intro k hk
      have : i.val + k < w.val.length := by omega
      simp [this]
    have g0 := g 0 (by omega)
    simp only [Nat.add_zero] at g0
    rw [g0, g 1 (by omega), g 2 (by omega), g 3 (by omega)]
    rfl
  · rfl

theorem wr_store_words (a e : Arm.V) :
    ∃ r, sha256.hw.arm.store_words a e = ok r ∧ r.val.map (·.bv) = wStoreWords a e :=
  ⟨_, rfl, rfl⟩

theorem wr_load_be (b : Slice U8) (i : Usize) :
    sha256.hw.arm.load_be b i =
      if 16 ≤ b.length ∧ i.val ≤ b.length - 16 then ok (wLoadBe (b.val.map (·.bv)) i.val)
      else fail .panic := by
  unfold sha256.hw.arm.load_be wLoadBe
  split
  · rename_i h
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
  · rfl

theorem wr_store_be (b : Slice U8) (i : Usize) (v : Arm.V) :
    (16 ≤ b.length ∧ i.val ≤ b.length - 16 →
      ∃ r, sha256.hw.arm.store_be b i v = ok r ∧
        r.val.map (·.bv) = wStoreBe (b.val.map (·.bv)) i.val v) ∧
    (¬ (16 ≤ b.length ∧ i.val ≤ b.length - 16) → sha256.hw.arm.store_be b i v = fail .panic) := by
  constructor
  · intro h
    refine ⟨b.setSlice! i.val (sha256.hw.arm.be_bytes v), by simp [sha256.hw.arm.store_be, h], ?_⟩
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
    simp [sha256.hw.arm.store_be, h]

end slhdsa
