import Slhdsa.Proofs.Hash
import Slhdsa.Proofs.Hw.Rounds
import Mathlib.Tactic.IntervalCases
open Aeneas Aeneas.Std Result

/-! A pure model of one chain of the hardware chain kernel, generic in the
hash length `n` ∈ {16, 24, 32}: the block as its fixed bytes, a counter and an
`n`-byte value; one hash step; and its relation to `stepBlock` / `runBlock`.

This is `../../lean-hw/Slhdsa/Proofs/Hw/ChainModel.lean` generalised. The
value occupies block bytes 22..22 + n. The kernel holds it in two vectors: `x`,
bytes 22..38 (all of the value for n = 16), and `xb`, bytes 38..54, of which
the first n − 16 bytes are value (for n = 24 its last two words are zero,
`Norm`; for n = 16 it is not used). -/

namespace slhdsa
open Spec.SHA256

set_option linter.unusedSimpArgs false

/-- The hash lengths the kernel handles. -/
def KN (n : Nat) : Prop := n = 16 ∨ n = 24 ∨ n = 32

theorem KN_le {n : Nat} (h : KN n) : 16 ≤ n ∧ n ≤ 32 := by
  rcases h with rfl | rfl | rfl <;> omega

/-! ## Bytes of vectors -/

/-- The sixteen big-endian bytes of a vector. -/
def vbytes (v : Arm.V) : Spec.Bytes :=
  Arm.beBytes v.e0 ++ Arm.beBytes v.e1 ++ Arm.beBytes v.e2 ++ Arm.beBytes v.e3

@[simp] theorem beBytes_length (w : Word) : (Arm.beBytes w).length = 4 := rfl

@[simp] theorem vbytes_length (v : Arm.V) : (vbytes v).length = 16 := rfl

theorem toByte_bv (w : Word) : Spec.toByte w.toNat 4 = Arm.beBytes w := by
  rw [toByte4_eq]
  simp [Arm.beBytes, BitVec.extractLsb']

theorem toByte_ofNat (c : Nat) (hc : c < 2 ^ 32) :
    Spec.toByte c 4 = Arm.beBytes (BitVec.ofNat 32 c) := by
  rw [← toByte_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

theorem getElem!_app {α} [Inhabited α] (A C : List α) (i : Nat) :
    (A ++ C)[i]! = if i < A.length then A[i]! else C[i - A.length]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append]
  split <;> rfl

theorem getElem!_take' {α} [Inhabited α] (A : List α) (n i : Nat) (h : i < n) :
    (A.take n)[i]! = A[i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take, h, ite_true]

theorem getElem!_drop' {α} [Inhabited α] (A : List α) (n i : Nat) :
    (A.drop n)[i]! = A[n + i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_drop]

/-! ## Vector constants -/

/-- `MASK1`, `MASK2`, `MASK2_24`, `ALL`, `LOW2`, `HIGH2` as vectors, and the zero vector. -/
def mask1V : Arm.V := ⟨4294901760#32, 0#32, 0#32, 0#32⟩
def mask2V : Arm.V := ⟨0#32, 65535#32, 4294967295#32, 4294967295#32⟩
def mask224V : Arm.V := ⟨0#32, 0#32, 0#32, 65535#32⟩
def allV : Arm.V := ⟨4294967295#32, 4294967295#32, 4294967295#32, 4294967295#32⟩
def low2V : Arm.V := ⟨4294967295#32, 4294967295#32, 0#32, 0#32⟩
def high2V : Arm.V := ⟨0#32, 0#32, 4294967295#32, 4294967295#32⟩
def zV : Arm.V := ⟨0#32, 0#32, 0#32, 0#32⟩

/-- The mask of the fixed part of W8..W11 (`k2` in `enter`). -/
def k2V (n : Nat) : Arm.V := if n = 16 then mask2V else if n = 24 then mask224V else zV
/-- The mask of the fixed part of W12..W15 (`k3`). -/
def k3V (n : Nat) : Arm.V := if n = 32 then mask2V else allV
/-- The mask of the value's words in bytes 38..54 (`kb`, n > 16). -/
def kbV (n : Nat) : Arm.V := if n = 24 then low2V else allV
/-- The mask of what follows the value in bytes 38..54 (`kt`, n > 16). -/
def ktV (n : Nat) : Arm.V := if n = 24 then high2V else zV

theorem and_ones (w : BitVec 32) : w &&& 4294967295#32 = w := by
  have : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes]

theorem and_zero' (w : BitVec 32) : w &&& 0#32 = 0#32 := BitVec.and_zero

theorem or_zero' (w : BitVec 32) : w ||| 0#32 = w := BitVec.or_zero

theorem zero_or' (w : BitVec 32) : 0#32 ||| w = w := BitVec.zero_or

/-! ## The block of a chain -/

/-- The `n` bytes of value held by `x` (bytes 22..38) and `xb` (bytes 38..54). -/
def valB (n : Nat) (x xb : Arm.V) : Spec.Bytes := (vbytes x ++ vbytes xb).take n

theorem valB_length (n : Nat) (hn : n ≤ 32) (x xb : Arm.V) : (valB n x xb).length = n := by
  simp [valB]; omega

/-- The block `B` with counter `c` at bytes 18..22 and the value of `x`, `xb`
at bytes 22..22 + n. -/
def setBlk (n : Nat) (B : Spec.Bytes) (c : Nat) (x xb : Arm.V) : Spec.Bytes :=
  B.take 18 ++ Spec.toByte c 4 ++ valB n x xb ++ B.drop (22 + n)

theorem toByte_length4 (c : Nat) : (Spec.toByte c 4).length = 4 := by simp [Spec.toByte]

theorem setBlk_length (n : Nat) (hn : n ≤ 32) (B : Spec.Bytes) (hB : B.length = 64) (c : Nat)
    (x xb : Arm.V) : (setBlk n B c x xb).length = 64 := by
  simp [setBlk, toByte_length4, hB, valB_length n hn]; omega

theorem setBlk_take18 (n : Nat) (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x xb : Arm.V) :
    (setBlk n B c x xb).take 18 = B.take 18 := by
  simp only [setBlk, List.append_assoc]
  exact List.take_left' (by simp [hB])

theorem setBlk_take22 (n : Nat) (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x xb : Arm.V) :
    (setBlk n B c x xb).take 22 = B.take 18 ++ Spec.toByte c 4 := by
  simp only [setBlk, List.append_assoc]
  rw [← List.append_assoc]
  exact List.take_left' (by simp [hB, toByte_length4])

theorem setBlk_drop22 (n : Nat) (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x xb : Arm.V) :
    (setBlk n B c x xb).drop 22 = valB n x xb ++ B.drop (22 + n) := by
  simp only [setBlk, List.append_assoc]
  rw [← List.append_assoc]
  exact List.drop_left' (by simp [hB, toByte_length4])

theorem setBlk_dropN (n : Nat) (hn : n ≤ 32) (B : Spec.Bytes) (hB : B.length = 64) (c : Nat)
    (x xb : Arm.V) : (setBlk n B c x xb).drop (22 + n) = B.drop (22 + n) := by
  simp only [setBlk]
  exact List.drop_left' (by simp [hB, toByte_length4, valB_length n hn]; omega)

/-- What `xb` becomes after a hash whose second state half (plus the initial
one) is `e`: unchanged for n = 16, its first two words for n = 24, all of it
for n = 32. -/
def xbNext (n : Nat) (e xb : Arm.V) : Arm.V :=
  if n = 16 then xb else if n = 24 then Arm.AND e low2V else e

/-- The value after one step from value `x`, `xb` with counter `c`: the first
`n / 4` words of the compression of the block. -/
def hval (n : Nat) (st : List Word) (B : Spec.Bytes) (c : Nat) (x xb : Arm.V) : Arm.V × Arm.V :=
  (vOf (compress st (setBlk n B c x xb)) 0, xbNext n (vOf (compress st (setBlk n B c x xb)) 4) xb)

theorem ser_takeN (n : Nat) (hn : KN n) (l : List Word) (hl : l.length = 8) (xb : Arm.V) :
    (ser l).take n = valB n (vOf l 0) (xbNext n (vOf l 4) xb) := by
  match l, hl with
  | a :: b :: c :: d :: e :: f :: g :: h :: [], _ =>
    rcases hn with rfl | rfl | rfl <;>
      simp [ser, vOf, vbytes, valB, xbNext, toByte_bv, Arm.beBytes, Arm.AND, low2V, and_ones]

theorem stepBlock_setBlk (n : Nat) (hn : KN n) (st : List Word) (B : Spec.Bytes) (hB : B.length = 64)
    (c t : Nat) (x xb : Arm.V) :
    stepBlock n st (setBlk n B c x xb) t = setBlk n B t (hval n st B t x xb).1 (hval n st B t x xb).2 := by
  have hn32 := (KN_le hn).2
  unfold stepBlock
  simp only []
  rw [setBlk_take18 _ _ hB, setBlk_drop22 _ _ hB]
  have e : B.take 18 ++ Spec.toByte t 4 ++ (valB n x xb ++ B.drop (22 + n)) = setBlk n B t x xb := by
    simp [setBlk]
  rw [e, setBlk_take22 _ _ hB, setBlk_dropN _ hn32 _ hB, ser_takeN n hn _ (sha_compress_length _ _) xb]
  simp [setBlk, hval]

theorem stepBlock_congr (n : Nat) (st : List Word) (B B' : Spec.Bytes) (t : Nat)
    (h1 : B.take 18 = B'.take 18) (h2 : B.drop 22 = B'.drop 22) :
    stepBlock n st B t = stepBlock n st B' t := by
  unfold stepBlock; rw [h1, h2]

/-! ## Bit-level facts -/

/-- Bit-by-bit equality of 32-bit words built from bytes, shifts, `and`, `or`. -/
macro "bvtac" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  try simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat rw [BitVec.getLsbD_append]
  try simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp))

theorem beBytes_concat (a b c d : BitVec 8) : Arm.beBytes (a ++ b ++ c ++ d) = [a, b, c, d] := by
  simp only [Arm.beBytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bvtac

theorem beBytes_word (B : Spec.Bytes) (i : Nat) :
    Arm.beBytes (word B i) = [B[i]!, B[i + 1]!, B[i + 2]!, B[i + 3]!] := by
  simp only [word, beBytes_concat]

theorem take16_explicit (B : Spec.Bytes) (i : Nat) (h : i + 16 ≤ B.length) :
    (B.drop i).take 16 = [B[i]!, B[i + 1]!, B[i + 2]!, B[i + 3]!, B[i + 4]!, B[i + 5]!, B[i + 6]!,
      B[i + 7]!, B[i + 8]!, B[i + 9]!, B[i + 10]!, B[i + 11]!, B[i + 12]!, B[i + 13]!, B[i + 14]!,
      B[i + 15]!] := by
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    have hn : n < 16 := by simpa using h2
    simp only [List.getElem_take, List.getElem_drop]
    rw [← getElem!_eq _ _ (by omega)]
    interval_cases n <;> rfl

theorem vbytes_beV (B : Spec.Bytes) (i : Nat) (h : i + 16 ≤ B.length) :
    vbytes (beV B i) = (B.drop i).take 16 := by
  rw [take16_explicit _ _ h]
  simp only [vbytes, beV, beBytes_word]
  simp [Nat.add_assoc]

/-- The value's second vector as `enter` loads it: zero for n = 16, else
bytes 38..54 masked to the value's words. -/
def xb0 (n : Nat) (B : Spec.Bytes) : Arm.V := if n = 16 then zV else Arm.AND (beV B 38) (kbV n)

/-- What `enter` saves of bytes 38..54 for `leave`: for n = 24 the bytes 46..54
that follow the value; zero otherwise. -/
def tailV (n : Nat) (B : Spec.Bytes) : Arm.V := if n = 16 then zV else Arm.AND (beV B 38) (ktV n)

theorem vbytes_and_low2 (v : Arm.V) : (vbytes (Arm.AND v low2V)).take 8 = (vbytes v).take 8 := by
  obtain ⟨a, b, c, d⟩ := v
  simp [vbytes, Arm.AND, low2V, and_ones, Arm.beBytes]

theorem vbytes_and_all (v : Arm.V) : Arm.AND v allV = v := by
  obtain ⟨a, b, c, d⟩ := v
  simp [Arm.AND, allV, and_ones]

theorem drop_split (B : Spec.Bytes) (i a : Nat) : B.drop i = (B.drop i).take a ++ B.drop (i + a) := by
  conv => lhs; rw [← List.take_append_drop a (B.drop i)]
  rw [List.drop_drop]

theorem valB_first (n : Nat) (hn : KN n) (B : Spec.Bytes) (hB : B.length = 64) :
    valB n (beV B 22) (xb0 n B) = (B.drop 22).take n := by
  have h22 := vbytes_beV B 22 (by omega)
  have h38 := vbytes_beV B 38 (by omega)
  have hl : (vbytes (beV B 22)).length = 16 := vbytes_length _
  rcases hn with rfl | rfl | rfl
  · simp only [valB, xb0, if_pos rfl]
    rw [List.take_append, List.take_of_length_le (by omega), hl, Nat.sub_self,
      List.take_zero, List.append_nil, h22]
  · simp only [valB, xb0, kbV, show (24 : Nat) ≠ 16 by omega, ite_false, ite_true]
    rw [List.take_append, List.take_of_length_le (by omega), hl,
      show 24 - 16 = 8 by omega, vbytes_and_low2, h22, h38, List.take_take,
      show min 8 16 = 8 by omega, show (24 : Nat) = 16 + 8 from rfl, List.take_add, List.drop_drop]
  · simp only [valB, xb0, kbV, show (32 : Nat) ≠ 16 by omega, show (32 : Nat) ≠ 24 by omega,
      ite_false, vbytes_and_all]
    rw [List.take_of_length_le (by simp), h22, h38, show (32 : Nat) = 16 + 16 from rfl,
      List.take_add, List.drop_drop]

theorem drop22_split (n : Nat) (hn : KN n) (B : Spec.Bytes) (hB : B.length = 64) :
    B.drop 22 = valB n (beV B 22) (xb0 n B) ++ B.drop (22 + n) := by
  rw [valB_first n hn B hB, ← List.drop_drop, List.take_append_drop]

theorem stepBlock_first (n : Nat) (hn : KN n) (st : List Word) (B : Spec.Bytes) (hB : B.length = 64)
    (s : Nat) :
    stepBlock n st B s = setBlk n B s (hval n st B s (beV B 22) (xb0 n B)).1
      (hval n st B s (beV B 22) (xb0 n B)).2 := by
  rw [stepBlock_congr n st B (setBlk n B s (beV B 22) (xb0 n B)) s (setBlk_take18 _ _ hB _ _ _).symm
    (by rw [setBlk_drop22 _ _ hB, drop22_split n hn _ hB]), stepBlock_setBlk n hn _ _ hB]

/-- The values of a chain started from block `B` at step `s`: `Yseq k` after `k` steps. -/
def Yseq (n : Nat) (st : List Word) (B : Spec.Bytes) (s : Nat) : Nat → Arm.V × Arm.V
  | 0 => (beV B 22, xb0 n B)
  | k + 1 => hval n st B (s + k) (Yseq n st B s k).1 (Yseq n st B s k).2

theorem runBlock_Yseq (n : Nat) (hn : KN n) (st : List Word) (B : Spec.Bytes) (hB : B.length = 64)
    (s : Nat) : ∀ k, runBlock n st B s (s + (k + 1)) =
      setBlk n B (s + k) (Yseq n st B s (k + 1)).1 (Yseq n st B s (k + 1)).2
  | 0 => by rw [runBlock_one, stepBlock_first n hn _ _ hB]; rfl
  | k + 1 => by
    rw [runBlock_succ, runBlock_Yseq n hn st B hB s k, stepBlock_setBlk n hn _ _ hB]
    rfl

/-- For n = 24 the upper two words of `xb` are zero. -/
def Norm (n : Nat) (xb : Arm.V) : Prop := n = 24 → xb.e2 = 0#32 ∧ xb.e3 = 0#32

theorem xbNext_norm (n : Nat) (e xb : Arm.V) (h : Norm n xb) : Norm n (xbNext n e xb) := by
  intro h24
  subst h24
  simp [xbNext, Arm.AND, low2V]

theorem xb0_norm (n : Nat) (B : Spec.Bytes) : Norm n (xb0 n B) := by
  intro h24
  subst h24
  simp [xb0, kbV, Arm.AND, low2V]

theorem Yseq_norm (n : Nat) (st : List Word) (B : Spec.Bytes) (s : Nat) :
    ∀ k, Norm n (Yseq n st B s k).2
  | 0 => xb0_norm n B
  | k + 1 => xbNext_norm _ _ _ (Yseq_norm n st B s k)

/-! ## The words the kernel rebuilds -/

/-- W4..W7 as `lane_step` rebuilds them from `c1`, the counter `T` and the value `x`. -/
def mkM1 (c1 : Arm.V) (T : Word) (x : Arm.V) : Arm.V :=
  Arm.ORR (Arm.ORR c1 ⟨T >>> 16, T <<< 16, 0#32, 0#32⟩)
    (Arm.ORR (Arm.EXT3 zV (Arm.USHR x 16)) (Arm.EXT2 zV (Arm.SHL x 16)))

/-- W8..W11 as `lane_step` rebuilds them from `c2` and the value `x`, `xb`. -/
def mkM2 (n : Nat) (c2 : Arm.V) (x xb : Arm.V) : Arm.V :=
  if n = 16 then Arm.ORR c2 (Arm.ORR (Arm.EXT2 (Arm.SHL x 16) zV) (Arm.EXT3 (Arm.USHR x 16) zV))
  else Arm.ORR c2 (Arm.ORR (Arm.EXT2 (Arm.SHL x 16) (Arm.SHL xb 16))
    (Arm.EXT3 (Arm.USHR x 16) (Arm.USHR xb 16)))

/-- W12..W15 as `lane_step` rebuilds them from `c3` and `xb`. -/
def mkM3 (n : Nat) (c3 : Arm.V) (xb : Arm.V) : Arm.V :=
  if n = 16 then c3 else if n = 24 then c3
  else Arm.ORR c3 (Arm.ORR (Arm.EXT2 (Arm.SHL xb 16) zV) (Arm.EXT3 (Arm.USHR xb 16) zV))

theorem setBlk_getElem! (n : Nat) (hn : n ≤ 32) (B : Spec.Bytes) (hB : B.length = 64) (c : Nat)
    (x xb : Arm.V) (j : Nat) :
    (setBlk n B c x xb)[j]! = if j < 18 then B[j]! else if j < 22 then (Spec.toByte c 4)[j - 18]!
      else if j < 22 + n then (vbytes x ++ vbytes xb)[j - 22]! else B[j]! := by
  rw [setBlk, getElem!_app, getElem!_app, getElem!_app]
  have l1 : (B.take 18).length = 18 := by simp [hB]
  simp only [List.length_append, l1, toByte_length4, valB_length n hn]
  split_ifs <;> first
    | omega
    | rfl
    | exact getElem!_take' _ _ _ (by omega)
    | (rw [valB, getElem!_take' _ _ _ (by omega)])
    | (rw [getElem!_drop', Nat.add_sub_cancel' (by omega)])

theorem word_setBlk_lo (n : Nat) (hn : n ≤ 32) (B : Spec.Bytes) (hB : B.length = 64) (c : Nat)
    (x xb : Arm.V) (j : Nat) (hj : j + 3 < 18) : word (setBlk n B c x xb) j = word B j := by
  simp only [word, setBlk_getElem! n hn _ hB]
  simp only [show j < 18 by omega, show j + 1 < 18 by omega, show j + 2 < 18 by omega,
    show j + 3 < 18 by omega, ite_true]

theorem beV_setBlk_0 (n : Nat) (hn : n ≤ 32) (B : Spec.Bytes) (hB : B.length = 64) (c : Nat)
    (x xb : Arm.V) : beV (setBlk n B c x xb) 0 = beV B 0 := by
  simp only [beV, word_setBlk_lo n hn _ hB _ _ _ _ (by omega : 0 + 3 < 18),
    word_setBlk_lo n hn _ hB _ _ _ _ (by omega : 0 + 4 + 3 < 18),
    word_setBlk_lo n hn _ hB _ _ _ _ (by omega : 0 + 8 + 3 < 18),
    word_setBlk_lo n hn _ hB _ _ _ _ (by omega : 0 + 12 + 3 < 18)]

theorem beV_setBlk_16 (n : Nat) (hn : KN n) (B : Spec.Bytes) (hB : B.length = 64) (c : Nat)
    (hc : c < 2 ^ 32) (x xb : Arm.V) :
    beV (setBlk n B c x xb) 16 = mkM1 (Arm.AND (beV B 16) mask1V) (BitVec.ofNat 32 c) x := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := xb
  have hn32 := (KN_le hn).2
  rcases hn with rfl | rfl | rfl <;>
  · simp only [beV, word, setBlk_getElem! _ hn32 _ hB, toByte_ofNat c hc]
    simp only [vbytes, Arm.beBytes, mkM1, Arm.ORR, Arm.AND, Arm.EXT2, Arm.EXT3, Arm.USHR, Arm.SHL,
      mask1V, zV]
    simp only [Arm.V.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp; bvtac)

theorem beV_setBlk_32 (n : Nat) (hn : KN n) (B : Spec.Bytes) (hB : B.length = 64) (c : Nat)
    (x xb : Arm.V) (hnorm : Norm n xb) :
    beV (setBlk n B c x xb) 32 = mkM2 n (Arm.AND (beV B 32) (k2V n)) x xb := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := xb
  have hn32 := (KN_le hn).2
  rcases hn with rfl | rfl | rfl
  · simp only [beV, word, setBlk_getElem! _ hn32 _ hB]
    simp only [vbytes, Arm.beBytes, mkM2, k2V, Arm.ORR, Arm.AND, Arm.EXT2, Arm.EXT3, Arm.USHR,
      Arm.SHL, mask2V, zV, ite_true]
    simp only [Arm.V.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp; bvtac)
  · obtain ⟨h2, h3⟩ := hnorm rfl
    simp only at h2 h3
    subst h2 h3
    simp only [beV, word, setBlk_getElem! _ hn32 _ hB]
    simp only [vbytes, Arm.beBytes, mkM2, k2V, Arm.ORR, Arm.AND, Arm.EXT2, Arm.EXT3, Arm.USHR,
      Arm.SHL, mask224V, zV, show (24 : Nat) ≠ 16 by omega, ite_true, ite_false]
    simp only [Arm.V.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp; bvtac)
  · simp only [beV, word, setBlk_getElem! _ hn32 _ hB]
    simp only [vbytes, Arm.beBytes, mkM2, k2V, Arm.ORR, Arm.AND, Arm.EXT2, Arm.EXT3, Arm.USHR,
      Arm.SHL, zV, show (32 : Nat) ≠ 16 by omega, show (32 : Nat) ≠ 24 by omega, ite_false]
    simp only [Arm.V.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp; bvtac)

theorem beV_setBlk_48 (n : Nat) (hn : KN n) (B : Spec.Bytes) (hB : B.length = 64) (c : Nat)
    (x xb : Arm.V) :
    beV (setBlk n B c x xb) 48 = mkM3 n (Arm.AND (beV B 48) (k3V n)) xb := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := xb
  have hn32 := (KN_le hn).2
  rcases hn with rfl | rfl | rfl
  · simp only [beV, word, setBlk_getElem! _ hn32 _ hB]
    simp only [mkM3, k3V, Arm.AND, allV, show (16 : Nat) ≠ 32 by omega, ite_true, ite_false]
    simp only [Arm.V.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp; bvtac)
  · simp only [beV, word, setBlk_getElem! _ hn32 _ hB]
    simp only [mkM3, k3V, Arm.AND, allV, show (24 : Nat) ≠ 32 by omega,
      show (24 : Nat) ≠ 16 by omega, ite_true, ite_false]
    simp only [Arm.V.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp; bvtac)
  · simp only [beV, word, setBlk_getElem! _ hn32 _ hB]
    simp only [vbytes, Arm.beBytes, mkM3, k3V, Arm.ORR, Arm.AND, Arm.EXT2, Arm.EXT3, Arm.USHR,
      Arm.SHL, mask2V, zV, show (32 : Nat) ≠ 16 by omega, show (32 : Nat) ≠ 24 by omega,
      ite_true, ite_false]
    simp only [Arm.V.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp; bvtac)

/-! ## One hash of the kernel -/

/-- The kernel state after step 0 of a hash of the chain in slot `sl`, with
counter `T` and value `x`, `xb`: the cached rounds 0..3 and the schedule with
W16..W19. -/
def initK (n : Nat) (sl : sha256.hw.Slot) (T : Word) (x xb : Arm.V) : KState :=
  ⟨sl.a1, sl.e1, [Arm.SHA256SU1 (Arm.SHA256SU0 sl.m0 (mkM1 sl.c1 T x)) (mkM2 n sl.c2 x xb)
      (mkM3 n sl.c3 xb),
    mkM1 sl.c1 T x, mkM2 n sl.c2 x xb, mkM3 n sl.c3 xb]⟩

/-- The new value after a hash: steps 1..15 from `initK`, plus the initial state. -/
def hashV (n : Nat) (abcd0 efgh0 : Arm.V) (sl : sha256.hw.Slot) (T : Word) (x xb : Arm.V) :
    Arm.V × Arm.V :=
  (Arm.ADD (kstep ((List.range' 1 14).foldl kstep (initK n sl T x xb)) 15).abcd abcd0,
    xbNext n (Arm.ADD (kstep ((List.range' 1 14).foldl kstep (initK n sl T x xb)) 15).efgh efgh0) xb)

/-- The constants of slot `sl` are those of block `B` and state `st`. -/
def SlotOk (n : Nat) (st : List Word) (B : Spec.Bytes) (sl : sha256.hw.Slot) : Prop :=
  sl.m0 = beV B 0 ∧ sl.c1 = Arm.AND (beV B 16) mask1V ∧ sl.c2 = Arm.AND (beV B 32) (k2V n) ∧
  sl.c3 = Arm.AND (beV B 48) (k3V n) ∧ sl.tail = tailV n B ∧
  sl.a1 = Arm.SHA256H (vOf st 0) (vOf st 4) (Arm.ADD (beV B 0) (vOf K 0)) ∧
  sl.e1 = Arm.SHA256H2 (vOf st 4) (vOf st 0) (Arm.ADD (beV B 0) (vOf K 0))

theorem kcompress_split (s0 : KState) :
    (List.range 16).foldl kstep s0 = kstep ((List.range' 1 14).foldl kstep (kstep s0 0)) 15 := rfl

/-- One hash of the kernel is one step of the chain. -/
theorem hashV_eq (n : Nat) (hn : KN n) (st : List Word) (hst : st.length = 8) (B : Spec.Bytes)
    (hB : B.length = 64) (sl : sha256.hw.Slot) (hsl : SlotOk n st B sl) (c : Nat) (hc : c < 2 ^ 32)
    (x xb : Arm.V) (hnorm : Norm n xb) :
    hashV n (vOf st 0) (vOf st 4) sl (BitVec.ofNat 32 c) x xb = hval n st B c x xb := by
  obtain ⟨h0, h1, h2, h3, -, h4, h5⟩ := hsl
  have hn32 := (KN_le hn).2
  have hk := kcompress_eq st hst (setBlk n B c x xb) (setBlk_length n hn32 B hB c x xb)
  rw [beV_setBlk_0 _ hn32 _ hB, beV_setBlk_16 _ hn _ hB _ hc, beV_setBlk_32 _ hn _ hB _ _ _ hnorm,
    beV_setBlk_48 _ hn _ hB] at hk
  unfold kcompress at hk
  rw [kcompress_split] at hk
  have hinit : kstep ⟨vOf st 0, vOf st 4, [beV B 0, mkM1 (Arm.AND (beV B 16) mask1V) (BitVec.ofNat 32 c) x,
      mkM2 n (Arm.AND (beV B 32) (k2V n)) x xb, mkM3 n (Arm.AND (beV B 48) (k3V n)) xb]⟩ 0 =
      initK n sl (BitVec.ofNat 32 c) x xb := by
    simp [kstep, initK, h0, h1, h2, h3, h4, h5]
  rw [hinit] at hk
  unfold hval hashV
  rw [← hk]
  simp [vOf, vwords]

/-! ## A lane of the kernel -/

/-- What a lane holds: the value going into its current hash (`x`, `xb`), and
its kernel state. -/
abbrev LV := Arm.V × Arm.V × KState

/-- Step `i` (1..=15) of a lane on slot `sl`, counter `T` (used only at
`i = 1`). At `i = 15` the value is replaced by the result; for n = 16 the
last update of the second half of the state is skipped. -/
def lpure (n : Nat) (abcd0 efgh0 : Arm.V) (sl : sha256.hw.Slot) (T : Word) (i : Nat) (v : LV) : LV :=
  let k0 := if i = 1 then initK n sl T v.1 v.2.1 else v.2.2
  let k1 := kstep k0 i
  if i = 15 then
    (Arm.ADD k1.abcd abcd0, xbNext n (Arm.ADD k1.efgh efgh0) v.2.1,
      { k1 with efgh := if n = 16 then k0.efgh else k1.efgh })
  else (v.1, v.2.1, k1)

/-- The values of the chain in slot `sl` after `h` hashes. -/
def Xseq (n : Nat) (abcd0 efgh0 : Arm.V) (sl : sha256.hw.Slot) : Nat → Arm.V × Arm.V
  | 0 => (sl.x, sl.xb)
  | h + 1 => hashV n abcd0 efgh0 sl (BitVec.ofNat 32 (sl.t.val + h)) (Xseq n abcd0 efgh0 sl h).1
      (Xseq n abcd0 efgh0 sl h).2

/-- A lane that has done `g` lane steps on slot `sl`. -/
def Good (n : Nat) (abcd0 efgh0 : Arm.V) (sl : sha256.hw.Slot) (g : Nat) (v : LV) : Prop :=
  (v.1, v.2.1) = Xseq n abcd0 efgh0 sl (g / 15) ∧
  (g % 15 ≠ 0 → v.2.2 = (List.range' 1 (g % 15)).foldl kstep
    (initK n sl (BitVec.ofNat 32 (sl.t.val + g / 15)) (Xseq n abcd0 efgh0 sl (g / 15)).1
      (Xseq n abcd0 efgh0 sl (g / 15)).2))

theorem Good_zero (n : Nat) (abcd0 efgh0 : Arm.V) (sl : sha256.hw.Slot) (v : LV)
    (h : (v.1, v.2.1) = (sl.x, sl.xb)) : Good n abcd0 efgh0 sl 0 v := ⟨h, by simp⟩

theorem Good_step (n : Nat) (abcd0 efgh0 : Arm.V) (sl : sha256.hw.Slot) (g : Nat) (v : LV)
    (hg : Good n abcd0 efgh0 sl g v) :
    Good n abcd0 efgh0 sl (g + 1)
      (lpure n abcd0 efgh0 sl (BitVec.ofNat 32 (sl.t.val + g / 15)) (g % 15 + 1) v) := by
  obtain ⟨x, xb, k⟩ := v
  obtain ⟨hx, hk⟩ := hg
  simp only at hx hk
  have hlt : g % 15 < 15 := Nat.mod_lt _ (by omega)
  by_cases h0 : g % 15 = 0
  · -- a new hash
    have e1 : (g + 1) / 15 = g / 15 := by omega
    have e2 : (g + 1) % 15 = 1 := by omega
    have hl : lpure n abcd0 efgh0 sl (BitVec.ofNat 32 (sl.t.val + g / 15)) (g % 15 + 1) (x, xb, k) =
        (x, xb, kstep (initK n sl (BitVec.ofNat 32 (sl.t.val + g / 15)) x xb) 1) := by
      rw [h0]; simp [lpure]
    rw [hl]
    refine ⟨hx.trans (congrArg _ e1.symm), fun _ => ?_⟩
    simp only
    rw [e2, e1, ← hx]; rfl
  · by_cases h14 : g % 15 = 14
    · -- the end of a hash
      have e1 : (g + 1) / 15 = g / 15 + 1 := by omega
      have e2 : (g + 1) % 15 = 0 := by omega
      simp only [lpure, h14, show (14 + 1 : Nat) = 15 from rfl, show (15 : Nat) ≠ 1 by omega,
        ite_true, ite_false]
      refine ⟨?_, fun h => absurd e2 h⟩
      have hx2 : xb = (Xseq n abcd0 efgh0 sl (g / 15)).2 := by rw [← hx]
      rw [e1, Xseq, hk (by omega), h14, hx2]; rfl
    · have e1 : (g + 1) / 15 = g / 15 := by omega
      have e2 : (g + 1) % 15 = g % 15 + 1 := by omega
      simp only [lpure, show g % 15 + 1 ≠ 1 by omega, show g % 15 + 1 ≠ 15 by omega, ite_false]
      refine ⟨hx.trans (congrArg _ e1.symm), fun _ => ?_⟩
      rw [hk h0, e1, e2, List.range'_concat, List.foldl_append]
      simp [Nat.add_comm]

theorem Good_final (n : Nat) (abcd0 efgh0 : Arm.V) (sl : sha256.hw.Slot) (h : Nat) (v : LV)
    (hg : Good n abcd0 efgh0 sl (15 * h) v) : (v.1, v.2.1) = Xseq n abcd0 efgh0 sl h := by
  rw [hg.1]; congr 1; omega

theorem Xseq_norm (n : Nat) (abcd0 efgh0 : Arm.V) (sl : sha256.hw.Slot) (h0 : Norm n sl.xb) :
    ∀ k, Norm n (Xseq n abcd0 efgh0 sl k).2
  | 0 => h0
  | k + 1 => xbNext_norm _ _ _ (Xseq_norm n abcd0 efgh0 sl h0 k)

/-- The values of a slot are those of its chain. -/
theorem Xseq_Yseq (n : Nat) (hn : KN n) (st : List Word) (hst : st.length = 8) (B : Spec.Bytes)
    (hB : B.length = 64) (s : Nat) (sl : sha256.hw.Slot) (hsl : SlotOk n st B sl) (hs : s ≤ sl.t.val)
    (hx : (sl.x, sl.xb) = Yseq n st B s (sl.t.val - s)) :
    ∀ k, sl.t.val + k ≤ 2 ^ 32 → Xseq n (vOf st 0) (vOf st 4) sl k = Yseq n st B s (sl.t.val - s + k)
  | 0, _ => by rw [Nat.add_zero]; exact hx
  | k + 1, hk => by
    have ih := Xseq_Yseq n hn st hst B hB s sl hsl hs hx k (by omega)
    rw [Xseq, ih, hashV_eq n hn st hst B hB sl hsl _ (by omega) _ _ (Yseq_norm _ _ _ _ _),
      show sl.t.val - s + (k + 1) = (sl.t.val - s + k) + 1 by omega, Yseq,
      show s + (sl.t.val - s + k) = sl.t.val + k by omega]

end slhdsa
