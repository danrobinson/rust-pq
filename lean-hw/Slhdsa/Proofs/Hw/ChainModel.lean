import Slhdsa.Proofs.Hash
import Slhdsa.Proofs.Hw.Rounds
import Mathlib.Tactic.IntervalCases
open Aeneas Aeneas.Std Result

/-! A pure model of one chain of the hardware chain kernel: the block as its
fixed bytes, a counter and a value; one hash step; and its relation to
`stepBlock` / `runBlock`. -/

namespace slhdsa
open Spec.SHA256

set_option linter.unusedSimpArgs false

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

/-! ## The block of a chain -/

/-- The block `B` with counter `c` at bytes 18..22 and value `x` at bytes 22..38. -/
def setBlk (B : Spec.Bytes) (c : Nat) (x : Arm.V) : Spec.Bytes :=
  B.take 18 ++ Spec.toByte c 4 ++ vbytes x ++ B.drop 38

theorem toByte_length4 (c : Nat) : (Spec.toByte c 4).length = 4 := by simp [Spec.toByte]

theorem setBlk_length (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x : Arm.V) :
    (setBlk B c x).length = 64 := by
  simp [setBlk, toByte_length4, hB]

theorem setBlk_take18 (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x : Arm.V) :
    (setBlk B c x).take 18 = B.take 18 := by
  simp only [setBlk, List.append_assoc]
  exact List.take_left' (by simp [hB])

theorem setBlk_take22 (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x : Arm.V) :
    (setBlk B c x).take 22 = B.take 18 ++ Spec.toByte c 4 := by
  simp only [setBlk, List.append_assoc]
  rw [← List.append_assoc]
  exact List.take_left' (by simp [hB, toByte_length4])

theorem setBlk_drop22 (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x : Arm.V) :
    (setBlk B c x).drop 22 = vbytes x ++ B.drop 38 := by
  simp only [setBlk, List.append_assoc]
  rw [← List.append_assoc]
  exact List.drop_left' (by simp [hB, toByte_length4])

theorem setBlk_drop38 (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x : Arm.V) :
    (setBlk B c x).drop 38 = B.drop 38 := by
  simp only [setBlk]
  exact List.drop_left' (by simp [hB, toByte_length4])

/-- The value after one step from value `x` with counter `c`: the first four
words of the compression of the block. -/
def hval (st : List Word) (B : Spec.Bytes) (c : Nat) (x : Arm.V) : Arm.V :=
  vOf (compress st (setBlk B c x)) 0

theorem ser_take16 (l : List Word) (hl : l.length = 8) : (ser l).take 16 = vbytes (vOf l 0) := by
  match l, hl with
  | a :: b :: c :: d :: rest, _ =>
    simp [ser, vOf, vbytes, toByte_bv, Arm.beBytes]

theorem stepBlock_setBlk (st : List Word) (B : Spec.Bytes) (hB : B.length = 64) (c t : Nat)
    (x : Arm.V) : stepBlock st (setBlk B c x) t = setBlk B t (hval st B t x) := by
  unfold stepBlock
  simp only []
  rw [setBlk_take18 _ hB, setBlk_drop22 _ hB]
  have e : B.take 18 ++ Spec.toByte t 4 ++ (vbytes x ++ B.drop 38) = setBlk B t x := by
    simp [setBlk]
  rw [e, setBlk_take22 _ hB, setBlk_drop38 _ hB, ser_take16 _ (sha_compress_length _ _)]
  simp [setBlk, hval]

theorem stepBlock_congr (st : List Word) (B B' : Spec.Bytes) (t : Nat)
    (h1 : B.take 18 = B'.take 18) (h2 : B.drop 22 = B'.drop 22) :
    stepBlock st B t = stepBlock st B' t := by
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

theorem drop22_split (B : Spec.Bytes) (hB : B.length = 64) :
    B.drop 22 = vbytes (beV B 22) ++ B.drop 38 := by
  rw [vbytes_beV _ _ (by omega)]
  conv => lhs; rw [← List.take_append_drop 16 (B.drop 22)]
  rw [List.drop_drop]

theorem stepBlock_first (st : List Word) (B : Spec.Bytes) (hB : B.length = 64) (s : Nat) :
    stepBlock st B s = setBlk B s (hval st B s (beV B 22)) := by
  rw [stepBlock_congr st B (setBlk B s (beV B 22)) s (setBlk_take18 _ hB _ _).symm
    (by rw [setBlk_drop22 _ hB, drop22_split _ hB]), stepBlock_setBlk _ _ hB]

/-- The values of a chain started from block `B` at step `s`: `Yseq k` after `k` steps. -/
def Yseq (st : List Word) (B : Spec.Bytes) (s : Nat) : Nat → Arm.V
  | 0 => beV B 22
  | k + 1 => hval st B (s + k) (Yseq st B s k)

theorem runBlock_Yseq (st : List Word) (B : Spec.Bytes) (hB : B.length = 64) (s : Nat) :
    ∀ k, runBlock st B s (s + (k + 1)) = setBlk B (s + k) (Yseq st B s (k + 1))
  | 0 => by rw [runBlock_one, stepBlock_first _ _ hB]; rfl
  | k + 1 => by
    rw [runBlock_succ, runBlock_Yseq st B hB s k, stepBlock_setBlk _ _ hB]
    rfl

/-! ## The words the kernel rebuilds -/

/-- `MASK1` and `MASK2` as vectors, and the zero vector. -/
def mask1V : Arm.V := ⟨4294901760#32, 0#32, 0#32, 0#32⟩
def mask2V : Arm.V := ⟨0#32, 65535#32, 4294967295#32, 4294967295#32⟩
def zV : Arm.V := ⟨0#32, 0#32, 0#32, 0#32⟩

/-- W4..W7 as `lane_step` rebuilds them from `c1`, the counter `T` and the value `x`. -/
def mkM1 (c1 : Arm.V) (T : Word) (x : Arm.V) : Arm.V :=
  Arm.ORR (Arm.ORR c1 ⟨T >>> 16, T <<< 16, 0#32, 0#32⟩)
    (Arm.ORR (Arm.EXT3 zV (Arm.USHR x 16)) (Arm.EXT2 zV (Arm.SHL x 16)))

/-- W8..W11 as `lane_step` rebuilds them from `c2` and the value `x`. -/
def mkM2 (c2 : Arm.V) (x : Arm.V) : Arm.V :=
  Arm.ORR c2 (Arm.ORR (Arm.EXT2 (Arm.SHL x 16) zV) (Arm.EXT3 (Arm.USHR x 16) zV))

theorem setBlk_getElem! (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x : Arm.V) (j : Nat) :
    (setBlk B c x)[j]! = if j < 18 then B[j]! else if j < 22 then (Spec.toByte c 4)[j - 18]!
      else if j < 38 then (vbytes x)[j - 22]! else B[j]! := by
  rw [setBlk, getElem!_app, getElem!_app, getElem!_app]
  have l1 : (B.take 18).length = 18 := by simp [hB]
  simp only [List.length_append, l1, toByte_length4, vbytes_length]
  split_ifs <;> first
    | omega
    | rfl
    | exact getElem!_take' _ _ _ (by omega)
    | (rw [getElem!_drop', Nat.add_sub_cancel' (by omega)])

theorem word_setBlk_lo (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x : Arm.V) (j : Nat)
    (hj : j + 3 < 18) : word (setBlk B c x) j = word B j := by
  simp only [word, setBlk_getElem! _ hB]
  simp only [show j < 18 by omega, show j + 1 < 18 by omega, show j + 2 < 18 by omega,
    show j + 3 < 18 by omega, ite_true]

theorem word_setBlk_hi (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x : Arm.V) (j : Nat)
    (hj : 38 ≤ j) : word (setBlk B c x) j = word B j := by
  simp only [word, setBlk_getElem! _ hB]
  simp only [show ¬ j < 18 by omega, show ¬ j < 22 by omega, show ¬ j < 38 by omega,
    show ¬ j + 1 < 18 by omega, show ¬ j + 1 < 22 by omega, show ¬ j + 1 < 38 by omega,
    show ¬ j + 2 < 18 by omega, show ¬ j + 2 < 22 by omega, show ¬ j + 2 < 38 by omega,
    show ¬ j + 3 < 18 by omega, show ¬ j + 3 < 22 by omega, show ¬ j + 3 < 38 by omega, ite_false]

theorem beV_setBlk_0 (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x : Arm.V) :
    beV (setBlk B c x) 0 = beV B 0 := by
  simp only [beV, word_setBlk_lo _ hB _ _ _ (by omega : 0 + 3 < 18),
    word_setBlk_lo _ hB _ _ _ (by omega : 0 + 4 + 3 < 18),
    word_setBlk_lo _ hB _ _ _ (by omega : 0 + 8 + 3 < 18),
    word_setBlk_lo _ hB _ _ _ (by omega : 0 + 12 + 3 < 18)]

theorem beV_setBlk_48 (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x : Arm.V) :
    beV (setBlk B c x) 48 = beV B 48 := by
  simp only [beV, word_setBlk_hi _ hB _ _ _ (by omega : 38 ≤ 48),
    word_setBlk_hi _ hB _ _ _ (by omega : 38 ≤ 48 + 4),
    word_setBlk_hi _ hB _ _ _ (by omega : 38 ≤ 48 + 8),
    word_setBlk_hi _ hB _ _ _ (by omega : 38 ≤ 48 + 12)]

theorem beV_setBlk_16 (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (hc : c < 2 ^ 32)
    (x : Arm.V) :
    beV (setBlk B c x) 16 = mkM1 (Arm.AND (beV B 16) mask1V) (BitVec.ofNat 32 c) x := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  simp only [beV, word, setBlk_getElem! _ hB, toByte_ofNat c hc]
  simp only [vbytes, Arm.beBytes, mkM1, Arm.ORR, Arm.AND, Arm.EXT2, Arm.EXT3, Arm.USHR, Arm.SHL,
    mask1V, zV]
  simp only [Arm.V.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp; bvtac)

theorem beV_setBlk_32 (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x : Arm.V) :
    beV (setBlk B c x) 32 = mkM2 (Arm.AND (beV B 32) mask2V) x := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  simp only [beV, word, setBlk_getElem! _ hB]
  simp only [vbytes, Arm.beBytes, mkM2, Arm.ORR, Arm.AND, Arm.EXT2, Arm.EXT3, Arm.USHR, Arm.SHL,
    mask2V, zV]
  simp only [Arm.V.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp; bvtac)

/-! ## One hash of the kernel -/

/-- The kernel state after step 0 of a hash of the chain in slot `sl`, with
counter `T` and value `x`: the cached rounds 0..3 and the schedule with W16..W19. -/
def initK (sl : sha256.hw.Slot) (T : Word) (x : Arm.V) : KState :=
  ⟨sl.a1, sl.e1, [Arm.SHA256SU1 (Arm.SHA256SU0 sl.m0 (mkM1 sl.c1 T x)) (mkM2 sl.c2 x) sl.m3,
    mkM1 sl.c1 T x, mkM2 sl.c2 x, sl.m3]⟩

/-- The new value after a hash: steps 1..15 from `initK`, plus the first state words. -/
def hashV (abcd0 : Arm.V) (sl : sha256.hw.Slot) (T : Word) (x : Arm.V) : Arm.V :=
  Arm.ADD (kstep ((List.range' 1 14).foldl kstep (initK sl T x)) 15).abcd abcd0

/-- The constants of slot `sl` are those of block `B` and state `st`. -/
def SlotOk (st : List Word) (B : Spec.Bytes) (sl : sha256.hw.Slot) : Prop :=
  sl.m0 = beV B 0 ∧ sl.c1 = Arm.AND (beV B 16) mask1V ∧ sl.c2 = Arm.AND (beV B 32) mask2V ∧
  sl.m3 = beV B 48 ∧
  sl.a1 = Arm.SHA256H (vOf st 0) (vOf st 4) (Arm.ADD (beV B 0) (vOf K 0)) ∧
  sl.e1 = Arm.SHA256H2 (vOf st 4) (vOf st 0) (Arm.ADD (beV B 0) (vOf K 0))

theorem kcompress_split (s0 : KState) :
    (List.range 16).foldl kstep s0 = kstep ((List.range' 1 14).foldl kstep (kstep s0 0)) 15 := rfl

/-- One hash of the kernel is one step of the chain. -/
theorem hashV_eq (st : List Word) (hst : st.length = 8) (B : Spec.Bytes) (hB : B.length = 64)
    (sl : sha256.hw.Slot) (hsl : SlotOk st B sl) (c : Nat) (hc : c < 2 ^ 32) (x : Arm.V) :
    hashV (vOf st 0) sl (BitVec.ofNat 32 c) x = hval st B c x := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hsl
  have hk := kcompress_eq st hst (setBlk B c x) (setBlk_length B hB c x)
  rw [beV_setBlk_0 _ hB, beV_setBlk_16 _ hB _ hc, beV_setBlk_32 _ hB, beV_setBlk_48 _ hB] at hk
  unfold kcompress at hk
  rw [kcompress_split] at hk
  have hinit : kstep ⟨vOf st 0, vOf st 4, [beV B 0, mkM1 (Arm.AND (beV B 16) mask1V) (BitVec.ofNat 32 c) x,
      mkM2 (Arm.AND (beV B 32) mask2V) x, beV B 48]⟩ 0 = initK sl (BitVec.ofNat 32 c) x := by
    simp [kstep, initK, h0, h1, h2, h3, h4, h5]
  rw [hinit] at hk
  unfold hval hashV
  rw [← hk]
  simp [vOf, vwords]

/-! ## A lane of the kernel -/

/-- What a lane holds: the value going into its current hash, and its kernel state. -/
abbrev LV := Arm.V × KState

/-- Step `i` (1..=15) of a lane on slot `sl`, counter `T` (used only at `i = 1`). -/
def lpure (abcd0 : Arm.V) (sl : sha256.hw.Slot) (T : Word) (i : Nat) (v : LV) : LV :=
  let k0 := if i = 1 then initK sl T v.1 else v.2
  let k1 := kstep k0 i
  if i = 15 then (Arm.ADD k1.abcd abcd0, { k1 with efgh := k0.efgh }) else (v.1, k1)

/-- The values of the chain in slot `sl` after `h` hashes. -/
def Xseq (abcd0 : Arm.V) (sl : sha256.hw.Slot) : Nat → Arm.V
  | 0 => sl.x
  | h + 1 => hashV abcd0 sl (BitVec.ofNat 32 (sl.t.val + h)) (Xseq abcd0 sl h)

/-- A lane that has done `g` lane steps on slot `sl`. -/
def Good (abcd0 : Arm.V) (sl : sha256.hw.Slot) (g : Nat) (v : LV) : Prop :=
  v.1 = Xseq abcd0 sl (g / 15) ∧
  (g % 15 ≠ 0 → v.2 = (List.range' 1 (g % 15)).foldl kstep
    (initK sl (BitVec.ofNat 32 (sl.t.val + g / 15)) (Xseq abcd0 sl (g / 15))))

theorem Good_zero (abcd0 : Arm.V) (sl : sha256.hw.Slot) (v : LV) (h : v.1 = sl.x) :
    Good abcd0 sl 0 v := ⟨h, by simp⟩

theorem Good_step (abcd0 : Arm.V) (sl : sha256.hw.Slot) (g : Nat) (v : LV)
    (hg : Good abcd0 sl g v) :
    Good abcd0 sl (g + 1) (lpure abcd0 sl (BitVec.ofNat 32 (sl.t.val + g / 15)) (g % 15 + 1) v) := by
  obtain ⟨hx, hk⟩ := hg
  have hlt : g % 15 < 15 := Nat.mod_lt _ (by omega)
  by_cases h0 : g % 15 = 0
  · -- a new hash
    have e1 : (g + 1) / 15 = g / 15 := by omega
    have e2 : (g + 1) % 15 = 1 := by omega
    simp only [lpure, h0, Nat.zero_add, ite_true, show (1 : Nat) ≠ 15 by omega, ite_false]
    refine ⟨by rw [e1, hx], fun _ => ?_⟩
    rw [e2, e1, hx]; rfl
  · by_cases h14 : g % 15 = 14
    · -- the end of a hash
      have e1 : (g + 1) / 15 = g / 15 + 1 := by omega
      have e2 : (g + 1) % 15 = 0 := by omega
      simp only [lpure, h14, show (14 + 1 : Nat) = 15 from rfl, show (15 : Nat) ≠ 1 by omega,
        ite_true, ite_false]
      refine ⟨?_, fun h => absurd e2 h⟩
      rw [e1, Xseq, hk (by omega), h14]; rfl
    · have e1 : (g + 1) / 15 = g / 15 := by omega
      have e2 : (g + 1) % 15 = g % 15 + 1 := by omega
      simp only [lpure, show g % 15 + 1 ≠ 1 by omega, show g % 15 + 1 ≠ 15 by omega, ite_false]
      refine ⟨by rw [e1, hx], fun _ => ?_⟩
      rw [hk h0, e1, e2, List.range'_concat, List.foldl_append]
      simp [Nat.add_comm]

theorem Good_final (abcd0 : Arm.V) (sl : sha256.hw.Slot) (h : Nat) (v : LV)
    (hg : Good abcd0 sl (15 * h) v) : v.1 = Xseq abcd0 sl h := by
  rw [hg.1]; congr 1; omega

/-- The values of a slot are those of its chain. -/
theorem Xseq_Yseq (st : List Word) (hst : st.length = 8) (B : Spec.Bytes) (hB : B.length = 64)
    (s : Nat) (sl : sha256.hw.Slot) (hsl : SlotOk st B sl) (hs : s ≤ sl.t.val)
    (hx : sl.x = Yseq st B s (sl.t.val - s)) :
    ∀ k, sl.t.val + k ≤ 2 ^ 32 → Xseq (vOf st 0) sl k = Yseq st B s (sl.t.val - s + k)
  | 0, _ => by rw [Nat.add_zero]; exact hx
  | k + 1, hk => by
    rw [Xseq, Xseq_Yseq st hst B hB s sl hsl hs hx k (by omega), hashV_eq st hst B hB sl hsl _
      (by omega), show sl.t.val - s + (k + 1) = (sl.t.val - s + k) + 1 by omega, Yseq,
      show s + (sl.t.val - s + k) = sl.t.val + k by omega]

end slhdsa
