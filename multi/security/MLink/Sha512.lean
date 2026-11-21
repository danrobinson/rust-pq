import MLink.Sha256
import MLink.Encoding

/-!
# SHA-512, HMAC-SHA-512 and MGF1-SHA-512: `Spec` = VCVio

VCVio's `VCVio.Algorithms.Sha2` (`sha512Family iv512 64`, `compress512`, `pad512`, 64-bit words,
128-byte blocks, 128-bit length field) against the list-fold transcription `Spec.SHA512` of
FIPS 180-4.  The proof follows `MLink/Sha256.lean`: words, schedule, rounds, compression, padding,
block iteration.  `compress512` is one monolithic `Id.run do` block; `compress512_unfold` first
exposes it as "schedule, then a fold of rounds, then feed-forward".

No side condition is needed anywhere.  In particular the 128-bit length field agrees for every
message length: VCVio writes `natToBytesBE (8 * len) 16` and the spec `toByte (8 * len) 16`, both
of which are the low 128 bits of `8 * len`; and MGF1's block counter is reduced modulo `2^32` on
both sides.
-/

namespace MLink

open VCVio.Algorithms.Sha2

/-! ### Word-level correspondence -/

/-- Read a `UInt64` array as a list of spec words. -/
def W64 (a : Array UInt64) : List (BitVec 64) := a.toList.map UInt64.toBitVec

theorem W64_get (a : Array UInt64) (i : Nat) : (W64 a)[i]! = (a[i]!).toBitVec := by
  by_cases h : i < a.size <;> simp [W64, h]
  rfl
theorem W64_get' (a : Array UInt64) (i : Nat) :
    (W64 a)[i]?.getD default = (a[i]!).toBitVec := by
  rw [← W64_get]; simp
@[simp] theorem W64_length (a : Array UInt64) : (W64 a).length = a.size := by simp [W64]
theorem W64_set (a : Array UInt64) (i : Nat) (v : UInt64) :
    W64 (a.setIfInBounds i v) = (W64 a).set i v.toBitVec := by
  simp [W64, List.map_set]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
theorem app8 (a b c d e f g h : BitVec 8) (i : Nat) :
    (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h : BitVec 64).getLsbD i =
      if i < 8 then h.getLsbD i else if i < 16 then g.getLsbD (i - 8)
      else if i < 24 then f.getLsbD (i - 16) else if i < 32 then e.getLsbD (i - 24)
      else if i < 40 then d.getLsbD (i - 32) else if i < 48 then c.getLsbD (i - 40)
      else if i < 56 then b.getLsbD (i - 48) else a.getLsbD (i - 56) := by
  have ge : ∀ (x : BitVec 8) (j : Nat), 8 ≤ j → x.getLsbD j = false :=
    fun x j h => BitVec.getLsbD_of_ge x j h
  simp only [BitVec.getLsbD_append]
  by_cases h1 : i < 8
  · simp [h1] <;> intros <;> omega
  by_cases h2 : i < 16
  · simp [h1, h2] <;> intros <;> omega
  by_cases h3 : i < 24
  · simp [h1, h2, h3, show ¬ i - 8 < 8 by omega, show i - 8 - 8 = i - 16 by omega] <;> intros <;> omega
  by_cases h4 : i < 32
  · simp [h1, h2, h3, h4, show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega,
      show i - 8 - 8 - 8 = i - 24 by omega] <;> intros <;> omega
  by_cases h5 : i < 40
  · simp [h1, h2, h3, h4, h5, show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega,
      show ¬ i - 8 - 8 - 8 < 8 by omega, show i - 8 - 8 - 8 - 8 = i - 32 by omega] <;> intros <;> omega
  by_cases h6 : i < 48
  · simp [h1, h2, h3, h4, h5, h6, show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega,
      show ¬ i - 8 - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 - 8 < 8 by omega,
      show i - 8 - 8 - 8 - 8 - 8 = i - 40 by omega] <;> intros <;> omega
  by_cases h7 : i < 56
  · simp [h1, h2, h3, h4, h5, h6, h7, show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega,
      show ¬ i - 8 - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 - 8 < 8 by omega,
      show ¬ i - 8 - 8 - 8 - 8 - 8 < 8 by omega,
      show i - 8 - 8 - 8 - 8 - 8 - 8 = i - 48 by omega] <;> intros <;> omega
  · simp [h1, h2, h3, h4, h5, h6, h7, show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega,
      show ¬ i - 8 - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 - 8 < 8 by omega,
      show ¬ i - 8 - 8 - 8 - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 - 8 - 8 - 8 < 8 by omega,
      show i - 8 - 8 - 8 - 8 - 8 - 8 - 8 = i - 56 by omega] <;> intros <;> omega

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
theorem be64 (a b c d e f g h : UInt8) :
    (a.toUInt64 <<< 56 ||| b.toUInt64 <<< 48 ||| c.toUInt64 <<< 40 ||| d.toUInt64 <<< 32 |||
      e.toUInt64 <<< 24 ||| f.toUInt64 <<< 16 ||| g.toUInt64 <<< 8 ||| h.toUInt64).toBitVec
      = a.toBitVec ++ b.toBitVec ++ c.toBitVec ++ d.toBitVec ++ e.toBitVec ++ f.toBitVec ++
        g.toBitVec ++ h.toBitVec := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [app8]
  have ge : ∀ (x : BitVec 8) (j : Nat), 8 ≤ j → x.getLsbD j = false :=
    fun x j h => BitVec.getLsbD_of_ge x j h
  simp
  by_cases h1 : i < 8
  · simp [h1, show i < 16 by omega, show i < 24 by omega, show i < 32 by omega,
      show i < 40 by omega, show i < 48 by omega, show i < 56 by omega] <;> intros <;> omega
  by_cases h2 : i < 16
  · simp [h1, h2, hi, show i < 24 by omega, show i < 32 by omega,
      show i < 40 by omega, show i < 48 by omega, show i < 56 by omega, ge _ i (by omega)] <;> intros <;> omega
  by_cases h3 : i < 24
  · simp [h1, h2, h3, hi, show i < 32 by omega,
      show i < 40 by omega, show i < 48 by omega, show i < 56 by omega, ge _ i (by omega),
      ge _ (i - 8) (by omega)] <;> intros <;> omega
  by_cases h4 : i < 32
  · simp [h1, h2, h3, h4, hi,
      show i < 40 by omega, show i < 48 by omega, show i < 56 by omega, ge _ i (by omega),
      ge _ (i - 8) (by omega), ge _ (i - 16) (by omega)] <;> intros <;> omega
  by_cases h5 : i < 40
  · simp [h1, h2, h3, h4, h5, hi, show i < 48 by omega, show i < 56 by omega, ge _ i (by omega),
      ge _ (i - 8) (by omega), ge _ (i - 16) (by omega), ge _ (i - 24) (by omega)] <;> intros <;> omega
  by_cases h6 : i < 48
  · simp [h1, h2, h3, h4, h5, h6, hi, show i < 56 by omega, ge _ i (by omega),
      ge _ (i - 8) (by omega), ge _ (i - 16) (by omega), ge _ (i - 24) (by omega),
      ge _ (i - 32) (by omega)] <;> intros <;> omega
  by_cases h7 : i < 56
  · simp [h1, h2, h3, h4, h5, h6, h7, hi, ge _ i (by omega),
      ge _ (i - 8) (by omega), ge _ (i - 16) (by omega), ge _ (i - 24) (by omega),
      ge _ (i - 32) (by omega), ge _ (i - 40) (by omega)] <;> intros <;> omega
  · simp [h1, h2, h3, h4, h5, h6, h7, hi, ge _ i (by omega),
      ge _ (i - 8) (by omega), ge _ (i - 16) (by omega), ge _ (i - 24) (by omega),
      ge _ (i - 32) (by omega), ge _ (i - 40) (by omega), ge _ (i - 48) (by omega)] <;> intros <;> omega

theorem ssig0_eq64 (x : UInt64) : (ssig0Sha512 x).toBitVec = Spec.SHA512.ssig0 x.toBitVec := by
  simp [ssig0Sha512, Spec.SHA512.ssig0, rotr64, BitVec.rotateRight, BitVec.rotateRightAux]
theorem ssig1_eq64 (x : UInt64) : (ssig1Sha512 x).toBitVec = Spec.SHA512.ssig1 x.toBitVec := by
  simp [ssig1Sha512, Spec.SHA512.ssig1, rotr64, BitVec.rotateRight, BitVec.rotateRightAux]
theorem bsig0_eq64 (x : UInt64) : (bsig0Sha512 x).toBitVec = Spec.SHA512.bsig0 x.toBitVec := by
  simp [bsig0Sha512, Spec.SHA512.bsig0, rotr64, BitVec.rotateRight, BitVec.rotateRightAux]
theorem bsig1_eq64 (x : UInt64) : (bsig1Sha512 x).toBitVec = Spec.SHA512.bsig1 x.toBitVec := by
  simp [bsig1Sha512, Spec.SHA512.bsig1, rotr64, BitVec.rotateRight, BitVec.rotateRightAux]
theorem ch_eq64 (x y z : UInt64) :
    (ch64 x y z).toBitVec = Spec.SHA512.ch x.toBitVec y.toBitVec z.toBitVec := by
  simp [ch64, Spec.SHA512.ch]
theorem maj_eq64 (x y z : UInt64) :
    (maj64 x y z).toBitVec = Spec.SHA512.maj x.toBitVec y.toBitVec z.toBitVec := by
  simp [maj64, Spec.SHA512.maj]
theorem W_k64 : W64 k512 = Spec.SHA512.K := by decide
theorem W_iv64 : W64 iv512 = Spec.SHA512.H0 := by decide

theorem blockAt_get64 (p : Spec.Bytes) (k j : Nat) (h : j < 128) :
    (Spec.SHA512.blockAt p k)[j]! = p[128 * k + j]! := by
  simp [Spec.SHA512.blockAt, h]

/-! ### `compress512` in structured form -/

/-- The big-endian 64-bit word `t` of the block at byte offset `base`. -/
def readWord512 (m : ByteArray) (base t : Nat) : UInt64 :=
  (m[base + t * 8]!).toUInt64 <<< 56 ||| (m[base + t * 8 + 1]!).toUInt64 <<< 48 |||
    (m[base + t * 8 + 2]!).toUInt64 <<< 40 ||| (m[base + t * 8 + 3]!).toUInt64 <<< 32 |||
    (m[base + t * 8 + 4]!).toUInt64 <<< 24 ||| (m[base + t * 8 + 5]!).toUInt64 <<< 16 |||
    (m[base + t * 8 + 6]!).toUInt64 <<< 8 ||| (m[base + t * 8 + 7]!).toUInt64

/-- The sixteen loaded schedule words in an 80-word buffer. -/
def loadSchedule512 (m : ByteArray) (base : Nat) : Array UInt64 :=
  (List.range' 0 16).foldl (fun b a => b.setIfInBounds a (readWord512 m base a))
    (Array.replicate 80 0)

/-- The expanded 80-word schedule. -/
def expandSchedule512 (w0 : Array UInt64) : Array UInt64 :=
  (List.range' 16 64).foldl (fun b a => b.setIfInBounds a
    (ssig1Sha512 b[a - 2]! + b[a - 7]! + ssig0Sha512 b[a - 15]! + b[a - 16]!)) w0

/-- The working registers `(a, …, h)` of `compress512`. -/
abbrev St512 := UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64

/-- One round of `compress512`. -/
def round512 (w : Array UInt64) (b : St512) (t : Nat) : St512 :=
  (b.2.2.2.2.2.2.2 + bsig1Sha512 b.2.2.2.2.1 + ch64 b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 +
      k512[t]! + w[t]! + (bsig0Sha512 b.1 + maj64 b.1 b.2.1 b.2.2.1),
    b.1, b.2.1, b.2.2.1,
    b.2.2.2.1 + (b.2.2.2.2.2.2.2 + bsig1Sha512 b.2.2.2.2.1 +
      ch64 b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 + k512[t]! + w[t]!),
    b.2.2.2.2.1, b.2.2.2.2.2.1, b.2.2.2.2.2.2.1)

/-- The 80 rounds of `compress512`. -/
def runRounds512 (st w : Array UInt64) : St512 :=
  (List.range' 0 80).foldl (round512 w)
    (st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!)

/-- VCVio's monolithic `compress512` is: load, expand, 80 rounds, feed-forward. -/
theorem compress512_unfold (st : Array UInt64) (m : ByteArray) (base : Nat) :
    compress512 st m base =
      let s := runRounds512 st (expandSchedule512 (loadSchedule512 m base))
      #[st[0]! + s.1, st[1]! + s.2.1, st[2]! + s.2.2.1, st[3]! + s.2.2.2.1,
        st[4]! + s.2.2.2.2.1, st[5]! + s.2.2.2.2.2.1, st[6]! + s.2.2.2.2.2.2.1,
        st[7]! + s.2.2.2.2.2.2.2] := by
  unfold compress512 runRounds512 expandSchedule512 loadSchedule512 round512 readWord512
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp

/-! ### Message schedule -/

theorem load_take64 (f : Nat → UInt64) (n : Nat) (w0 : Array UInt64) (h : n ≤ w0.size) :
    (List.foldl (fun b a => b.setIfInBounds a (f a)) w0 (List.range' 0 n)).size = w0.size ∧
    (W64 (List.foldl (fun b a => b.setIfInBounds a (f a)) w0 (List.range' 0 n))).take n
      = (List.range n).map (fun t => (f t).toBitVec) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append]
    refine ⟨by simp [h1], ?_⟩
    simp only [List.foldl_cons, List.foldl_nil, W64_set, Nat.zero_add, Nat.one_mul]
    rw [take_set_succ _ _ _ (by simp [h1]; omega), h2, List.range_succ, List.map_append]
    rfl

open Spec.SHA512 in
theorem expand_take64 (n : Nat) (w0 : Array UInt64) (hs : w0.size = 80) (h : 16 + n ≤ 80) :
    (List.foldl (fun b a => b.setIfInBounds a
        (ssig1Sha512 b[a - 2]! + b[a - 7]! + ssig0Sha512 b[a - 15]! + b[a - 16]!)) w0
      (List.range' 16 n)).size = 80 ∧
    (W64 (List.foldl (fun b a => b.setIfInBounds a
        (ssig1Sha512 b[a - 2]! + b[a - 7]! + ssig0Sha512 b[a - 15]! + b[a - 16]!)) w0
      (List.range' 16 n))).take (16 + n) = Nat.repeat scheduleStep n ((W64 w0).take 16) := by
  induction n with
  | zero => simp [Nat.repeat, hs]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append]
    refine ⟨by simp [h1], ?_⟩
    simp only [List.foldl_cons, List.foldl_nil, W64_set, Nat.one_mul]
    rw [← Nat.add_assoc, take_set_succ _ _ _ (by simp [h1]; omega), Nat.repeat, ← h2]
    simp only [scheduleStep, List.length_take, W64_length, h1,
      Nat.min_eq_left (show 16 + n ≤ 80 by omega)]
    rw [take_get _ _ _ (by omega), take_get _ _ _ (by omega), take_get _ _ _ (by omega),
      take_get _ _ _ (by omega)]
    simp only [W64_get, ssig0_eq64, ssig1_eq64, UInt64.toBitVec_add, Nat.add_sub_cancel_left]

theorem readWord512_eq (m : ByteArray) (k t : Nat) (ht : t < 16) :
    (readWord512 m (k * 128) t).toBitVec
      = Spec.SHA512.word (Spec.SHA512.blockAt (spA m) k) (8 * t) := by
  unfold readWord512 Spec.SHA512.word
  rw [be64, blockAt_get64 _ _ _ (by omega), blockAt_get64 _ _ _ (by omega),
    blockAt_get64 _ _ _ (by omega), blockAt_get64 _ _ _ (by omega),
    blockAt_get64 _ _ _ (by omega), blockAt_get64 _ _ _ (by omega),
    blockAt_get64 _ _ _ (by omega), blockAt_get64 _ _ _ (by omega)]
  rw [show 128 * k + 8 * t = k * 128 + t * 8 by omega,
    show 128 * k + (8 * t + 1) = k * 128 + t * 8 + 1 by omega,
    show 128 * k + (8 * t + 2) = k * 128 + t * 8 + 2 by omega,
    show 128 * k + (8 * t + 3) = k * 128 + t * 8 + 3 by omega,
    show 128 * k + (8 * t + 4) = k * 128 + t * 8 + 4 by omega,
    show 128 * k + (8 * t + 5) = k * 128 + t * 8 + 5 by omega,
    show 128 * k + (8 * t + 6) = k * 128 + t * 8 + 6 by omega,
    show 128 * k + (8 * t + 7) = k * 128 + t * 8 + 7 by omega]
  simp only [spA_get]

theorem loadSchedule512_eq (m : ByteArray) (k : Nat) :
    (loadSchedule512 m (k * 128)).size = 80 ∧
    (W64 (loadSchedule512 m (k * 128))).take 16
      = Spec.SHA512.blockWords (Spec.SHA512.blockAt (spA m) k) := by
  have := load_take64 (readWord512 m (k * 128)) 16 (Array.replicate 80 0) (by simp)
  unfold loadSchedule512
  refine ⟨by simpa using this.1, ?_⟩
  rw [this.2, Spec.SHA512.blockWords]
  apply List.map_congr_left
  intro t ht
  exact readWord512_eq m k t (by simpa using ht)

theorem schedule512_eq (m : ByteArray) (k : Nat) :
    W64 (expandSchedule512 (loadSchedule512 m (k * 128)))
      = Spec.SHA512.schedule (Spec.SHA512.blockAt (spA m) k) := by
  obtain ⟨h1, h2⟩ := loadSchedule512_eq m k
  have := expand_take64 64 _ h1 (by omega)
  unfold expandSchedule512 Spec.SHA512.schedule
  rw [← h2, ← this.2, List.take_of_length_le (by simp [this.1])]

/-! ### Rounds and compression -/

/-- Read a VCVio round state as a spec state. -/
def R64 (s : St512) : Spec.SHA512.State :=
  (s.1.toBitVec, s.2.1.toBitVec, s.2.2.1.toBitVec, s.2.2.2.1.toBitVec,
    s.2.2.2.2.1.toBitVec, s.2.2.2.2.2.1.toBitVec, s.2.2.2.2.2.2.1.toBitVec,
    s.2.2.2.2.2.2.2.toBitVec)

theorem round512_eq (w : Array UInt64) (s : St512) (t : Nat) :
    R64 (round512 w s t) = Spec.SHA512.round (W64 w) (R64 s) t := by
  have hk : Spec.SHA512.K[t]! = (k512[t]!).toBitVec := by rw [← W_k64, W64_get]
  simp only [round512, Spec.SHA512.round, R64, hk, W64_get]
  simp [bsig0_eq64, bsig1_eq64, ch_eq64, maj_eq64]

theorem runRounds512_eq (st w : Array UInt64) :
    R64 (runRounds512 st w) = (List.range 80).foldl (Spec.SHA512.round (W64 w))
      ((W64 st)[0]!, (W64 st)[1]!, (W64 st)[2]!, (W64 st)[3]!, (W64 st)[4]!, (W64 st)[5]!,
        (W64 st)[6]!, (W64 st)[7]!) := by
  unfold runRounds512
  rw [foldl_rel R64 _ (Spec.SHA512.round (W64 w)) (fun a c => round512_eq w a c),
    List.range_eq_range']
  simp only [R64, W64_get]

theorem compress512_eq (st : Array UInt64) (m : ByteArray) (k : Nat) :
    W64 (compress512 st m (k * 128))
      = Spec.SHA512.compress (W64 st) (Spec.SHA512.blockAt (spA m) k) := by
  rw [compress512_unfold]
  unfold Spec.SHA512.compress
  simp only
  rw [← schedule512_eq, ← runRounds512_eq]
  simp only [R64, W64_get]
  simp [W64]

theorem compress512_size (st : Array UInt64) (m : ByteArray) (b : Nat) :
    (compress512 st m b).size = 8 := by
  rw [compress512_unfold]; rfl

/-! ### Padding and serialization -/

theorem u64be_eq' (x : UInt64) : spA (u64be x) = Spec.toByte x.toNat 8 := by
  simp [u64be, spA, sp, Spec.toByte, List.range_succ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp [Nat.shiftRight_eq_div_pow]

/-- SHA-512 padding agrees for every message length (the 128-bit length field is the low 128 bits
of `8 * len` on both sides). -/
theorem pad512_eq (m : ByteArray) : spA (pad512 m) = Spec.SHA512.pad (spA m) := by
  unfold pad512 Spec.SHA512.pad
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [push_loop, spA_push, ← toByte_eq]
  have : (240 - (m.size + 1) % 128) % 128 = (239 - m.size % 128) % 128 := by omega
  simp [this]
  rfl

theorem stateBytes64_eq (st : Array UInt64) (hs : st.size = 8) :
    spA ((stateBytes64 st).extract 0 64) = (W64 st).flatMap fun w => Spec.toByte w.toNat 8 := by
  have := @ByteArray.extract_zero_size (stateBytes64 st)
  rw [stateBytes64_size] at this
  rw [this]
  obtain ⟨l⟩ := st
  simp at hs
  match l, hs with
  | [a, b, c, d, e, f, g, h], _ =>
    simp [W64, ← u64be_eq', stateBytes64, spA, sp, u64be]
    repeat' apply And.intro
    all_goals rfl

/-! ### SHA-512 -/

theorem blocks512_eq (p : ByteArray) (l : List Nat) (st : Array UInt64) (hs : st.size = 8) :
    (l.foldl (fun b a => compress512 b p (a * 128)) st).size = 8 ∧
    W64 (l.foldl (fun b a => compress512 b p (a * 128)) st)
      = l.foldl (fun st k => Spec.SHA512.compress st (Spec.SHA512.blockAt (spA p) k)) (W64 st) := by
  induction l generalizing st with
  | nil => exact ⟨hs, rfl⟩
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [← compress512_eq]
    exact ih _ (compress512_size _ _ _)

/-- SHA-512 agrees on every input (no length bound). -/
theorem sha512_eq (b : ByteArray) : spA (sha512 b) = Spec.sha512 (spA b) := by
  unfold sha512 sha512Family Spec.SHA512.sha512
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  obtain ⟨h1, h2⟩ := blocks512_eq (pad512 b) (List.range' 0 ((pad512 b).size / 128)) iv512 rfl
  rw [stateBytes64_eq _ h1, h2, W_iv64, ← pad512_eq, spA_length, List.range_eq_range']

theorem spec_sha512_length (x : Spec.Bytes) : (Spec.sha512 x).length = 64 := by
  have h : spA (sha512 (ByteArray.mk (cv x).toArray)) = Spec.sha512 (sp (cv x)) := sha512_eq _
  rw [sp_cv] at h
  rw [← h, spA_length, sha512_size]

/-! ### HMAC -/

theorem hmacKey0Sha512_eq (key : ByteArray) :
    spA (hmacKey0Sha512 key) =
      (if (spA key).length > 128 then Spec.sha512 (spA key) else spA key) ++
        List.replicate (128 - (if (spA key).length > 128 then Spec.sha512 (spA key)
          else spA key).length) 0#8 := by
  unfold hmacKey0Sha512
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [push_loop]
  have hl : (Spec.sha512 (spA key)).length = 64 := spec_sha512_length _
  split <;> simp [sha512_eq, hl]

/-- HMAC-SHA-512 agrees on every key and message. -/
theorem hmacSha512_eq (key msg : ByteArray) :
    spA (hmacSha512 key msg) = Spec.hmacSha512 (spA key) (spA msg) := by
  unfold hmacSha512 Spec.hmacSha512
  simp only [sha512_eq, spA_append, xorConst_eq, hmacKey0Sha512_eq]
  rfl

/-! ### MGF1 -/

/-- MGF1-SHA-512 agrees on every seed and every output length (both sides use `⌈l / 64⌉` blocks
and reduce the counter modulo `2^32`). -/
theorem mgf1Sha512_eq (seed : ByteArray) (l : Nat) :
    spA (mgf1Sha512 seed l) = Spec.mgf1 Spec.sha512 64 (spA seed) l := by
  unfold mgf1Sha512 Spec.mgf1
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [spA_extract, append_loop, List.range_eq_range']
  simp [sha512_eq, u32be_ofNat]
  rfl

end MLink

#print axioms MLink.sha512_eq
#print axioms MLink.hmacSha512_eq
#print axioms MLink.mgf1Sha512_eq
