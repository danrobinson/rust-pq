import MLink.Basic

/-!
# SHA-256, HMAC-SHA-256 and MGF1-SHA-256: `Spec` = VCVio

VCVio's `VCVio.Algorithms.Sha2` is imperative (`Id.run do` loops over `ByteArray` / `Array UInt32`);
`Spec.SHA256` is a list-fold transcription of FIPS 180-4.
-/

namespace MLink

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

theorem spA_get (m : ByteArray) (i : Nat) : (spA m)[i]! = (m[i]!).toBitVec := by
  by_cases h : i < m.size
  · simp [spA, sp, h]
    rfl
  · simp [spA, sp, h]
    rfl

@[simp] theorem spA_length (m : ByteArray) : (spA m).length = m.size := by
  simp [spA, sp]

theorem spA_push (m : ByteArray) (x : UInt8) : spA (m.push x) = spA m ++ [x.toBitVec] := by
  simp [spA, sp]

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

theorem ssig0_eq (x : UInt32) : (ssig0 x).toBitVec = Spec.SHA256.ssig0 x.toBitVec := by
  simp [ssig0, Spec.SHA256.ssig0, rotr, BitVec.rotateRight, BitVec.rotateRightAux]
theorem ssig1_eq (x : UInt32) : (ssig1 x).toBitVec = Spec.SHA256.ssig1 x.toBitVec := by
  simp [ssig1, Spec.SHA256.ssig1, rotr, BitVec.rotateRight, BitVec.rotateRightAux]
theorem bsig0_eq (x : UInt32) : (bsig0 x).toBitVec = Spec.SHA256.bsig0 x.toBitVec := by
  simp [bsig0, Spec.SHA256.bsig0, rotr, BitVec.rotateRight, BitVec.rotateRightAux]
theorem bsig1_eq (x : UInt32) : (bsig1 x).toBitVec = Spec.SHA256.bsig1 x.toBitVec := by
  simp [bsig1, Spec.SHA256.bsig1, rotr, BitVec.rotateRight, BitVec.rotateRightAux]
theorem ch_eq (x y z : UInt32) :
    (ch x y z).toBitVec = Spec.SHA256.ch x.toBitVec y.toBitVec z.toBitVec := by
  simp [ch, Spec.SHA256.ch]
theorem maj_eq (x y z : UInt32) :
    (maj x y z).toBitVec = Spec.SHA256.maj x.toBitVec y.toBitVec z.toBitVec := by
  simp [maj, Spec.SHA256.maj]
theorem W_k : W k = Spec.SHA256.K := by decide
theorem W_iv : W iv = Spec.SHA256.H0 := by decide

/-! ### List helpers -/

theorem take_set_succ {α} (l : List α) (n : Nat) (v : α) (h : n < l.length) :
    (l.set n v).take (n + 1) = l.take n ++ [v] := by
  rw [List.take_add_one, List.take_set_of_le (Nat.le_refl _)]
  simp [h]

theorem take_get {α} [Inhabited α] (l : List α) (n i : Nat) (h : i < n) :
    (l.take n)[i]! = l[i]! := by
  simp [h]

theorem blockAt_get (p : Spec.Bytes) (k j : Nat) (h : j < 64) :
    (Spec.SHA256.blockAt p k)[j]! = p[64 * k + j]! := by
  simp [Spec.SHA256.blockAt, h]

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

open Spec.SHA256 in
theorem expand_take (n : Nat) (w0 : Array UInt32) (hs : w0.size = 64) (h : 16 + n ≤ 64) :
    (List.foldl (fun b a => b.setIfInBounds a
        (ssig1 b[a - 2]! + b[a - 7]! + ssig0 b[a - 15]! + b[a - 16]!)) w0
      (List.range' 16 n)).size = 64 ∧
    (W (List.foldl (fun b a => b.setIfInBounds a
        (ssig1 b[a - 2]! + b[a - 7]! + ssig0 b[a - 15]! + b[a - 16]!)) w0
      (List.range' 16 n))).take (16 + n) = Nat.repeat scheduleStep n ((W w0).take 16) := by
  induction n with
  | zero => simp [Nat.repeat, hs]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append]
    refine ⟨by simp [h1], ?_⟩
    simp only [List.foldl_cons, List.foldl_nil, W_set, Nat.one_mul]
    rw [← Nat.add_assoc, take_set_succ _ _ _ (by simp [h1]; omega), Nat.repeat, ← h2]
    simp only [scheduleStep, List.length_take, W_length, h1, Nat.min_eq_left (show 16 + n ≤ 64 by omega)]
    rw [take_get _ _ _ (by omega), take_get _ _ _ (by omega), take_get _ _ _ (by omega),
      take_get _ _ _ (by omega)]
    simp only [W_get, ssig0_eq, ssig1_eq, UInt32.toBitVec_add, Nat.add_sub_cancel_left]

theorem readWord_eq (m : ByteArray) (k t : Nat) (ht : t < 16) :
    (readWord256 m (k * 64) t).toBitVec
      = Spec.SHA256.word (Spec.SHA256.blockAt (spA m) k) (4 * t) := by
  unfold readWord256 Spec.SHA256.word
  rw [be32, blockAt_get _ _ _ (by omega), blockAt_get _ _ _ (by omega),
    blockAt_get _ _ _ (by omega), blockAt_get _ _ _ (by omega)]
  rw [show 64 * k + 4 * t = k * 64 + t * 4 by omega,
    show 64 * k + (4 * t + 1) = k * 64 + t * 4 + 1 by omega,
    show 64 * k + (4 * t + 2) = k * 64 + t * 4 + 2 by omega,
    show 64 * k + (4 * t + 3) = k * 64 + t * 4 + 3 by omega]
  simp only [spA_get]

theorem loadSchedule_eq (m : ByteArray) (k : Nat) :
    (loadSchedule256 m (k * 64)).size = 64 ∧
    (W (loadSchedule256 m (k * 64))).take 16
      = Spec.SHA256.blockWords (Spec.SHA256.blockAt (spA m) k) := by
  have := load_take (readWord256 m (k * 64)) 16 (Array.replicate 64 0) (by simp)
  unfold loadSchedule256
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] 
  simp
  refine ⟨by simpa using this.1, ?_⟩
  rw [this.2, Spec.SHA256.blockWords]
  apply List.map_congr_left
  intro t ht
  exact readWord_eq m k t (by simpa using ht)

theorem schedule_eq (m : ByteArray) (k : Nat) :
    W (expandSchedule256 (loadSchedule256 m (k * 64)))
      = Spec.SHA256.schedule (Spec.SHA256.blockAt (spA m) k) := by
  obtain ⟨h1, h2⟩ := loadSchedule_eq m k
  have := expand_take 48 _ h1 (by omega)
  unfold expandSchedule256 Spec.SHA256.schedule
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [← h2, ← this.2, List.take_of_length_le (by simp [this.1])]

/-! ### Rounds and compression -/

/-- Read a VCVio round state as a spec state. -/
def R (s : RoundState) : Spec.SHA256.State :=
  (s.a.toBitVec, s.b.toBitVec, s.c.toBitVec, s.d.toBitVec,
    s.e.toBitVec, s.f.toBitVec, s.g.toBitVec, s.h.toBitVec)

theorem round_eq (w : Array UInt32) (s : RoundState) (t : Nat) :
    R (round256 s k[t]! w[t]!) = Spec.SHA256.round (W w) (R s) t := by
  have hk : Spec.SHA256.K[t]! = (k[t]!).toBitVec := by rw [← W_k, W_get]
  simp only [round256, Spec.SHA256.round, R, hk, W_get]
  simp [bsig0_eq, bsig1_eq, ch_eq, maj_eq]

theorem runRounds_eq (st w : Array UInt32) :
    R (runRounds256 st w) = (List.range 64).foldl (Spec.SHA256.round (W w))
      ((W st)[0]!, (W st)[1]!, (W st)[2]!, (W st)[3]!, (W st)[4]!, (W st)[5]!, (W st)[6]!,
        (W st)[7]!) := by
  unfold runRounds256
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [foldl_rel R _ (Spec.SHA256.round (W w)) (fun a c => round_eq w a c), List.range_eq_range']
  simp only [R, W_get']

theorem compress_eq (st : Array UInt32) (m : ByteArray) (k : Nat) :
    W (compress st m (k * 64)) = Spec.SHA256.compress (W st) (Spec.SHA256.blockAt (spA m) k) := by
  unfold compress Spec.SHA256.compress
  simp only
  rw [← schedule_eq, ← runRounds_eq]
  simp only [R, W_get]
  simp [W, feedForward256]

theorem compress_size (st : Array UInt32) (m : ByteArray) (b : Nat) :
    (compress st m b).size = 8 := by
  simp [compress, feedForward256]

/-! ### Padding and serialization -/

theorem push_loop {γ} (c : UInt8) (l : List γ) (out : ByteArray) :
    spA (l.foldl (fun b _ => b.push c) out) = spA out ++ List.replicate l.length c.toBitVec := by
  induction l generalizing out with
  | nil => simp
  | cons x xs ih => simp [ih, spA_push, List.replicate_succ]

theorem u32be_eq (x : UInt32) : spA (u32be x) = Spec.toByte x.toNat 4 := by
  simp [u32be, spA, sp, Spec.toByte, List.range_succ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp [Nat.shiftRight_eq_div_pow]

theorem u64be_eq (n : Nat) : spA (u64be (UInt64.ofNat n * 8)) = Spec.toByte (8 * n) 8 := by
  simp [u64be, spA, sp, Spec.toByte, List.range_succ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp [Nat.shiftRight_eq_div_pow] <;> omega

theorem pad_eq (m : ByteArray) : spA (pad m) = Spec.SHA256.pad (spA m) := by
  unfold pad Spec.SHA256.pad
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [push_loop, spA_push, u64be_eq]
  have : (120 - (m.size + 1) % 64) % 64 = (119 - m.size % 64) % 64 := by omega
  simp [this]

theorem stateBytes_eq (st : Array UInt32) (hs : st.size = 8) :
    spA ((stateBytes32 st).extract 0 32) = (W st).flatMap fun w => Spec.toByte w.toNat 4 := by
  have := @ByteArray.extract_zero_size (stateBytes32 st)
  rw [stateBytes32_size] at this
  rw [this]
  obtain ⟨l⟩ := st
  simp at hs
  match l, hs with
  | [a, b, c, d, e, f, g, h], _ =>
    simp [W, ← u32be_eq, stateBytes32, spA, sp, u32be]
    repeat' apply And.intro
    all_goals rfl

/-! ### SHA-256 -/

theorem blocks_eq (p : ByteArray) (l : List Nat) (st : Array UInt32) (hs : st.size = 8) :
    (l.foldl (fun b a => compress b p (a * 64)) st).size = 8 ∧
    W (l.foldl (fun b a => compress b p (a * 64)) st)
      = l.foldl (fun st k => Spec.SHA256.compress st (Spec.SHA256.blockAt (spA p) k)) (W st) := by
  induction l generalizing st with
  | nil => exact ⟨hs, rfl⟩
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [← compress_eq]
    exact ih _ (compress_size _ _ _)

/-- SHA-256 agrees on every input. -/
theorem sha256_eq (b : ByteArray) : spA (sha256 b) = Spec.sha256 (spA b) := by
  unfold sha256 sha256Family Spec.SHA256.sha256
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  obtain ⟨h1, h2⟩ := blocks_eq (pad b) (List.range' 0 ((pad b).size / 64)) iv rfl
  rw [stateBytes_eq _ h1, h2, W_iv, ← pad_eq, spA_length, List.range_eq_range']

/-! ### HMAC -/

theorem xor_loop (b : ByteArray) (c : UInt8) (n : Nat) (h : n ≤ b.size) :
    spA ((List.range' 0 n).foldl (fun out i => out.push (b[i]! ^^^ c)) ByteArray.empty)
      = ((spA b).take n).map (· ^^^ c.toBitVec) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : (spA b)[n]? = some (b[n]!).toBitVec := by
      rw [← spA_get]; simp [show n < b.size by omega]
    rw [List.range'_concat, List.foldl_append]
    simp [spA_push, ih (by omega), List.take_add_one, hn]

theorem xorConst_eq (b : ByteArray) (c : UInt8) :
    spA (xorConst b c) = (spA b).map (· ^^^ c.toBitVec) := by
  unfold xorConst
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  have := xor_loop b c b.size (Nat.le_refl _)
  rw [this, List.take_of_length_le (by simp)]

theorem hmacKey0_eq (key : ByteArray) :
    spA (hmacKey0 key) =
      (if (spA key).length > 64 then Spec.sha256 (spA key) else spA key) ++
        List.replicate (64 - (if (spA key).length > 64 then Spec.sha256 (spA key)
          else spA key).length) 0#8 := by
  unfold hmacKey0
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [push_loop]
  have hl : (Spec.sha256 (spA key)).length = 32 := by rw [← sha256_eq, spA_length, sha256_size]
  split <;> simp [sha256_eq, hl]

/-- HMAC-SHA-256 agrees on every key and message. -/
theorem hmacSha256_eq (key msg : ByteArray) :
    spA (hmacSha256 key msg) = Spec.hmacSha256 (spA key) (spA msg) := by
  unfold hmacSha256 Spec.hmacSha256
  simp only [sha256_eq, spA_append, xorConst_eq, hmacKey0_eq]
  rfl

/-! ### MGF1 -/

theorem append_loop {γ} (g : γ → ByteArray) (l : List γ) (out : ByteArray) :
    spA (l.foldl (fun o c => o ++ g c) out) = spA out ++ l.flatMap (fun c => spA (g c)) := by
  induction l generalizing out with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem u32be_ofNat (c : Nat) : spA (u32be c.toUInt32) = Spec.toByte c 4 := by
  rw [u32be_eq]
  simp [Spec.toByte, List.range_succ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp [Nat.shiftRight_eq_div_pow] <;> omega

theorem spA_extract (b : ByteArray) (l : Nat) : spA (b.extract 0 l) = (spA b).take l := by
  simp [spA, sp, List.map_take]

/-- MGF1-SHA-256 agrees on every seed and every output length.  No bound on `l` is needed: both
sides use `⌈l / 32⌉` blocks and both reduce the block counter modulo `2^32` (VCVio by
`Nat.toUInt32`, the spec by `toByte c 4`), so they agree even past RFC 8017's limit
`l ≤ 2^32 · 32`. -/
theorem mgf1Sha256_eq (seed : ByteArray) (l : Nat) :
    spA (mgf1Sha256 seed l) = Spec.mgf1 Spec.sha256 32 (spA seed) l := by
  unfold mgf1Sha256 mgf1 Spec.mgf1
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [spA_extract, append_loop, List.range_eq_range']
  simp [sha256_eq, u32be_ofNat]
  rfl

end MLink

#print axioms MLink.sha256_eq
#print axioms MLink.hmacSha256_eq
#print axioms MLink.mgf1Sha256_eq
