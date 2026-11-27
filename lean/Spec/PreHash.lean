import Spec.Correctness
import Spec.ShakeWords

/-!
# FIPS 202 SHAKE128 and FIPS 205 HashSLH-DSA (Algorithms 23 & 25)

An independent transcription of:
- FIPS 202 §6.2 `SHAKE128` (rate = 168 bytes / 1344 bits, domain byte `0x1f`,
  final pad bit `0x80` at rate byte 167, reusing `Spec.Keccak.permute`).
- FIPS 205 §10.2.2 / §10.3.2 (`PreHash`, DER OIDs, `prehashDigest`, `prehashFrame`,
  `hashSlhSignPrehashed`, `hashSlhVerifyPrehashed`, `hashSlhSign`, `hashSlhVerify`).
- Specification-level completeness for every valid parameter set (`Params.Valid`,
  all 12 SHA-2 and SHAKE parameter sets of Table 2).
-/

namespace Spec.PreHash

/-! ## SHAKE128 (FIPS 202 §6.2, rate = 168 bytes) -/

/-- Rate of SHAKE128 in bytes (`1344 / 8 = 168`). -/
def rate128 : Nat := 168

/-- Absorb one byte into a SHAKE128 sponge, permuting after each complete 1344-bit rate block. -/
def feed128 (s : Keccak.State × Nat) (b : Byte) : Keccak.State × Nat :=
  let lanes := Keccak.xorByte s.1 s.2 b
  if s.2 + 1 = 168 then (Keccak.permute lanes, 0) else (lanes, s.2 + 1)

/-- Pad with SHAKE domain separator `0x1f` and final `pad10*1` bit `0x80` at byte 167,
then permute. -/
def finalize128 (s : Keccak.State × Nat) : Keccak.State :=
  Keccak.permute (Keccak.xorByte (Keccak.xorByte s.1 s.2 0x1f) 167 0x80)

/-- Squeeze `n` bytes from a SHAKE128 state, permuting whenever 168 bytes have been extracted. -/
def squeeze128 (a : Keccak.State) (pos : Nat) : Nat → Bytes
  | 0 => []
  | n + 1 =>
    let (block, atPos) := if pos = 168 then (Keccak.permute a, 0) else (a, pos)
    Keccak.extractByte block atPos :: squeeze128 block (atPos + 1) n

/-- FIPS 202 SHAKE128 on byte strings, with the requested output length in bytes. -/
def shake128 (m : Bytes) (length : Nat) : Bytes :=
  let a := finalize128 (m.foldl feed128 Keccak.initial)
  squeeze128 a 0 length

@[simp] theorem squeeze128_length (a : Keccak.State) (pos n : Nat) :
    (squeeze128 a pos n).length = n := by
  induction n generalizing a pos with
  | zero => rfl
  | succ n ih => simp [squeeze128, ih]

@[simp] theorem shake128_length (m : Bytes) (n : Nat) : (shake128 m n).length = n := by
  simp [shake128]

private theorem feedWithin128 (a : Keccak.State) (lane k : Nat) (input : Bytes)
    (valid : lane < a.size) (bounded : k + input.length ≤ 8)
    (within : 8 * lane + k + input.length < 168) :
    input.foldl feed128 (a, 8 * lane + k) =
      (a.setIfInBounds lane (a[lane]! ^^^ Keccak.laneBytes k input),
       8 * lane + k + input.length) := by
  induction input generalizing a k with
  | nil =>
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero, Keccak.laneBytes]
    congr 1
    apply Array.ext <;> simp_all [Array.getElem_setIfInBounds, getElem!_pos]
  | cons b bs ih =>
    simp only [List.length_cons] at bounded within ⊢
    have bytePos : k < 8 := by omega
    have idx : (8 * lane + k) / 8 = lane := by omega
    have offset : (8 * lane + k) % 8 = k := by omega
    have hne : 8 * lane + k + 1 ≠ 168 := by omega
    simp only [List.foldl_cons, feed128, Keccak.xorByte, idx, offset, hne, ↓reduceIte]
    rw [show 8 * lane + k + 1 = 8 * lane + (k + 1) by omega,
      ih _ _ (by simpa) (by omega) (by omega)]
    congr 1
    · apply Array.ext
      · simp
      · intro j hj hj'
        by_cases same : lane = j
        · subst j
          simp (disch := simp_all) [getElem!_pos, Keccak.laneBytes, BitVec.xor_assoc]
        · simp (disch := simp_all)
    · omega

private theorem laneBytes_append (k : Nat) (xs ys : Bytes) :
    Keccak.laneBytes k (xs ++ ys) =
      Keccak.laneBytes k xs ^^^ Keccak.laneBytes (k + xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [Keccak.laneBytes]
  | cons b xs ih =>
    simp [Keccak.laneBytes, ih, BitVec.xor_assoc, Nat.add_assoc, Nat.add_comm]

/-- Absorbing one lane-aligned 8-byte word into SHAKE128 is equivalent to eight
FIPS 202 byte steps, including the permutation when lane 20 completes the 168-byte rate block. -/
theorem feedWord128 (a : Keccak.State) (lane : Nat) (input : Bytes) (eight : input.length = 8)
    (valid : lane < a.size) (rate : lane < 21) :
    input.foldl feed128 (a, 8 * lane) =
      let next := a.setIfInBounds lane (a[lane]! ^^^ Keccak.laneBytes 0 input)
      if lane = 20 then (Keccak.permute next, 0) else (next, 8 * lane + 8) := by
  by_cases last : lane = 20
  · subst lane
    obtain ⟨initBytes, b, rfl⟩ : ∃ l b, input = l ++ [b] := by
      induction input using List.reverseRecOn with
      | nil => simp at eight
      | append_singleton l b _ => exact ⟨l, b, rfl⟩
    have seven : initBytes.length = 7 := by simpa using eight
    rw [List.foldl_append]
    rw [show 8 * 20 = 8 * 20 + 0 by decide,
      feedWithin128 a 20 0 initBytes valid (by omega) (by omega)]
    simp only [seven, List.foldl_cons, List.foldl_nil, feed128, Keccak.xorByte, ite_true]
    simp only [laneBytes_append, seven, Keccak.laneBytes, Nat.zero_add]
    congr 2
    apply Array.ext
    · simp
    · intro j hj hj'
      by_cases eq : j = 20
      · subst j
        simp (disch := simp_all) [getElem!_pos, BitVec.xor_assoc]
      · simp (disch := simp_all) [Array.getElem_setIfInBounds, Ne.symm eq]
  · simp only [last, ↓reduceIte]
    simpa [eight] using feedWithin128 a lane 0 input valid (by omega) (by omega)

/-! ## FIPS 205 HashSLH-DSA (§10.2.2, §10.3.2, Algorithms 23 & 25) -/

set_option linter.dupNamespace false

/-- Approved pre-hash functions for HashSLH-DSA (FIPS 205 §10.2.2 / §10.3.2). -/
inductive PreHash where
  | sha256
  | sha512
  | shake128
  | shake256
deriving Repr, DecidableEq

/-- The 11-byte DER-encoded ASN.1 OBJECT IDENTIFIER for each approved pre-hash function. -/
def PreHash.oid : PreHash → Bytes
  | .sha256   => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01]
  | .sha512   => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03]
  | .shake128 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0b]
  | .shake256 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0c]

/-- Expected digest length in bytes (`32` for SHA-256 / SHAKE128, `64` for SHA-512 / SHAKE256). -/
def PreHash.digestLen : PreHash → Nat
  | .sha256 | .shake128 => 32
  | .sha512 | .shake256 => 64

@[simp] theorem PreHash.oid_length (ph : PreHash) : ph.oid.length = 11 := by
  cases ph <;> rfl

/-- Computes `PH(M)` according to FIPS 205 §10.2.2. -/
def prehashDigest (ph : PreHash) (m : Bytes) : Bytes :=
  match ph with
  | .sha256   => Spec.sha256 m
  | .sha512   => Spec.sha512 m
  | .shake128 => shake128 m 32
  | .shake256 => Spec.shake256 m 64

@[simp] theorem prehashDigest_length (ph : PreHash) (m : Bytes) :
    (prehashDigest ph m).length = ph.digestLen := by
  cases ph <;> simp [prehashDigest, PreHash.digestLen, sha256_length, sha512_length]

/-- FIPS 205 Algorithms 23 & 25 message framing:
`M' = toByte(1, 1) ‖ toByte(|ctx|, 1) ‖ ctx ‖ OID ‖ PH(M)`. -/
def prehashFrame (ctx : Bytes) (ph : PreHash) (phm : Bytes) : Bytes :=
  toByte 1 1 ++ toByte ctx.length 1 ++ ctx ++ ph.oid ++ phm

theorem prehashFrame_eq_cons (ctx : Bytes) (ph : PreHash) (phm : Bytes) :
    prehashFrame ctx ph phm =
      [1#8, BitVec.ofNat 8 ctx.length] ++ ctx ++ ph.oid ++ phm := by
  rfl

/-- Algorithm 23 (`hash_slh_sign`) on a pre-computed digest `phm = PH(M)`.
Returns `none` if `|ctx| > 255` or `|phm| ≠ ph.digestLen`. -/
def hashSlhSignPrehashed (p : Params) (phm ctx : Bytes) (ph : PreHash)
    (sk addrnd : Bytes) : Option Bytes :=
  if ctx.length > 255 ∨ phm.length ≠ ph.digestLen then none
  else some (slhSignInternal p (prehashFrame ctx ph phm) sk addrnd)

/-- Algorithm 25 (`hash_slh_verify`) on a pre-computed digest `phm = PH(M)`.
Returns `false` if `|ctx| > 255` or `|phm| ≠ ph.digestLen`. -/
def hashSlhVerifyPrehashed (p : Params) (phm sig ctx : Bytes) (ph : PreHash)
    (pk : Bytes) : Bool :=
  if ctx.length > 255 ∨ phm.length ≠ ph.digestLen then false
  else slhVerifyInternal p (prehashFrame ctx ph phm) sig pk

/-- Algorithm 23 (`hash_slh_sign`): hashes `m` with `ph` and signs the framed digest. -/
def hashSlhSign (p : Params) (m ctx : Bytes) (ph : PreHash)
    (sk addrnd : Bytes) : Option Bytes :=
  if ctx.length > 255 then none
  else hashSlhSignPrehashed p (prehashDigest ph m) ctx ph sk addrnd

/-- Algorithm 25 (`hash_slh_verify`): hashes `m` with `ph` and verifies `sig`. -/
def hashSlhVerify (p : Params) (m sig ctx : Bytes) (ph : PreHash)
    (pk : Bytes) : Bool :=
  if ctx.length > 255 then false
  else hashSlhVerifyPrehashed p (prehashDigest ph m) sig ctx ph pk

/-! ## Validity of all 6 SHAKE parameter sets (complementing `sha2_*_valid`) -/

theorem shake_128s_valid : shake_128s.Valid := by constructor <;> decide
theorem shake_128f_valid : shake_128f.Valid := by constructor <;> decide
theorem shake_192s_valid : shake_192s.Valid := by constructor <;> decide
theorem shake_192f_valid : shake_192f.Valid := by constructor <;> decide
theorem shake_256s_valid : shake_256s.Valid := by constructor <;> decide
theorem shake_256f_valid : shake_256f.Valid := by constructor <;> decide

/-! ## Completeness & Validation Theorems -/

/-- Completeness of Algorithms 23 & 25 in pre-hashed mode. -/
theorem hashSlh_complete_prehashed (p : Params) (hv : p.Valid) (phm ctx sk addrnd : Bytes)
    (ph : PreHash) (hc : ctx.length ≤ 255) (hd : phm.length = ph.digestLen) (hk : KeyOk p sk) :
    ∃ sig, hashSlhSignPrehashed p phm ctx ph sk addrnd = some sig ∧
      hashSlhVerifyPrehashed p phm sig ctx ph (skPk p sk) = true := by
  have hok : ¬ (ctx.length > 255 ∨ phm.length ≠ ph.digestLen) := by omega
  refine ⟨slhSignInternal p (prehashFrame ctx ph phm) sk addrnd, ?_, ?_⟩
  · simp [hashSlhSignPrehashed, hok]
  · simp only [hashSlhVerifyPrehashed, hok, ↓reduceIte]
    exact slh_complete_internal p hv _ _ _ hk

/-- Completeness of Algorithms 23 & 25: for any valid parameter set, well-formed key,
context `|ctx| ≤ 255`, message `m`, and approved `PreHash` algorithm, `hashSlhVerify`
accepts the signature produced by `hashSlhSign`. -/
theorem hashSlh_complete (p : Params) (hv : p.Valid) (m ctx sk addrnd : Bytes)
    (ph : PreHash) (hc : ctx.length ≤ 255) (hk : KeyOk p sk) :
    ∃ sig, hashSlhSign p m ctx ph sk addrnd = some sig ∧
      hashSlhVerify p m sig ctx ph (skPk p sk) = true := by
  have hc' : ¬ ctx.length > 255 := by omega
  obtain ⟨sig, hsign, hver⟩ := hashSlh_complete_prehashed p hv (prehashDigest ph m) ctx sk addrnd ph
    hc (prehashDigest_length ph m) hk
  exact ⟨sig, by simp [hashSlhSign, hc', hsign], by simp [hashSlhVerify, hc', hver]⟩

theorem hashSlhSign_ctx_gt_255 (p : Params) (m ctx sk addrnd : Bytes) (ph : PreHash)
    (hc : ctx.length > 255) :
    hashSlhSign p m ctx ph sk addrnd = none := by
  simp [hashSlhSign, hc]

theorem hashSlhVerify_ctx_gt_255 (p : Params) (m sig ctx pk : Bytes) (ph : PreHash)
    (hc : ctx.length > 255) :
    hashSlhVerify p m sig ctx ph pk = false := by
  simp [hashSlhVerify, hc]

theorem hashSlhSignPrehashed_bad_len (p : Params) (phm ctx sk addrnd : Bytes) (ph : PreHash)
    (h : ctx.length > 255 ∨ phm.length ≠ ph.digestLen) :
    hashSlhSignPrehashed p phm ctx ph sk addrnd = none := by
  simp [hashSlhSignPrehashed, h]

theorem hashSlhVerifyPrehashed_bad_len (p : Params) (phm sig ctx pk : Bytes) (ph : PreHash)
    (h : ctx.length > 255 ∨ phm.length ≠ ph.digestLen) :
    hashSlhVerifyPrehashed p phm sig ctx ph pk = false := by
  simp [hashSlhVerifyPrehashed, h]

end Spec.PreHash
