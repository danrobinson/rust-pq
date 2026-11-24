import MLink.Sha256
import MLink.Sha512
import MLink.Encoding
import ToMathlib.Data.ByteArray

/-!
# The six SLH-DSA-SHA2 hash functions, all six parameter sets: `Spec` = VCVio's `sha2Primitives`

Which concrete function each one is (FIPS 205 §11.2.1 for `n = 16`, §11.2.2 for `n = 24, 32`):

| function | `n = 16` (128s, 128f) | `n = 24, 32` (192s, 192f, 256s, 256f) |
|---|---|---|
| `F`, `PRF` | SHA-256, padding `64 − n` | SHA-256, padding `64 − n` |
| `H`, `T_l` | SHA-256, padding `64 − n` | SHA-512, padding `128 − n` |
| `PRF_msg` | HMAC-SHA-256 | HMAC-SHA-512 |
| `H_msg` | MGF1-SHA-256 of SHA-256 | MGF1-SHA-512 of SHA-512 |

VCVio's `sha2Thash` selects by arity: a singleton list is hashed by the `F` formula in every
category, so `Tl_eq` needs `ys.length ≠ 1` (FIPS only uses `T_len`, `T_k`, with `len ≥ 35`,
`k ≥ 14`).
-/

namespace MLink

open SLHDSA SLHDSA.Concrete

open VCVio.Algorithms.Sha2

/-! ### Helpers -/

theorem Sha2Set.n_le_32 (S : Sha2Set) : S.vp.params.n ≤ 32 := by cases S <;> decide

theorem spec_sha256_length (x : Spec.Bytes) : (Spec.sha256 x).length = 32 := by
  have h : spA (sha256 (ByteArray.mk (cv x).toArray)) = Spec.sha256 (sp (cv x)) := sha256_eq _
  rw [sp_cv] at h
  rw [← h, spA_length, sha256_size]

theorem spec_hmacSha256_length (k x : Spec.Bytes) : (Spec.hmacSha256 k x).length = 32 := by
  unfold Spec.hmacSha256
  exact spec_sha256_length _

theorem spec_hmacSha512_length (k x : Spec.Bytes) : (Spec.hmacSha512 k x).length = 64 := by
  unfold Spec.hmacSha512
  exact spec_sha512_length _

private theorem ifPos {α} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]
private theorem ifNeg {α} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := by simp [h]
private theorem nd_def {n : Nat} (y : Bytes n) : nd y = sp y.toList := rfl

private theorem flatMap_length_const {α β} (f : α → List β) (c : Nat)
    (h : ∀ a, (f a).length = c) (l : List α) : (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, h, Nat.succ_mul, Nat.add_comm]

/-- MGF1-SHA-256 returns exactly the requested number of bytes. -/
theorem spec_mgf1Sha256_length (x : Spec.Bytes) (l : Nat) :
    (Spec.mgf1 Spec.sha256 32 x l).length = l := by
  unfold Spec.mgf1
  rw [List.length_take, flatMap_length_const _ 32 (fun _ => spec_sha256_length _),
    List.length_range]
  omega

/-- MGF1-SHA-512 returns exactly the requested number of bytes. -/
theorem spec_mgf1Sha512_length (x : Spec.Bytes) (l : Nat) :
    (Spec.mgf1 Spec.sha512 64 x l).length = l := by
  unfold Spec.mgf1
  rw [List.length_take, flatMap_length_const _ 64 (fun _ => spec_sha512_length _),
    List.length_range]
  omega

private theorem prefixChecked_ok (b : ByteArray) (n : Nat) (h : n ≤ b.size) :
    ∃ v : Bytes n, byteArrayPrefixChecked b n = .ok v ∧ sp v.toList = (spA b).take n := by
  have hraw : (b.extract 0 n).toList = b.data.toList.take n := by
    rw [ByteArray.toList_eq_toList_data, ByteArray.data_extract, Array.toList_extract]
    simp
  have hl : (b.extract 0 n).toList.length = n := by
    rw [hraw, List.length_take]
    have : b.data.toList.length = b.size := by rw [Array.length_toList]; rfl
    omega
  refine ⟨⟨(b.extract 0 n).toList.toArray, by simpa using hl⟩, ?_, ?_⟩
  · simp [byteArrayPrefixChecked, decodeExact, hl]
  · simp [spA, hraw]

private theorem prefixOrZero_eq (b : ByteArray) (n : Nat) (h : n ≤ b.size) :
    nd (byteArrayPrefixOrZero b n) = (spA b).take n := by
  obtain ⟨v, hv, hs⟩ := prefixChecked_ok b n h
  simp [nd, byteArrayPrefixOrZero, hv, hs]

private theorem spA_bytes {n : Nat} (v : Bytes n) : spA (bytesToByteArray v) = nd v := rfl

private theorem spA_zero (n : Nat) : spA (zeroByteArray n) = Spec.toByte 0 n := by
  simp [spA, sp, zeroByteArray, Spec.toByte]

private theorem spA_concat {n : Nat} (ys : List (Bytes n)) : spA (concatBytes ys) = nds ys := by
  unfold concatBytes
  suffices h : ∀ (acc : ByteArray),
      spA (ys.foldl (fun out value => out ++ bytesToByteArray value) acc) = spA acc ++ nds ys by
    simpa [spA] using h ByteArray.empty
  induction ys with
  | nil => intro acc; simp [nds]
  | cons y ys ih => intro acc; simp [ih, nds, spA_bytes]

private theorem spA_prefix256 {n : Nat} (pk : Bytes n) (k : Bytes 22) :
    spA (sha2Prefix256Key pk k) = nd pk ++ Spec.toByte 0 (64 - n) ++ nd k := by
  simp [sha2Prefix256Key, spA_bytes, spA_zero]

private theorem spA_prefix512 {n : Nat} (pk : Bytes n) (k : Bytes 22) :
    spA (sha2Prefix512Key pk k) = nd pk ++ Spec.toByte 0 (128 - n) ++ nd k := by
  simp [sha2Prefix512Key, spA_bytes, spA_zero]

variable (S : Sha2Set)

/-! ### Which concrete function `S.prims.Thash` is (VCVio level, raw 22-byte key)

`S.prims.Thash = sha2Thash S.vp.params` dispatches first on the arity of the node list and only
then on `n`.  The three lemmas below cover all cases; `nd key` is the byte reading of the 22-byte
key (for an in-domain address, `ADRSc`, see `adrsKey_eq`). -/

/-- (a) Arity one, every parameter set: `Trunc_n(SHA-256(PK.seed ‖ 0^(64−n) ‖ key ‖ y))`. -/
theorem thash_singleton_sha256 (pk : S.Node) (key : Bytes 22) (ys : List S.Node)
    (hys : ys.length = 1) :
    nd (S.prims.Thash pk key ys) =
      (Spec.sha256 (nd pk ++ Spec.toByte 0 (64 - S.vp.params.n) ++ nd key ++ nds ys)).take
        S.vp.params.n := by
  have h : S.prims.Thash pk key ys =
      byteArrayPrefixOrZero (sha256 (sha2Prefix256Key pk key ++ concatBytes ys))
        S.vp.params.n := by
    show sha2Thash S.vp.params pk key ys = _
    unfold sha2Thash
    simp only [hys, ite_true]
  rw [h, prefixOrZero_eq _ _ (by rw [sha256_size]; have := S.n_le_32; omega), sha256_eq, spA_append,
    spA_prefix256, spA_concat]

/-- (b) Arity other than one, `n = 16` (128s, 128f): the same SHA-256 form. -/
theorem thash_sha256_of_n16 (pk : S.Node) (key : Bytes 22) (ys : List S.Node)
    (hys : ys.length ≠ 1) (hn : S.vp.params.n = 16) :
    nd (S.prims.Thash pk key ys) =
      (Spec.sha256 (nd pk ++ Spec.toByte 0 (64 - S.vp.params.n) ++ nd key ++ nds ys)).take
        S.vp.params.n := by
  have h : S.prims.Thash pk key ys =
      byteArrayPrefixOrZero (sha256 (sha2Prefix256Key pk key ++ concatBytes ys))
        S.vp.params.n := by
    show sha2Thash S.vp.params pk key ys = _
    unfold sha2Thash
    simp only [hys, ite_false]
    rw [ifPos hn]
  rw [h, prefixOrZero_eq _ _ (by rw [sha256_size]; have := S.n_le_32; omega), sha256_eq, spA_append,
    spA_prefix256, spA_concat]

/-- (c) Arity other than one, `n ≠ 16` (192s, 192f, 256s, 256f):
`Trunc_n(SHA-512(PK.seed ‖ 0^(128−n) ‖ key ‖ ys))`. -/
theorem thash_sha512_of_n_ne_16 (pk : S.Node) (key : Bytes 22) (ys : List S.Node)
    (hys : ys.length ≠ 1) (hn : S.vp.params.n ≠ 16) :
    nd (S.prims.Thash pk key ys) =
      (Spec.sha512 (nd pk ++ Spec.toByte 0 (128 - S.vp.params.n) ++ nd key ++ nds ys)).take
        S.vp.params.n := by
  have h : S.prims.Thash pk key ys =
      byteArrayPrefixOrZero (sha512 (sha2Prefix512Key pk key ++ concatBytes ys))
        S.vp.params.n := by
    show sha2Thash S.vp.params pk key ys = _
    unfold sha2Thash
    simp only [hys, ite_false]
    rw [ifNeg hn]
  rw [h, prefixOrZero_eq _ _ (by rw [sha512_size]; have := S.n_le_32; omega), sha512_eq, spA_append,
    spA_prefix512, spA_concat]

private theorem spec_sha2 (S : Sha2Set) : S.spec.family = .sha2 := by cases S <;> rfl

/-! ### Key-level and address-level forms in terms of `Spec` -/

/-- The tweakable hash at a raw key and a single node: the `F` formula of the spec with the key
bytes in place of `ADRSc`. -/
theorem thash_key_singleton_eq (pk : S.Node) (k : Bytes 22) (y : S.Node) :
    nd (S.prims.Thash pk k [y]) =
      (Spec.sha256 (nd pk ++ Spec.toByte 0 (64 - S.spec.n) ++ nd k ++ nd y)).take S.spec.n := by
  have := thash_singleton_sha256 S pk k [y] rfl
  rw [← S.n_eq]
  simp only [nds, List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  exact this

/-- The tweakable hash at a raw key and a non-singleton list: the `H`/`T_l` formula of the spec
with the key bytes in place of `ADRSc`. -/
theorem thash_key_eq (pk : S.Node) (k : Bytes 22) (ys : List S.Node) (hys : ys.length ≠ 1) :
    nd (S.prims.Thash pk k ys) =
      if S.spec.n = 16 then
        (Spec.sha256 (nd pk ++ Spec.toByte 0 (64 - S.spec.n) ++ nd k ++ nds ys)).take S.spec.n
      else
        (Spec.sha512 (nd pk ++ Spec.toByte 0 (128 - S.spec.n) ++ nd k ++ nds ys)).take
          S.spec.n := by
  rw [← S.n_eq]
  by_cases hn : S.vp.params.n = 16
  · rw [ifPos hn]; exact thash_sha256_of_n16 S pk k ys hys hn
  · rw [ifNeg hn]; exact thash_sha512_of_n_ne_16 S pk k ys hys hn

/-- The tweakable hash at an in-domain address, non-singleton list (`H`, `T_l`). -/
theorem thash_eq (pk : S.Node) (a : SLHDSA.Adrs) (h : Dom a) (ys : List S.Node)
    (hys : ys.length ≠ 1) :
    nd (S.prims.Thash pk (S.prims.adrsToKey a) ys) = Spec.T S.spec (nd pk) (adr a) (nds ys) := by
  have := thash_key_eq S pk (sha2AdrsKey a) ys hys
  rw [show nd (sha2AdrsKey a) = (adr a).compress from adrsKey_eq a h] at this
  simp only [Spec.T, spec_sha2]
  exact this

/-- `F` at an in-domain address (SHA-256 in every category). -/
theorem F_eq (pk : S.Node) (a : SLHDSA.Adrs) (h : Dom a) (y : S.Node) :
    nd (S.prims.F pk a y) = Spec.F S.spec (nd pk) (adr a) (nd y) := by
  have := thash_key_singleton_eq S pk (sha2AdrsKey a) y
  rw [show nd (sha2AdrsKey a) = (adr a).compress from adrsKey_eq a h] at this
  simp only [Spec.F, spec_sha2]
  exact this

/-- `H` at an in-domain address (SHA-256 for `n = 16`, SHA-512 otherwise). -/
theorem H_eq (pk : S.Node) (a : SLHDSA.Adrs) (h : Dom a) (l r : S.Node) :
    nd (S.prims.H pk a l r) = Spec.H S.spec (nd pk) (adr a) (nd l ++ nd r) := by
  have := thash_eq S pk a h [l, r] (by simp)
  simp only [nds, List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  exact this

/-- `T_l` at an in-domain address, for a list that is not a singleton
(SHA-256 for `n = 16`, SHA-512 otherwise). -/
theorem Tl_eq (pk : S.Node) (a : SLHDSA.Adrs) (h : Dom a) (ys : List S.Node)
    (hys : ys.length ≠ 1) :
    nd (S.prims.Tl pk a ys) = Spec.T S.spec (nd pk) (adr a) (nds ys) :=
  thash_eq S pk a h ys hys

/-- `PRF` at an in-domain address (SHA-256 in every category). -/
theorem PRF_eq (pk sk : S.Node) (a : SLHDSA.Adrs) (h : Dom a) :
    nd (S.prims.PRF pk sk a) = Spec.PRF S.spec (nd pk) (nd sk) (adr a) := by
  obtain ⟨v, hv, hs⟩ := prefixChecked_ok
    (sha256 (sha2Prefix256 pk ⟨a, h.1, h.2.1, h.2.2⟩ ++ bytesToByteArray sk)) S.vp.params.n
    (by rw [sha256_size]; have := S.n_le_32; omega)
  have e : S.prims.PRF pk sk a = v := by
    show checkedNodeOrZero (sha2PRFChecked pk sk a) = v
    simp only [sha2PRFChecked, Sha2Address.ofAdrs, h.1, h.2.1, h.2.2, dite_true]
    show checkedNodeOrZero (byteArrayPrefixChecked _ _) = v
    rw [hv]; rfl
  rw [e, nd, hs, sha256_eq, spA_append, sha2Prefix256, spA_prefix256]
  simp only [nd_def, Sha2Address.bytes_toList, compressSha2_eq, spA_bytes]
  unfold Spec.PRF
  rw [spec_sha2]
  rw [← S.n_eq]

/-- `PRF_msg` (HMAC-SHA-256 for `n = 16`, HMAC-SHA-512 otherwise). -/
theorem PRFmsg_eq (skPrf optRand : S.Node) (msg : List UInt8) :
    nd (S.prims.PRFmsg skPrf optRand msg) = Spec.PRFmsg S.spec (nd skPrf) (nd optRand) (sp msg) := by
  have hle := S.n_le_32
  show nd (sha2PRFmsg skPrf optRand msg) = _
  unfold sha2PRFmsg Spec.PRFmsg
  rw [spec_sha2]
  rw [← S.n_eq]
  by_cases hn : S.vp.params.n = 16
  · rw [ifPos hn, ifPos hn]
    rw [prefixOrZero_eq _ _ (by
      rw [← spA_length, hmacSha256_eq, spec_hmacSha256_length]; omega), hmacSha256_eq, spA_append,
      spA_bytes, spA_bytes, spA_mk]
  · rw [ifNeg hn, ifNeg hn]
    rw [prefixOrZero_eq _ _ (by
      rw [← spA_length, hmacSha512_eq, spec_hmacSha512_length]; omega), hmacSha512_eq, spA_append,
      spA_bytes, spA_bytes, spA_mk]

/-- `H_msg` (`m`-byte digest; MGF1-SHA-256 for `n = 16`, MGF1-SHA-512 otherwise). -/
theorem Hmsg_eq (r pk root : S.Node) (msg : List UInt8) :
    nd (S.prims.Hmsg r pk root msg) = Spec.Hmsg S.spec (nd r) (nd pk) (nd root) (sp msg) := by
  show nd (sha2Hmsg S.vp.params r pk root msg) = _
  unfold sha2Hmsg Spec.Hmsg
  rw [spec_sha2]
  rw [← S.n_eq, ← S.m_eq]
  by_cases hn : S.vp.params.n = 16
  · rw [ifPos hn, ifPos hn]
    rw [prefixOrZero_eq _ _ (by
      rw [← spA_length, mgf1Sha256_eq, spec_mgf1Sha256_length]), mgf1Sha256_eq,
      List.take_of_length_le (le_of_eq (spec_mgf1Sha256_length _ _))]
    simp only [spA_append, spA_bytes, spA_mk, sha256_eq]
  · rw [ifNeg hn, ifNeg hn]
    rw [prefixOrZero_eq _ _ (by
      rw [← spA_length, mgf1Sha512_eq, spec_mgf1Sha512_length]), mgf1Sha512_eq,
      List.take_of_length_le (le_of_eq (spec_mgf1Sha512_length _ _))]
    simp only [spA_append, spA_bytes, spA_mk, sha512_eq]

end MLink

#print axioms MLink.thash_singleton_sha256
#print axioms MLink.thash_sha256_of_n16
#print axioms MLink.thash_sha512_of_n_ne_16
#print axioms MLink.thash_key_singleton_eq
#print axioms MLink.thash_key_eq
#print axioms MLink.thash_eq
#print axioms MLink.F_eq
#print axioms MLink.H_eq
#print axioms MLink.Tl_eq
#print axioms MLink.PRF_eq
#print axioms MLink.PRFmsg_eq
#print axioms MLink.Hmsg_eq
