import Link.Sha256
import Link.Encoding
import ToMathlib.Data.ByteArray

/-!
# The six SLH-DSA-SHA2-128s hash functions: `Spec` = VCVio's `sha2Primitives`
-/

namespace Link

open SLHDSA SLHDSA.Concrete

open VCVio.Algorithms.Sha2

/-! ### Helpers -/

private theorem spec_sha256_length (x : Spec.Bytes) : (Spec.sha256 x).length = 32 := by
  have h : spA (sha256 (ByteArray.mk (cv x).toArray)) = Spec.sha256 (sp (cv x)) := sha256_eq _
  rw [sp_cv] at h
  rw [← h, spA_length, sha256_size]

private theorem spec_hmac_length (k x : Spec.Bytes) : (Spec.hmacSha256 k x).length = 32 := by
  unfold Spec.hmacSha256
  exact spec_sha256_length _

private theorem spec_mgf1_length (x : Spec.Bytes) : (Spec.mgf1 x 30).length = 30 := by
  unfold Spec.mgf1
  rw [show (30 + 31) / 32 = 1 from rfl, List.length_take]
  simp [spec_sha256_length]

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
    sp (byteArrayPrefixOrZero b n).toList = (spA b).take n := by
  obtain ⟨v, hv, hs⟩ := prefixChecked_ok b n h
  simp [byteArrayPrefixOrZero, hv, hs]

private theorem spA_bytes {n : Nat} (v : Bytes n) : spA (bytesToByteArray v) = sp v.toList := rfl

private theorem spA_zero (n : Nat) : spA (zeroByteArray n) = Spec.toByte 0 n := by
  simp [spA, sp, zeroByteArray, Spec.toByte]

private theorem spA_concat (ys : List Node) : spA (concatBytes ys) = nds ys := by
  unfold concatBytes
  suffices h : ∀ (acc : ByteArray),
      spA (ys.foldl (fun out value => out ++ bytesToByteArray value) acc) = spA acc ++ nds ys by
    simpa [spA] using h ByteArray.empty
  induction ys with
  | nil => intro acc; simp [nds]
  | cons y ys ih => intro acc; simp [ih, nds, spA_bytes, nd]

private theorem spA_prefix (pk : Node) (k : Bytes 22) :
    spA (sha2Prefix256Key pk k) = nd pk ++ Spec.toByte 0 (64 - Spec.n) ++ sp k.toList := by
  simp [sha2Prefix256Key, spA_bytes, spA_zero, nd, Spec.n]

private theorem thash_key_eq (pk : Node) (k : Bytes 22) (ys : List Node) :
    nd (sha2Thash vp.params pk k ys) =
      (Spec.sha256 (nd pk ++ Spec.toByte 0 (64 - Spec.n) ++ sp k.toList ++ nds ys)).take Spec.n := by
  have h : sha2Thash vp.params pk k ys =
      byteArrayPrefixOrZero (sha256 (sha2Prefix256Key pk k ++ concatBytes ys)) 16 := by
    unfold sha2Thash
    split <;> rfl
  rw [h, nd, prefixOrZero_eq _ _ (by simp), sha256_eq, spA_append, spA_prefix, spA_concat]
  rfl

/-- The tweakable hash (`F`, `H`, `T_l`) at an in-domain address. -/
theorem thash_eq (pk : Node) (a : SLHDSA.Adrs) (h : Dom a) (ys : List Node) :
    nd (prims.Thash pk (prims.adrsToKey a) ys) = Spec.thash (nd pk) (adr a) (nds ys) := by
  have := thash_key_eq pk (sha2AdrsKey a) ys
  rw [adrsKey_eq a h] at this
  exact this

theorem F_eq (pk : Node) (a : SLHDSA.Adrs) (h : Dom a) (y : Node) :
    nd (prims.F pk a y) = Spec.F (nd pk) (adr a) (nd y) := by
  have := thash_eq pk a h [y]
  simp only [nds, List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  exact this

theorem H_eq (pk : Node) (a : SLHDSA.Adrs) (h : Dom a) (l r : Node) :
    nd (prims.H pk a l r) = Spec.H (nd pk) (adr a) (nd l ++ nd r) := by
  have := thash_eq pk a h [l, r]
  simp only [nds, List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  exact this

theorem Tl_eq (pk : Node) (a : SLHDSA.Adrs) (h : Dom a) (ys : List Node) :
    nd (prims.Tl pk a ys) = Spec.T (nd pk) (adr a) (nds ys) :=
  thash_eq pk a h ys

/-- `PRF` at an in-domain address. -/
theorem PRF_eq (pk sk : Node) (a : SLHDSA.Adrs) (h : Dom a) :
    nd (prims.PRF pk sk a) = Spec.PRF (nd pk) (nd sk) (adr a) := by
  obtain ⟨v, hv, hs⟩ := prefixChecked_ok
    (sha256 (sha2Prefix256 pk ⟨a, h.1, h.2.1, h.2.2⟩ ++ bytesToByteArray sk)) 16 (by simp)
  have e : prims.PRF pk sk a = v := by
    show checkedNodeOrZero (sha2PRFChecked pk sk a) = v
    simp only [sha2PRFChecked, Sha2Address.ofAdrs, h.1, h.2.1, h.2.2, dite_true]
    show checkedNodeOrZero (byteArrayPrefixChecked _ 16) = v
    rw [hv]; rfl
  rw [e, nd, hs, sha256_eq, spA_append, sha2Prefix256, spA_prefix, Sha2Address.bytes_toList,
    compressSha2_eq, spA_bytes]
  rfl

/-- `PRF_msg`. -/
theorem PRFmsg_eq (skPrf optRand : Node) (msg : List UInt8) :
    nd (prims.PRFmsg skPrf optRand msg) = Spec.PRFmsg (nd skPrf) (nd optRand) (sp msg) := by
  have e : prims.PRFmsg skPrf optRand msg =
      byteArrayPrefixOrZero (hmacSha256 (bytesToByteArray skPrf)
        (bytesToByteArray optRand ++ ByteArray.mk msg.toArray)) 16 := rfl
  have hsz : 16 ≤ (hmacSha256 (bytesToByteArray skPrf)
        (bytesToByteArray optRand ++ ByteArray.mk msg.toArray)).size := by
    rw [← spA_length, hmacSha256_eq, spec_hmac_length]; omega
  rw [e, nd, prefixOrZero_eq _ _ hsz, hmacSha256_eq, spA_append, spA_bytes, spA_bytes, spA_mk]
  rfl

/-- `H_msg` (30-byte digest). -/
theorem Hmsg_eq (r pk root : Node) (msg : List UInt8) :
    sp (prims.Hmsg r pk root msg).toList = Spec.Hmsg (nd r) (nd pk) (nd root) (sp msg) := by
  have e : sp (prims.Hmsg r pk root msg).toList =
      sp (Vector.toList (n := 30) <| byteArrayPrefixOrZero (mgf1 (bytesToByteArray r ++ bytesToByteArray pk ++
        sha256 (bytesToByteArray r ++ bytesToByteArray pk ++ bytesToByteArray root ++
          ByteArray.mk msg.toArray)) 30) 30) := rfl
  have hsz : 30 ≤ (mgf1 (bytesToByteArray r ++ bytesToByteArray pk ++
        sha256 (bytesToByteArray r ++ bytesToByteArray pk ++ bytesToByteArray root ++
          ByteArray.mk msg.toArray)) 30).size := by
    rw [← spA_length, mgf1_eq, spec_mgf1_length]
  rw [e, prefixOrZero_eq _ _ hsz, mgf1_eq]
  simp only [spA_append, spA_bytes, spA_mk, sha256_eq]
  rw [List.take_of_length_le (le_of_eq (spec_mgf1_length _))]
  rfl

end Link

#print axioms Link.thash_eq
#print axioms Link.F_eq
#print axioms Link.H_eq
#print axioms Link.Tl_eq
#print axioms Link.PRF_eq
#print axioms Link.PRFmsg_eq
#print axioms Link.Hmsg_eq
