import Link.Basic

/-!
# SHA-256 and the SLH-DSA-SHA2 hash functions over an abstract compression function

Verbatim copies of VCVio's `VCVio.Algorithms.Sha2` (SHA-256, MGF1, HMAC) and of the SHA-2 primitive
bundle of `HashSig.SLHDSA.Concrete.FIPS`, with the SHA-256 compression function abstracted as a
parameter `c` of the type of `VCVio.Algorithms.Sha2.compress`.  Instantiating `c := compress`
gives back VCVio's definitions *definitionally* (`sha2PrimitivesG_compress`).

The SHA-512 branches (used only for `n ≠ 16`) are left exactly as in VCVio.
-/

namespace Ideal

open SLHDSA SLHDSA.Concrete
open VCVio.Algorithms.Sha2

/-- The type of a SHA-256 compression function acting on a block inside a byte array. -/
abbrev CompressFn := Array UInt32 → ByteArray → Nat → Array UInt32

/-! ## SHA-256, MGF1, HMAC -/

/-- `VCVio.Algorithms.Sha2.sha256Family` over the compression function `c`. -/
def sha256FamilyG (c : CompressFn) (initial : Array UInt32) (outLen : ℕ)
    (msg : ByteArray) : ByteArray := Id.run do
  let padded := pad msg
  let mut st := initial
  for b in [0:padded.size / 64] do
    st := c st padded (b * 64)
  return (stateBytes32 st).extract 0 outLen

/-- SHA-256 over the compression function `c`. -/
def sha256G (c : CompressFn) (msg : ByteArray) : ByteArray := sha256FamilyG c iv 32 msg

@[simp] theorem sha256G_size (c : CompressFn) (msg : ByteArray) : (sha256G c msg).size = 32 := by
  simp [sha256G, sha256FamilyG]

/-- MGF1-SHA-256 over the compression function `c`. -/
def mgf1G (c : CompressFn) (seed : ByteArray) (outLen : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let blocks := (outLen + 31) / 32
  for ctr in [0:blocks] do
    out := out ++ sha256G c (seed ++ u32be ctr.toUInt32)
  return out.extract 0 outLen

/-- HMAC key block over the compression function `c`. -/
def hmacKey0G (c : CompressFn) (key : ByteArray) : ByteArray := Id.run do
  let k := if key.size > 64 then sha256G c key else key
  let mut out := k
  for _ in [0:64 - k.size] do
    out := out.push 0
  return out

/-- HMAC-SHA-256 over the compression function `c`. -/
def hmacSha256G (c : CompressFn) (key msg : ByteArray) : ByteArray :=
  let k0 := hmacKey0G c key
  sha256G c (xorConst k0 0x5c ++ sha256G c (xorConst k0 0x36 ++ msg))

theorem sha256FamilyG_compress : sha256FamilyG compress = sha256Family := rfl
theorem sha256G_compress : sha256G compress = sha256 := rfl
theorem mgf1G_compress : mgf1G compress = mgf1 := rfl
theorem hmacKey0G_compress : hmacKey0G compress = hmacKey0 := rfl
theorem hmacSha256G_compress : hmacSha256G compress = hmacSha256 := rfl

/-! ## The SLH-DSA SHA-2 functions -/

/-- `sha2PRFChecked` over the compression function `c`. -/
def sha2PRFCheckedG (c : CompressFn) {n : ℕ} (pkSeed skSeed : Bytes n) (address : Adrs) :
    Except CodecError (Bytes n) := do
  let checked ← Sha2Address.ofAdrs address
  byteArrayPrefixChecked
    (sha256G c (sha2Prefix256 pkSeed checked ++ bytesToByteArray skSeed)) n

/-- `sha2PRFmsg` over the compression function `c`. -/
def sha2PRFmsgG (c : CompressFn) {n : ℕ} (skPrf optRand : Bytes n) (message : List Byte) :
    Bytes n :=
  let input := bytesToByteArray optRand ++ ByteArray.mk message.toArray
  if n = 16 then
    byteArrayPrefixOrZero (hmacSha256G c (bytesToByteArray skPrf) input) n
  else
    byteArrayPrefixOrZero (hmacSha512 (bytesToByteArray skPrf) input) n

/-- `sha2Hmsg` over the compression function `c`. -/
def sha2HmsgG (c : CompressFn) (p : Params) (randomizer pkSeed pkRoot : Bytes p.n)
    (message : List Byte) : Bytes p.m :=
  let input := bytesToByteArray randomizer ++ bytesToByteArray pkSeed ++
    bytesToByteArray pkRoot ++ ByteArray.mk message.toArray
  if p.n = 16 then
    let inner := sha256G c input
    byteArrayPrefixOrZero (mgf1G c (bytesToByteArray randomizer ++
      bytesToByteArray pkSeed ++ inner) p.m) p.m
  else
    let inner := sha512 input
    byteArrayPrefixOrZero (mgf1Sha512 (bytesToByteArray randomizer ++
      bytesToByteArray pkSeed ++ inner) p.m) p.m

/-- `sha2Thash` over the compression function `c`. -/
def sha2ThashG (c : CompressFn) (p : Params) (pkSeed : Bytes p.n) (address : Bytes 22)
    (messages : List (Bytes p.n)) : Bytes p.n :=
  let payload := concatBytes messages
  if messages.length = 1 then
    byteArrayPrefixOrZero (sha256G c (sha2Prefix256Key pkSeed address ++ payload)) p.n
  else if p.n = 16 then
    byteArrayPrefixOrZero (sha256G c (sha2Prefix256Key pkSeed address ++ payload)) p.n
  else
    byteArrayPrefixOrZero (sha512 (sha2Prefix512Key pkSeed address ++ payload)) p.n

/-- `sha2Primitives` over the compression function `c`: same carriers, address key and byte
encoding; only SHA-256's compression function is replaced. -/
def sha2PrimitivesG (c : CompressFn) (p : Params) : Primitives p where
  PkSeed := Bytes p.n
  SkSeed := Bytes p.n
  SkPrf := Bytes p.n
  Y := Bytes p.n
  AdrsKey := Bytes 22
  adrsToKey := sha2AdrsKey
  Thash := sha2ThashG c p
  PRF := fun pkSeed skSeed address => checkedNodeOrZero (sha2PRFCheckedG c pkSeed skSeed address)
  PRFmsg := sha2PRFmsgG c
  Hmsg := sha2HmsgG c p
  yToBytes := id

theorem sha2PRFCheckedG_compress {n : ℕ} :
    @sha2PRFCheckedG compress n = @sha2PRFChecked n := rfl
theorem sha2PRFmsgG_compress {n : ℕ} : @sha2PRFmsgG compress n = @sha2PRFmsg n := rfl
theorem sha2HmsgG_compress (p : Params) : sha2HmsgG compress p = sha2Hmsg p := rfl
theorem sha2ThashG_compress (p : Params) : sha2ThashG compress p = sha2Thash p := rfl

/-- **Instantiation lemma**: at the real SHA-256 compression function the generic bundle is
VCVio's FIPS SHA-2 bundle. -/
theorem sha2PrimitivesG_compress (p : Params) :
    sha2PrimitivesG compress p = sha2Primitives p := rfl

/-! ### Carrier instances (as for `sha2Primitives p`) -/

instance (c : CompressFn) (p : Params) : SampleableType (sha2PrimitivesG c p).PkSeed :=
  inferInstanceAs (SampleableType (Bytes p.n))
instance (c : CompressFn) (p : Params) : SampleableType (sha2PrimitivesG c p).SkSeed :=
  inferInstanceAs (SampleableType (Bytes p.n))
instance (c : CompressFn) (p : Params) : SampleableType (sha2PrimitivesG c p).SkPrf :=
  inferInstanceAs (SampleableType (Bytes p.n))
instance (c : CompressFn) (p : Params) : SampleableType (sha2PrimitivesG c p).Y :=
  inferInstanceAs (SampleableType (Bytes p.n))
instance (c : CompressFn) (p : Params) : DecidableEq (sha2PrimitivesG c p).PkSeed :=
  inferInstanceAs (DecidableEq (Bytes p.n))
instance (c : CompressFn) (p : Params) : DecidableEq (sha2PrimitivesG c p).SkPrf :=
  inferInstanceAs (DecidableEq (Bytes p.n))
instance (c : CompressFn) (p : Params) : DecidableEq (sha2PrimitivesG c p).Y :=
  inferInstanceAs (DecidableEq (Bytes p.n))
instance (c : CompressFn) (p : Params) : DecidableEq (sha2PrimitivesG c p).AdrsKey :=
  inferInstanceAs (DecidableEq (Bytes 22))

/-- The carrier instances agree with those of `sha2Primitives p` across
`sha2PrimitivesG_compress` (all are the `Bytes` instances). -/
example (p : Params) :
    (inferInstance : SampleableType (sha2PrimitivesG compress p).PkSeed) =
      (inferInstance : SampleableType (sha2Primitives p).PkSeed) := rfl

/-! ## The bundle at SLH-DSA-SHA2-128s -/

/-- The generic bundle at SLH-DSA-SHA2-128s. -/
abbrev primsG (c : CompressFn) : Primitives Link.vp.params := sha2PrimitivesG c Link.vp.params

theorem primsG_compress : primsG compress = Link.prims := rfl

/-- At 128s the tweakable hash is SHA-256 at every arity. -/
theorem sha2ThashG_128 (c : CompressFn) (pk : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) :
    sha2ThashG c Link.vp.params pk a xs =
      byteArrayPrefixOrZero (sha256G c (sha2Prefix256Key pk a ++ concatBytes xs)) 16 := by
  unfold sha2ThashG
  split <;> rfl

/-- `PRF` is the arity-one tweakable hash on the checked `ADRSc` domain. -/
theorem PRF_eq_Thash (c : CompressFn) (p : Params) (pk sk : Bytes p.n) (a : Adrs)
    {chk : Sha2Address} (h : Sha2Address.ofAdrs a = .ok chk) :
    (sha2PrimitivesG c p).PRF pk sk a =
      (sha2PrimitivesG c p).Thash pk (sha2AdrsKey a) [sk] := by
  have hc : a.isCanonical = true := by
    unfold Sha2Address.ofAdrs at h; split at h
    · assumption
    · cases h
  have hl : Adrs.Fits 1 a.layer = true := by
    unfold Sha2Address.ofAdrs at h; simp only [hc, ↓reduceDIte] at h; split at h
    · assumption
    · cases h
  have ht : Adrs.Fits 8 a.tree = true := by
    unfold Sha2Address.ofAdrs at h; simp only [hc, hl, ↓reduceDIte] at h; split at h
    · assumption
    · cases h
  have hk : sha2AdrsKey a = (⟨a, hc, hl, ht⟩ : Sha2Address).bytes :=
    sha2AdrsKey_eq_compressed a hc hl ht
  show checkedNodeOrZero (sha2PRFCheckedG c pk sk a) = sha2ThashG c p pk (sha2AdrsKey a) [sk]
  have h1 : sha2ThashG c p pk (sha2AdrsKey a) [sk] = byteArrayPrefixOrZero
      (sha256G c (sha2Prefix256Key pk (sha2AdrsKey a) ++ concatBytes [sk])) p.n := by
    simp [sha2ThashG]
  have h2 : concatBytes [sk] = bytesToByteArray sk := by
    simp [concatBytes]
  rw [h1, h2, hk]
  simp only [sha2PRFCheckedG, Sha2Address.ofAdrs, hc, hl, ht, dite_true]
  rfl

end Ideal

#print axioms Ideal.sha2PrimitivesG_compress
#print axioms Ideal.primsG_compress
#print axioms Ideal.PRF_eq_Thash
