import Ideal.Sha.Generic

namespace Ideal

open SLHDSA SLHDSA.Concrete VCVio.Algorithms.Sha2

/-- SHA-512 compression at a byte offset, parallel to `CompressFn`. -/
abbrev Compress512Fn := Array UInt64 → ByteArray → Nat → Array UInt64

def sha512FamilyG (c : Compress512Fn) (initial : Array UInt64) (outLen : ℕ)
    (msg : ByteArray) : ByteArray := Id.run do
  let padded := pad512 msg
  let mut st := initial
  for b in [0:padded.size / 128] do
    st := c st padded (b * 128)
  return (stateBytes64 st).extract 0 outLen

def sha512G (c : Compress512Fn) : ByteArray → ByteArray := sha512FamilyG c iv512 64

def mgf1Sha512G (c : Compress512Fn) (seed : ByteArray) (outLen : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let blocks := (outLen + 63) / 64
  for ctr in [0:blocks] do
    out := out ++ sha512G c (seed ++ u32be ctr.toUInt32)
  return out.extract 0 outLen

def hmacKey0Sha512G (c : Compress512Fn) (key : ByteArray) : ByteArray := Id.run do
  let k := if key.size > 128 then sha512G c key else key
  let mut out := k
  for _ in [0:128 - k.size] do
    out := out.push 0
  return out

def hmacSha512G (c : Compress512Fn) (key msg : ByteArray) : ByteArray :=
  let k0 := hmacKey0Sha512G c key
  sha512G c (xorConst k0 0x5c ++ sha512G c (xorConst k0 0x36 ++ msg))



def sha2PRFmsgMixed (c : CompressFn) (c512 : Compress512Fn) {n : ℕ} (skPrf optRand : Bytes n) (message : List Byte) :
    Bytes n :=
  let input := bytesToByteArray optRand ++ ByteArray.mk message.toArray
  if n = 16 then
    byteArrayPrefixOrZero (hmacSha256G c (bytesToByteArray skPrf) input) n
  else
    byteArrayPrefixOrZero (hmacSha512G c512 (bytesToByteArray skPrf) input) n

def sha2HmsgMixed (c : CompressFn) (c512 : Compress512Fn) (p : Params) (randomizer pkSeed pkRoot : Bytes p.n)
    (message : List Byte) : Bytes p.m :=
  let input := bytesToByteArray randomizer ++ bytesToByteArray pkSeed ++
    bytesToByteArray pkRoot ++ ByteArray.mk message.toArray
  if p.n = 16 then
    let inner := sha256G c input
    byteArrayPrefixOrZero (mgf1G c (bytesToByteArray randomizer ++
      bytesToByteArray pkSeed ++ inner) p.m) p.m
  else
    let inner := sha512G c512 input
    byteArrayPrefixOrZero (mgf1Sha512G c512 (bytesToByteArray randomizer ++
      bytesToByteArray pkSeed ++ inner) p.m) p.m

def sha2ThashMixed (c : CompressFn) (c512 : Compress512Fn) (p : Params) (pkSeed : Bytes p.n) (address : Bytes 22)
    (messages : List (Bytes p.n)) : Bytes p.n :=
  let payload := concatBytes messages
  if messages.length = 1 then
    byteArrayPrefixOrZero (sha256G c (sha2Prefix256Key pkSeed address ++ payload)) p.n
  else if p.n = 16 then
    byteArrayPrefixOrZero (sha256G c (sha2Prefix256Key pkSeed address ++ payload)) p.n
  else
    byteArrayPrefixOrZero (sha512G c512 (sha2Prefix512Key pkSeed address ++ payload)) p.n

def sha2PrimitivesMixed (c : CompressFn) (c512 : Compress512Fn) (p : Params) : Primitives p where
  PkSeed := Bytes p.n
  SkSeed := Bytes p.n
  SkPrf := Bytes p.n
  Y := Bytes p.n
  AdrsKey := Bytes 22
  adrsToKey := sha2AdrsKey
  Thash := sha2ThashMixed c c512 p
  PRF := fun pkSeed skSeed address => checkedNodeOrZero (sha2PRFCheckedG c pkSeed skSeed address)
  PRFmsg := sha2PRFmsgMixed c c512
  Hmsg := sha2HmsgMixed c c512 p
  yToBytes := id

/-- Specializing SHA-512 alone recovers the existing SHA-256 compression model. -/
theorem sha2PrimitivesMixed_compress512 (c : CompressFn) (p : Params) :
    sha2PrimitivesMixed c compress512 p = sha2PrimitivesG c p := rfl

/-- With both real compressors the mixed model computes the FIPS primitives at every set. -/
theorem sha2PrimitivesMixed_real (p : Params) :
    sha2PrimitivesMixed compress compress512 p = sha2Primitives p := rfl

end Ideal

#print axioms Ideal.sha2PrimitivesMixed_compress512
#print axioms Ideal.sha2PrimitivesMixed_real
