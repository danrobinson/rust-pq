import Spec.Sha256

/-!
# SHA-512 and HMAC-SHA-512

A direct transcription of FIPS 180-4 (SHA-512) and FIPS 198-1 (HMAC), over
lists of bytes. Depends on nothing but core Lean.
-/

namespace Spec

namespace SHA512

abbrev Word := BitVec 64

/-- FIPS 180-4 §4.2.3. -/
def K : List Word := [
  0x428a2f98d728ae22#64, 0x7137449123ef65cd#64, 0xb5c0fbcfec4d3b2f#64, 0xe9b5dba58189dbbc#64,
  0x3956c25bf348b538#64, 0x59f111f1b605d019#64, 0x923f82a4af194f9b#64, 0xab1c5ed5da6d8118#64,
  0xd807aa98a3030242#64, 0x12835b0145706fbe#64, 0x243185be4ee4b28c#64, 0x550c7dc3d5ffb4e2#64,
  0x72be5d74f27b896f#64, 0x80deb1fe3b1696b1#64, 0x9bdc06a725c71235#64, 0xc19bf174cf692694#64,
  0xe49b69c19ef14ad2#64, 0xefbe4786384f25e3#64, 0x0fc19dc68b8cd5b5#64, 0x240ca1cc77ac9c65#64,
  0x2de92c6f592b0275#64, 0x4a7484aa6ea6e483#64, 0x5cb0a9dcbd41fbd4#64, 0x76f988da831153b5#64,
  0x983e5152ee66dfab#64, 0xa831c66d2db43210#64, 0xb00327c898fb213f#64, 0xbf597fc7beef0ee4#64,
  0xc6e00bf33da88fc2#64, 0xd5a79147930aa725#64, 0x06ca6351e003826f#64, 0x142929670a0e6e70#64,
  0x27b70a8546d22ffc#64, 0x2e1b21385c26c926#64, 0x4d2c6dfc5ac42aed#64, 0x53380d139d95b3df#64,
  0x650a73548baf63de#64, 0x766a0abb3c77b2a8#64, 0x81c2c92e47edaee6#64, 0x92722c851482353b#64,
  0xa2bfe8a14cf10364#64, 0xa81a664bbc423001#64, 0xc24b8b70d0f89791#64, 0xc76c51a30654be30#64,
  0xd192e819d6ef5218#64, 0xd69906245565a910#64, 0xf40e35855771202a#64, 0x106aa07032bbd1b8#64,
  0x19a4c116b8d2d0c8#64, 0x1e376c085141ab53#64, 0x2748774cdf8eeb99#64, 0x34b0bcb5e19b48a8#64,
  0x391c0cb3c5c95a63#64, 0x4ed8aa4ae3418acb#64, 0x5b9cca4f7763e373#64, 0x682e6ff3d6b2b8a3#64,
  0x748f82ee5defb2fc#64, 0x78a5636f43172f60#64, 0x84c87814a1f0ab72#64, 0x8cc702081a6439ec#64,
  0x90befffa23631e28#64, 0xa4506cebde82bde9#64, 0xbef9a3f7b2c67915#64, 0xc67178f2e372532b#64,
  0xca273eceea26619c#64, 0xd186b8c721c0c207#64, 0xeada7dd6cde0eb1e#64, 0xf57d4f7fee6ed178#64,
  0x06f067aa72176fba#64, 0x0a637dc5a2c898a6#64, 0x113f9804bef90dae#64, 0x1b710b35131c471b#64,
  0x28db77f523047d84#64, 0x32caab7b40c72493#64, 0x3c9ebe0a15c9bebc#64, 0x431d67c49c100d4c#64,
  0x4cc5d4becb3e42b6#64, 0x597f299cfc657e2a#64, 0x5fcb6fab3ad6faec#64, 0x6c44198c4a475817#64]

/-- FIPS 180-4 §5.3.5. -/
def H0 : List Word := [
  0x6a09e667f3bcc908#64, 0xbb67ae8584caa73b#64, 0x3c6ef372fe94f82b#64, 0xa54ff53a5f1d36f1#64,
  0x510e527fade682d1#64, 0x9b05688c2b3e6c1f#64, 0x1f83d9abfb41bd6b#64, 0x5be0cd19137e2179#64]

/-! FIPS 180-4 §4.1.3. -/
def ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)
def maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bsig0 (x : Word) : Word := x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39
def bsig1 (x : Word) : Word := x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41
def ssig0 (x : Word) : Word := x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ (x >>> 7)
def ssig1 (x : Word) : Word := x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ (x >>> 6)

/-- The big-endian 64-bit word at byte offset `i`. -/
def word (b : Bytes) (i : Nat) : Word :=
  b[i]! ++ b[i + 1]! ++ b[i + 2]! ++ b[i + 3]! ++ b[i + 4]! ++ b[i + 5]! ++ b[i + 6]! ++ b[i + 7]!

/-- The sixteen message words of a 128-byte block. -/
def blockWords (block : Bytes) : List Word :=
  (List.range 16).map fun i => word block (8 * i)

/-- Extend the message schedule by one word: `W_t` for `t = |w| ≥ 16`. -/
def scheduleStep (w : List Word) : List Word :=
  let t := w.length
  w ++ [ssig1 w[t - 2]! + w[t - 7]! + ssig0 w[t - 15]! + w[t - 16]!]

/-- The message schedule `W_0 … W_79` (§6.4.2 step 1). -/
def schedule (block : Bytes) : List Word :=
  Nat.repeat scheduleStep 64 (blockWords block)

abbrev State := Word × Word × Word × Word × Word × Word × Word × Word

/-- One round of the compression function (§6.4.2 step 3). -/
def round (w : List Word) (s : State) (t : Nat) : State :=
  let (a, b, c, d, e, f, g, h) := s
  let t1 := h + bsig1 e + ch e f g + K[t]! + w[t]!
  let t2 := bsig0 a + maj a b c
  (t1 + t2, a, b, c, d + t1, e, f, g)

/-- The compression function on one 128-byte block (§6.4.2). -/
def compress (st : List Word) (block : Bytes) : List Word :=
  let w := schedule block
  let (a, b, c, d, e, f, g, h) :=
    (List.range 80).foldl (round w) (st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!)
  [st[0]! + a, st[1]! + b, st[2]! + c, st[3]! + d, st[4]! + e, st[5]! + f, st[6]! + g, st[7]! + h]

/-- Padding (§5.1.2): a `1` bit, the least number of `0` bits reaching
112 mod 128 bytes, then the bit length as a 128-bit big-endian integer. -/
def pad (m : Bytes) : Bytes :=
  m ++ [0x80#8] ++ List.replicate ((239 - m.length % 128) % 128) 0#8 ++ toByte (8 * m.length) 16

/-- The `k`-th 128-byte block of a padded message. -/
def blockAt (p : Bytes) (k : Nat) : Bytes := (p.drop (128 * k)).take 128

/-- SHA-512 of a byte string shorter than 2^125 bytes. -/
def sha512 (m : Bytes) : Bytes :=
  let p := pad m
  let st := (List.range (p.length / 128)).foldl (fun st k => compress st (blockAt p k)) H0
  st.flatMap fun w => toByte w.toNat 8

end SHA512

export SHA512 (sha512)

/-- HMAC-SHA-512 (FIPS 198-1), block size 128. -/
def hmacSha512 (key msg : Bytes) : Bytes :=
  let k := if key.length > 128 then sha512 key else key
  let k0 := k ++ List.replicate (128 - k.length) 0#8
  sha512 (k0.map (· ^^^ 0x5c#8) ++ sha512 (k0.map (· ^^^ 0x36#8) ++ msg))

end Spec
