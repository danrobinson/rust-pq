/-!
# SHA-256 and HMAC-SHA-256

A direct transcription of FIPS 180-4 (SHA-256) and FIPS 198-1 (HMAC), over
lists of bytes. Depends on nothing but core Lean.
-/

namespace Spec

abbrev Byte := BitVec 8
abbrev Bytes := List Byte

/-- FIPS 205 Algorithm 3, `toByte(x, n)`: the `n`-byte big-endian encoding of `x`. -/
def toByte (x n : Nat) : Bytes :=
  (List.range n).map fun i => BitVec.ofNat 8 (x >>> (8 * (n - 1 - i)))

namespace SHA256

abbrev Word := BitVec 32

/-- FIPS 180-4 §4.2.2. -/
def K : List Word := [
  0x428a2f98#32, 0x71374491#32, 0xb5c0fbcf#32, 0xe9b5dba5#32, 0x3956c25b#32, 0x59f111f1#32, 0x923f82a4#32, 0xab1c5ed5#32,
  0xd807aa98#32, 0x12835b01#32, 0x243185be#32, 0x550c7dc3#32, 0x72be5d74#32, 0x80deb1fe#32, 0x9bdc06a7#32, 0xc19bf174#32,
  0xe49b69c1#32, 0xefbe4786#32, 0x0fc19dc6#32, 0x240ca1cc#32, 0x2de92c6f#32, 0x4a7484aa#32, 0x5cb0a9dc#32, 0x76f988da#32,
  0x983e5152#32, 0xa831c66d#32, 0xb00327c8#32, 0xbf597fc7#32, 0xc6e00bf3#32, 0xd5a79147#32, 0x06ca6351#32, 0x14292967#32,
  0x27b70a85#32, 0x2e1b2138#32, 0x4d2c6dfc#32, 0x53380d13#32, 0x650a7354#32, 0x766a0abb#32, 0x81c2c92e#32, 0x92722c85#32,
  0xa2bfe8a1#32, 0xa81a664b#32, 0xc24b8b70#32, 0xc76c51a3#32, 0xd192e819#32, 0xd6990624#32, 0xf40e3585#32, 0x106aa070#32,
  0x19a4c116#32, 0x1e376c08#32, 0x2748774c#32, 0x34b0bcb5#32, 0x391c0cb3#32, 0x4ed8aa4a#32, 0x5b9cca4f#32, 0x682e6ff3#32,
  0x748f82ee#32, 0x78a5636f#32, 0x84c87814#32, 0x8cc70208#32, 0x90befffa#32, 0xa4506ceb#32, 0xbef9a3f7#32, 0xc67178f2#32]

/-- FIPS 180-4 §5.3.3. -/
def H0 : List Word := [
  0x6a09e667#32, 0xbb67ae85#32, 0x3c6ef372#32, 0xa54ff53a#32, 0x510e527f#32, 0x9b05688c#32, 0x1f83d9ab#32, 0x5be0cd19#32]

/-! FIPS 180-4 §4.1.2. -/
def ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)
def maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bsig0 (x : Word) : Word := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
def bsig1 (x : Word) : Word := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
def ssig0 (x : Word) : Word := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)
def ssig1 (x : Word) : Word := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

/-- The big-endian 32-bit word at byte offset `i`. -/
def word (b : Bytes) (i : Nat) : Word :=
  b[i]! ++ b[i + 1]! ++ b[i + 2]! ++ b[i + 3]!

/-- The sixteen message words of a 64-byte block. -/
def blockWords (block : Bytes) : List Word :=
  (List.range 16).map fun i => word block (4 * i)

/-- Extend the message schedule by one word: `W_t` for `t = |w| ≥ 16`. -/
def scheduleStep (w : List Word) : List Word :=
  let t := w.length
  w ++ [ssig1 w[t - 2]! + w[t - 7]! + ssig0 w[t - 15]! + w[t - 16]!]

/-- The message schedule `W_0 … W_63` (§6.2.2 step 1). -/
def schedule (block : Bytes) : List Word :=
  Nat.repeat scheduleStep 48 (blockWords block)

abbrev State := Word × Word × Word × Word × Word × Word × Word × Word

/-- One round of the compression function (§6.2.2 step 3). -/
def round (w : List Word) (s : State) (t : Nat) : State :=
  let (a, b, c, d, e, f, g, h) := s
  let t1 := h + bsig1 e + ch e f g + K[t]! + w[t]!
  let t2 := bsig0 a + maj a b c
  (t1 + t2, a, b, c, d + t1, e, f, g)

/-- The compression function on one 64-byte block (§6.2.2). -/
def compress (st : List Word) (block : Bytes) : List Word :=
  let w := schedule block
  let (a, b, c, d, e, f, g, h) :=
    (List.range 64).foldl (round w) (st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!)
  [st[0]! + a, st[1]! + b, st[2]! + c, st[3]! + d, st[4]! + e, st[5]! + f, st[6]! + g, st[7]! + h]

/-- Padding (§5.1.1): a `1` bit, the least number of `0` bits reaching
56 mod 64 bytes, then the bit length as a 64-bit big-endian integer. -/
def pad (m : Bytes) : Bytes :=
  m ++ [0x80#8] ++ List.replicate ((119 - m.length % 64) % 64) 0#8 ++ toByte (8 * m.length) 8

/-- The `k`-th 64-byte block of a padded message. -/
def blockAt (p : Bytes) (k : Nat) : Bytes := (p.drop (64 * k)).take 64

/-- SHA-256 of a byte string shorter than 2^61 bytes. -/
def sha256 (m : Bytes) : Bytes :=
  let p := pad m
  let st := (List.range (p.length / 64)).foldl (fun st k => compress st (blockAt p k)) H0
  st.flatMap fun w => toByte w.toNat 4

end SHA256

export SHA256 (sha256)

/-- HMAC-SHA-256 (FIPS 198-1), block size 64. -/
def hmacSha256 (key msg : Bytes) : Bytes :=
  let k := if key.length > 64 then sha256 key else key
  let k0 := k ++ List.replicate (64 - k.length) 0#8
  sha256 (k0.map (· ^^^ 0x5c#8) ++ sha256 (k0.map (· ^^^ 0x36#8) ++ msg))

end Spec
