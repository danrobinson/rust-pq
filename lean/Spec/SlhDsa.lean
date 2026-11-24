import Spec.Sha256
import Spec.Sha512
import Spec.Shake256

/-!
# SLH-DSA with SHA-2

A transcription of FIPS 205 for the six parameter sets
SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}, over lists of bytes and
natural numbers. Every function takes the parameter set as its first
argument. Loops of the standard are written as folds over `List.range`.
Signatures are flat byte strings laid out exactly as in the standard.
-/

namespace Spec

/-! ## Parameters (FIPS 205 §11, Table 2) -/

inductive HashFamily where
  | sha2
  | shake
deriving Repr, DecidableEq

/-- A row of Table 2. -/
structure Params where
  /-- Security parameter: hash output length in bytes. -/
  n : Nat
  /-- Total hypertree height. -/
  h : Nat
  /-- Number of hypertree layers. -/
  d : Nat
  /-- Height of each XMSS tree, `h' = h / d`. -/
  hp : Nat
  /-- FORS tree height. -/
  a : Nat
  /-- Number of FORS trees. -/
  k : Nat
  /-- Bits per WOTS+ digit. -/
  lgw : Nat
  /-- Message digest length in bytes. -/
  m : Nat
  family : HashFamily := .sha2
deriving Repr, DecidableEq

def sha2_128s : Params := { n := 16, h := 63, d := 7, hp := 9, a := 12, k := 14, lgw := 4, m := 30 }
def sha2_128f : Params := { n := 16, h := 66, d := 22, hp := 3, a := 6, k := 33, lgw := 4, m := 34 }
def sha2_192s : Params := { n := 24, h := 63, d := 7, hp := 9, a := 14, k := 17, lgw := 4, m := 39 }
def sha2_192f : Params := { n := 24, h := 66, d := 22, hp := 3, a := 8, k := 33, lgw := 4, m := 42 }
def sha2_256s : Params := { n := 32, h := 64, d := 8, hp := 8, a := 14, k := 22, lgw := 4, m := 47 }
def sha2_256f : Params := { n := 32, h := 68, d := 17, hp := 4, a := 9, k := 35, lgw := 4, m := 49 }

def shake_128s : Params := { sha2_128s with family := .shake }
def shake_128f : Params := { sha2_128f with family := .shake }
def shake_192s : Params := { sha2_192s with family := .shake }
def shake_192f : Params := { sha2_192f with family := .shake }
def shake_256s : Params := { sha2_256s with family := .shake }
def shake_256f : Params := { sha2_256f with family := .shake }

namespace Params

/-- The Winternitz parameter `w = 2^lg_w` (§5, equation 5.1). -/
def w (p : Params) : Nat := 2 ^ p.lgw

/-- `len_1 = ⌈8n / lg_w⌉` (equation 5.2). -/
def len1 (p : Params) : Nat := (8 * p.n + p.lgw - 1) / p.lgw

/-- `len_2 = ⌊log_2(len_1 · (w − 1)) / lg_w⌋ + 1` (equation 5.3). -/
def len2 (p : Params) : Nat := Nat.log2 (p.len1 * (p.w - 1)) / p.lgw + 1

/-- `len = len_1 + len_2` (equation 5.4). -/
def len (p : Params) : Nat := p.len1 + p.len2

/-- Bytes of the digest used for FORS: `⌈k·a / 8⌉` (Algorithm 19, line 6). -/
def mdBytes (p : Params) : Nat := (p.k * p.a + 7) / 8

/-- Bytes of the digest holding the tree index: `⌈(h − h/d) / 8⌉` (line 7). -/
def treeBytes (p : Params) : Nat := (p.h - p.h / p.d + 7) / 8

/-- Bytes of the digest holding the leaf index: `⌈h / (8d)⌉` (line 8). -/
def leafBytes (p : Params) : Nat := (p.h / p.d + 7) / 8

/-- Bytes of one XMSS signature: `(len + h')·n`. -/
def xmssSigBytes (p : Params) : Nat := (p.len + p.hp) * p.n

/-- Bytes of a FORS signature: `k·(1 + a)·n`. -/
def forsSigBytes (p : Params) : Nat := p.k * (1 + p.a) * p.n

/-- Bytes of a signature: `(1 + k(1 + a) + h + d·len)·n` (Figure 17). -/
def sigBytes (p : Params) : Nat := (1 + p.k * (1 + p.a) + p.h + p.d * p.len) * p.n

/-- The conditions on a parameter set under which the Rust implementation is
proven to compute this specification. They hold for every row of Table 2
(`sha2_128s_valid` … `sha2_256f_valid` below). The bounds are those of the
machine representation: the tree index is held in 64 bits, the leaf index
and FORS indices in 32 bits. -/
structure Valid (p : Params) : Prop where
  /-- Table 2 has `n = 16`, `24` or `32`. -/
  n_cases : p.n = 16 ∨ p.n = 24 ∨ p.n = 32
  /-- Table 2 has `lg_w = 4` throughout. -/
  lgw_eq : p.lgw = 4
  d_ge : 2 ≤ p.d
  d_le : p.d ≤ 22
  hp_pos : 1 ≤ p.hp
  hp_le : p.hp ≤ 9
  /-- `h = d · h'`. -/
  h_eq : p.h = p.d * p.hp
  /-- The tree index `h − h'` bits long fits in 64 bits. -/
  tree_le : p.h - p.hp ≤ 64
  a_pos : 1 ≤ p.a
  a_le : p.a ≤ 14
  k_pos : 1 ≤ p.k
  k_le : p.k ≤ 35
  /-- The digest is exactly the three pieces Algorithm 19 cuts it into. -/
  m_eq : p.m = p.mdBytes + p.treeBytes + p.leafBytes

end Params

theorem sha2_128s_valid : sha2_128s.Valid := by constructor <;> decide
theorem sha2_128f_valid : sha2_128f.Valid := by constructor <;> decide
theorem sha2_192s_valid : sha2_192s.Valid := by constructor <;> decide
theorem sha2_192f_valid : sha2_192f.Valid := by constructor <;> decide
theorem sha2_256s_valid : sha2_256s.Valid := by constructor <;> decide
theorem sha2_256f_valid : sha2_256f.Valid := by constructor <;> decide

/-! ## Byte-string helpers (§4.1, §4.4) -/

/-- Algorithm 2, `toInt`. -/
def toInt (x : Bytes) : Nat := x.foldl (fun t b => 256 * t + b.toNat) 0

/-- The inner `while bits < b` loop of Algorithm 4. -/
def base2bFill (x : Bytes) (b inp bits total : Nat) : Nat × Nat × Nat :=
  if bits < b then base2bFill x b (inp + 1) (bits + 8) ((total <<< 8) + x[inp]!.toNat)
  else (inp, bits, total)
termination_by b - bits

/-- The outer loop of Algorithm 4, with `out` digits still to produce. -/
def base2bGo (x : Bytes) (b : Nat) : Nat → Nat → Nat → Nat → List Nat
  | 0, _, _, _ => []
  | out + 1, inp, bits, total =>
    let (inp, bits, total) := base2bFill x b inp bits total
    let bits := bits - b
    (total >>> bits) % 2 ^ b :: base2bGo x b out inp bits total

/-- Algorithm 4, `base_2^b`. -/
def base2b (x : Bytes) (b outLen : Nat) : List Nat := base2bGo x b outLen 0 0 0

/-- The `i`-th `n`-byte block of a byte string. -/
def block (p : Params) (s : Bytes) (i : Nat) : Bytes := (s.drop (i * p.n)).take p.n

/-! ## Addresses (§4.2, §11.2) -/

structure Adrs where
  layer : Nat
  tree : Nat
  typ : Nat
  /-- Word 1: key pair address. -/
  keypair : Nat
  /-- Word 2: chain address or tree height. -/
  word2 : Nat
  /-- Word 3: hash address or tree index. -/
  word3 : Nat

def WOTS_HASH : Nat := 0
def WOTS_PK : Nat := 1
def TREE : Nat := 2
def FORS_TREE : Nat := 3
def FORS_ROOTS : Nat := 4
def WOTS_PRF : Nat := 5
def FORS_PRF : Nat := 6

def Adrs.zero : Adrs := ⟨0, 0, 0, 0, 0, 0⟩

/-- `setTypeAndClear`. -/
def Adrs.setTypeAndClear (x : Adrs) (t : Nat) : Adrs :=
  { x with typ := t, keypair := 0, word2 := 0, word3 := 0 }

/-- The 32-byte address: layer (4) ‖ tree (12) ‖ type (4) ‖ three words (4 each). -/
def Adrs.bytes (x : Adrs) : Bytes :=
  toByte x.layer 4 ++ toByte x.tree 12 ++ toByte x.typ 4 ++
    toByte x.keypair 4 ++ toByte x.word2 4 ++ toByte x.word3 4

/-- The compressed address `ADRSc = ADRS[3] ‖ ADRS[8:16] ‖ ADRS[19] ‖ ADRS[20:32]`. -/
def Adrs.compress (x : Adrs) : Bytes :=
  let b := x.bytes
  [b[3]!] ++ (b.drop 8).take 8 ++ [b[19]!] ++ (b.drop 20).take 12

/-! ## Hash functions (§11.2)

§11.2.1 (security category 1) applies when `n = 16`, §11.2.2 (categories 3
and 5) when `n = 24` or `n = 32` (§11, first paragraph after Table 2). -/

/-- `F`: `Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 − n) ‖ ADRSc ‖ M_1))`, in
both §11.2.1 and §11.2.2. -/
def F (p : Params) (pkSeed : Bytes) (adrs : Adrs) (msg : Bytes) : Bytes :=
  match p.family with
  | .shake => shake256 (pkSeed ++ adrs.bytes ++ msg) p.n
  | .sha2 =>
    (sha256 (pkSeed ++ toByte 0 (64 - p.n) ++ adrs.compress ++ msg)).take p.n

/-- `PRF`: `Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 − n) ‖ ADRSc ‖ SK.seed))`,
in both §11.2.1 and §11.2.2. -/
def PRF (p : Params) (pkSeed skSeed : Bytes) (adrs : Adrs) : Bytes :=
  match p.family with
  | .shake => shake256 (pkSeed ++ adrs.bytes ++ skSeed) p.n
  | .sha2 =>
    (sha256 (pkSeed ++ toByte 0 (64 - p.n) ++ adrs.compress ++ skSeed)).take p.n

/-- `H`: `Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 − n) ‖ ADRSc ‖ M_2))` for
`n = 16` (§11.2.1) and `Trunc_n(SHA-512(PK.seed ‖ toByte(0, 128 − n) ‖ ADRSc ‖ M_2))`
otherwise (§11.2.2). -/
def H (p : Params) (pkSeed : Bytes) (adrs : Adrs) (msg : Bytes) : Bytes :=
  match p.family with
  | .shake => shake256 (pkSeed ++ adrs.bytes ++ msg) p.n
  | .sha2 =>
    if p.n = 16 then (sha256 (pkSeed ++ toByte 0 (64 - p.n) ++ adrs.compress ++ msg)).take p.n
    else (sha512 (pkSeed ++ toByte 0 (128 - p.n) ++ adrs.compress ++ msg)).take p.n

/-- `T_l`: the same formula as `H`, on `l` blocks. -/
def T (p : Params) (pkSeed : Bytes) (adrs : Adrs) (msg : Bytes) : Bytes :=
  match p.family with
  | .shake => shake256 (pkSeed ++ adrs.bytes ++ msg) p.n
  | .sha2 =>
    if p.n = 16 then (sha256 (pkSeed ++ toByte 0 (64 - p.n) ++ adrs.compress ++ msg)).take p.n
    else (sha512 (pkSeed ++ toByte 0 (128 - p.n) ++ adrs.compress ++ msg)).take p.n

/-- `PRF_msg`: `Trunc_n(HMAC-SHA-256(SK.prf, opt_rand ‖ M))` for `n = 16`,
with HMAC-SHA-512 otherwise. -/
def PRFmsg (p : Params) (skPrf optRand msg : Bytes) : Bytes :=
  match p.family with
  | .shake => shake256 (skPrf ++ optRand ++ msg) p.n
  | .sha2 =>
    if p.n = 16 then (hmacSha256 skPrf (optRand ++ msg)).take p.n
    else (hmacSha512 skPrf (optRand ++ msg)).take p.n

/-- MGF1 (RFC 8017 Appendix B.2.1) with a hash function of output length `hLen`. -/
def mgf1 (hash : Bytes → Bytes) (hLen : Nat) (seed : Bytes) (l : Nat) : Bytes :=
  ((List.range ((l + hLen - 1) / hLen)).flatMap fun c => hash (seed ++ toByte c 4)).take l

/-- `H_msg`: `MGF1-SHA-256(R ‖ PK.seed ‖ SHA-256(R ‖ PK.seed ‖ PK.root ‖ M), m)`
for `n = 16`, with SHA-512 in both places otherwise. -/
def Hmsg (p : Params) (r pkSeed pkRoot msg : Bytes) : Bytes :=
  match p.family with
  | .shake => shake256 (r ++ pkSeed ++ pkRoot ++ msg) p.m
  | .sha2 =>
    if p.n = 16 then mgf1 sha256 32 (r ++ pkSeed ++ sha256 (r ++ pkSeed ++ pkRoot ++ msg)) p.m
    else mgf1 sha512 64 (r ++ pkSeed ++ sha512 (r ++ pkSeed ++ pkRoot ++ msg)) p.m

/-! ## WOTS+ (§5) -/

/-- Algorithm 5, `chain`. -/
def chain (p : Params) (x : Bytes) (i s : Nat) (pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  (List.range s).foldl (fun tmp j => F p pkSeed { adrs with word3 := i + j } tmp) x

/-- The `len` base-`w` digits of a message and its checksum (Algorithm 7, lines 1–7). -/
def wotsDigits (p : Params) (msg : Bytes) : List Nat :=
  let digits := base2b msg p.lgw p.len1
  let csum := digits.foldl (fun c x => c + (p.w - 1 - x)) 0
  let csum := csum <<< ((8 - ((p.len2 * p.lgw) % 8)) % 8)
  digits ++ base2b (toByte csum ((p.len2 * p.lgw + 7) / 8)) p.lgw p.len2

def wotsSkAdrs (adrs : Adrs) : Adrs :=
  { adrs.setTypeAndClear WOTS_PRF with keypair := adrs.keypair }

def wotsPkAdrs (adrs : Adrs) : Adrs :=
  { adrs.setTypeAndClear WOTS_PK with keypair := adrs.keypair }

/-- Algorithm 6, `wots_pkGen`. -/
def wotsPkGen (p : Params) (skSeed pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let tmp := (List.range p.len).flatMap fun i =>
    let sk := PRF p pkSeed skSeed { wotsSkAdrs adrs with word2 := i }
    chain p sk 0 (p.w - 1) pkSeed { adrs with word2 := i }
  T p pkSeed (wotsPkAdrs adrs) tmp

/-- Algorithm 7, `wots_sign`. -/
def wotsSign (p : Params) (msg skSeed pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let digits := wotsDigits p msg
  (List.range p.len).flatMap fun i =>
    let sk := PRF p pkSeed skSeed { wotsSkAdrs adrs with word2 := i }
    chain p sk 0 digits[i]! pkSeed { adrs with word2 := i }

/-- Algorithm 8, `wots_pkFromSig`. -/
def wotsPkFromSig (p : Params) (sig msg pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let digits := wotsDigits p msg
  let tmp := (List.range p.len).flatMap fun i =>
    chain p (block p sig i) digits[i]! (p.w - 1 - digits[i]!) pkSeed { adrs with word2 := i }
  T p pkSeed (wotsPkAdrs adrs) tmp

/-! ## XMSS (§6) -/

/-- Algorithm 9, `xmss_node`. -/
def xmssNode (p : Params) (skSeed : Bytes) (i : Nat) (z : Nat) (pkSeed : Bytes) (adrs : Adrs) :
    Bytes :=
  match z with
  | 0 => wotsPkGen p skSeed pkSeed { adrs.setTypeAndClear WOTS_HASH with keypair := i }
  | z + 1 =>
    let lnode := xmssNode p skSeed (2 * i) z pkSeed adrs
    let rnode := xmssNode p skSeed (2 * i + 1) z pkSeed adrs
    H p pkSeed { adrs.setTypeAndClear TREE with word2 := z + 1, word3 := i } (lnode ++ rnode)

/-- Algorithm 10, `xmss_sign`: `sig ‖ AUTH`. -/
def xmssSign (p : Params) (msg skSeed : Bytes) (idx : Nat) (pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let auth := (List.range p.hp).flatMap fun j =>
    xmssNode p skSeed ((idx / 2 ^ j) ^^^ 1) j pkSeed adrs
  let sig := wotsSign p msg skSeed pkSeed { adrs.setTypeAndClear WOTS_HASH with keypair := idx }
  sig ++ auth

/-- Climbing an authentication path: Algorithm 11 lines 8–18 and Algorithm 17
lines 9–19. `idx` is the leaf index whose bits select left or right; `treeIdx`
is the tree index stored in the address, halved at every level. -/
def climb (p : Params) (node : Bytes) (idx treeIdx : Nat) (auth : Bytes) (height : Nat)
    (pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  ((List.range height).foldl (fun (st : Bytes × Nat) j =>
    let (node, ti) := st
    if (idx / 2 ^ j) % 2 = 0 then
      let ti := ti / 2
      (H p pkSeed { adrs with word2 := j + 1, word3 := ti } (node ++ block p auth j), ti)
    else
      let ti := (ti - 1) / 2
      (H p pkSeed { adrs with word2 := j + 1, word3 := ti } (block p auth j ++ node), ti))
    (node, treeIdx)).1

/-- Algorithm 11, `xmss_pkFromSig`. -/
def xmssPkFromSig (p : Params) (idx : Nat) (sig msg pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let wsig := sig.take (p.len * p.n)
  let auth := (sig.drop (p.len * p.n)).take (p.hp * p.n)
  let node := wotsPkFromSig p wsig msg pkSeed { adrs.setTypeAndClear WOTS_HASH with keypair := idx }
  climb p node idx idx auth p.hp pkSeed (adrs.setTypeAndClear TREE)

/-! ## Hypertree (§7)

Algorithms 12 and 13 treat layer 0 before their loop; here every layer is one
iteration of the same fold, which computes the same values. -/

/-- Algorithm 12, `ht_sign`. -/
def htSign (p : Params) (msg skSeed pkSeed : Bytes) (idxTree idxLeaf : Nat) : Bytes :=
  ((List.range p.d).foldl (fun (st : Bytes × Bytes × Nat × Nat) j =>
    let (sig, root, tree, leaf) := st
    let adrs := { Adrs.zero with layer := j, tree := tree }
    let s := xmssSign p root skSeed leaf pkSeed adrs
    (sig ++ s, xmssPkFromSig p leaf s root pkSeed adrs, tree >>> p.hp, tree % 2 ^ p.hp))
    ([], msg, idxTree, idxLeaf)).1

/-- Algorithm 13, `ht_verify`. -/
def htVerify (p : Params) (msg sig pkSeed : Bytes) (idxTree idxLeaf : Nat) (pkRoot : Bytes) : Bool :=
  let (node, _, _) := (List.range p.d).foldl (fun (st : Bytes × Nat × Nat) j =>
    let (node, tree, leaf) := st
    let adrs := { Adrs.zero with layer := j, tree := tree }
    let s := (sig.drop (j * p.xmssSigBytes)).take p.xmssSigBytes
    (xmssPkFromSig p leaf s node pkSeed adrs, tree >>> p.hp, tree % 2 ^ p.hp))
    (msg, idxTree, idxLeaf)
  node == pkRoot

/-! ## FORS (§8) -/

/-- Algorithm 14, `fors_skGen`. -/
def forsSkGen (p : Params) (skSeed pkSeed : Bytes) (adrs : Adrs) (idx : Nat) : Bytes :=
  PRF p pkSeed skSeed
    { adrs.setTypeAndClear FORS_PRF with keypair := adrs.keypair, word3 := idx }

/-- Algorithm 15, `fors_node`. -/
def forsNode (p : Params) (skSeed : Bytes) (i : Nat) (z : Nat) (pkSeed : Bytes) (adrs : Adrs) :
    Bytes :=
  match z with
  | 0 => F p pkSeed { adrs with word2 := 0, word3 := i } (forsSkGen p skSeed pkSeed adrs i)
  | z + 1 =>
    let lnode := forsNode p skSeed (2 * i) z pkSeed adrs
    let rnode := forsNode p skSeed (2 * i + 1) z pkSeed adrs
    H p pkSeed { adrs with word2 := z + 1, word3 := i } (lnode ++ rnode)

/-- Algorithm 16, `fors_sign`. -/
def forsSign (p : Params) (md skSeed pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let indices := base2b md p.a p.k
  (List.range p.k).flatMap fun i =>
    forsSkGen p skSeed pkSeed adrs (i * 2 ^ p.a + indices[i]!) ++
      (List.range p.a).flatMap fun j =>
        let s := (indices[i]! / 2 ^ j) ^^^ 1
        forsNode p skSeed (i * 2 ^ (p.a - j) + s) j pkSeed adrs

/-- Algorithm 17, `fors_pkFromSig`. -/
def forsPkFromSig (p : Params) (sig md pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let indices := base2b md p.a p.k
  let roots := (List.range p.k).flatMap fun i =>
    let sk := block p sig (i * (p.a + 1))
    let leaf := i * 2 ^ p.a + indices[i]!
    let node := F p pkSeed { adrs with word2 := 0, word3 := leaf } sk
    let auth := (sig.drop ((i * (p.a + 1) + 1) * p.n)).take (p.a * p.n)
    climb p node indices[i]! leaf auth p.a pkSeed adrs
  T p pkSeed { adrs.setTypeAndClear FORS_ROOTS with keypair := adrs.keypair } roots

/-! ## SLH-DSA (§9, §10) -/

/-- The tree index in the digest (Algorithm 19, lines 7 and 9). -/
def digestTree (p : Params) (digest : Bytes) : Nat :=
  toInt ((digest.drop p.mdBytes).take p.treeBytes) % 2 ^ (p.h - p.h / p.d)

/-- The leaf index in the digest (Algorithm 19, lines 8 and 10). -/
def digestLeaf (p : Params) (digest : Bytes) : Nat :=
  toInt ((digest.drop (p.mdBytes + p.treeBytes)).take p.leafBytes) % 2 ^ (p.h / p.d)

/-- Algorithm 18, `slh_keygen_internal`: returns `(SK, PK)`. -/
def slhKeygenInternal (p : Params) (skSeed skPrf pkSeed : Bytes) : Bytes × Bytes :=
  let adrs := { Adrs.zero with layer := p.d - 1 }
  let pkRoot := xmssNode p skSeed 0 p.hp pkSeed adrs
  (skSeed ++ skPrf ++ pkSeed ++ pkRoot, pkSeed ++ pkRoot)

/-- Algorithm 19, `slh_sign_internal`, with `opt_rand = addrnd`. -/
def slhSignInternal (p : Params) (msg sk addrnd : Bytes) : Bytes :=
  let skSeed := block p sk 0
  let skPrf := block p sk 1
  let pkSeed := block p sk 2
  let pkRoot := block p sk 3
  let r := PRFmsg p skPrf addrnd msg
  let digest := Hmsg p r pkSeed pkRoot msg
  let md := digest.take p.mdBytes
  let idxTree := digestTree p digest
  let idxLeaf := digestLeaf p digest
  let adrs := { { Adrs.zero with tree := idxTree }.setTypeAndClear FORS_TREE with keypair := idxLeaf }
  let sigFors := forsSign p md skSeed pkSeed adrs
  let pkFors := forsPkFromSig p sigFors md pkSeed adrs
  let sigHt := htSign p pkFors skSeed pkSeed idxTree idxLeaf
  r ++ sigFors ++ sigHt

/-- Algorithm 20, `slh_verify_internal`. -/
def slhVerifyInternal (p : Params) (msg sig pk : Bytes) : Bool :=
  if sig.length ≠ p.sigBytes then false else
  let pkSeed := block p pk 0
  let pkRoot := block p pk 1
  let r := sig.take p.n
  let sigFors := (sig.drop p.n).take p.forsSigBytes
  let sigHt := sig.drop (p.n + p.forsSigBytes)
  let digest := Hmsg p r pkSeed pkRoot msg
  let md := digest.take p.mdBytes
  let idxTree := digestTree p digest
  let idxLeaf := digestLeaf p digest
  let adrs := { { Adrs.zero with tree := idxTree }.setTypeAndClear FORS_TREE with keypair := idxLeaf }
  let pkFors := forsPkFromSig p sigFors md pkSeed adrs
  htVerify p pkFors sigHt pkSeed idxTree idxLeaf pkRoot

/-- The message actually signed by the pure variant (Algorithms 22 and 24). -/
def withContext (msg ctx : Bytes) : Bytes :=
  toByte 0 1 ++ toByte ctx.length 1 ++ ctx ++ msg

/-- Algorithm 22, `slh_sign`, with caller-supplied randomness. -/
def slhSign (p : Params) (msg ctx sk addrnd : Bytes) : Option Bytes :=
  if ctx.length > 255 then none else some (slhSignInternal p (withContext msg ctx) sk addrnd)

/-- Algorithm 24, `slh_verify`. -/
def slhVerify (p : Params) (msg sig ctx pk : Bytes) : Bool :=
  if ctx.length > 255 then false else slhVerifyInternal p (withContext msg ctx) sig pk

end Spec
