import Spec

/-!
# The SLH-DSA-SHA2-128s specification of the single-set tree

A verbatim copy of `../../lean/Spec/SlhDsa.lean` and `../../lean/Spec/Checked.lean`
(the specification the proofs of `../../lean` are stated against), in the
namespace `Spec128` so that it can sit beside the generic `Spec`. Only the
definitions that do not depend on the parameter set are not copied: `toInt`,
`base2b` and its loops, the address type and its functions, and SHA-256 /
HMAC-SHA-256, which are taken from `Spec` (where they are character-for-character
the same definitions). `Slhdsa/Compat128.lean` proves that the generic
specification at `Spec.sha2_128s` is this one.
-/

namespace Spec128

open Spec (Byte Bytes toByte sha256 hmacSha256 toInt base2bFill base2bGo base2b Adrs
  WOTS_HASH WOTS_PK TREE FORS_TREE FORS_ROOTS WOTS_PRF FORS_PRF withContext)

/-! ## Parameters (FIPS 205 Table 2, SLH-DSA-SHA2-128s) -/

def n : Nat := 16
def h : Nat := 63
def d : Nat := 7
def hp : Nat := 9
def a : Nat := 12
def k : Nat := 14
def lgw : Nat := 4
def m : Nat := 30
def w : Nat := 16
def len1 : Nat := 32
def len2 : Nat := 3
def len : Nat := 35

/-- The `i`-th `n`-byte block of a byte string. -/
def block (s : Bytes) (i : Nat) : Bytes := (s.drop (i * n)).take n

/-! ## Hash functions (§11.2.1, SHA2, security category 1) -/

/-- `Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 − n) ‖ ADRSc ‖ M))`: this is `F`, `H` and `T_l`. -/
def thash (pkSeed : Bytes) (adrs : Adrs) (msg : Bytes) : Bytes :=
  (sha256 (pkSeed ++ toByte 0 (64 - n) ++ adrs.compress ++ msg)).take n

def F := thash
def H := thash
def T := thash

def PRF (pkSeed skSeed : Bytes) (adrs : Adrs) : Bytes := thash pkSeed adrs skSeed

def PRFmsg (skPrf optRand msg : Bytes) : Bytes :=
  (hmacSha256 skPrf (optRand ++ msg)).take n

/-- MGF1 with SHA-256 (NIST SP 800-56B §7.2.2.2). -/
def mgf1 (seed : Bytes) (l : Nat) : Bytes :=
  ((List.range ((l + 31) / 32)).flatMap fun c => sha256 (seed ++ toByte c 4)).take l

def Hmsg (r pkSeed pkRoot msg : Bytes) : Bytes :=
  mgf1 (r ++ pkSeed ++ sha256 (r ++ pkSeed ++ pkRoot ++ msg)) m

/-! ## WOTS+ (§5) -/

/-- Algorithm 5, `chain`. -/
def chain (x : Bytes) (i s : Nat) (pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  (List.range s).foldl (fun tmp j => F pkSeed { adrs with word3 := i + j } tmp) x

/-- The `len` base-`w` digits of a message and its checksum (Algorithm 7, lines 1–7). -/
def wotsDigits (msg : Bytes) : List Nat :=
  let digits := base2b msg lgw len1
  let csum := digits.foldl (fun c x => c + (w - 1 - x)) 0
  let csum := csum <<< ((8 - ((len2 * lgw) % 8)) % 8)
  digits ++ base2b (toByte csum ((len2 * lgw + 7) / 8)) lgw len2

def wotsSkAdrs (adrs : Adrs) : Adrs :=
  { adrs.setTypeAndClear WOTS_PRF with keypair := adrs.keypair }

def wotsPkAdrs (adrs : Adrs) : Adrs :=
  { adrs.setTypeAndClear WOTS_PK with keypair := adrs.keypair }

/-- Algorithm 6, `wots_pkGen`. -/
def wotsPkGen (skSeed pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let tmp := (List.range len).flatMap fun i =>
    let sk := PRF pkSeed skSeed { wotsSkAdrs adrs with word2 := i }
    chain sk 0 (w - 1) pkSeed { adrs with word2 := i }
  T pkSeed (wotsPkAdrs adrs) tmp

/-- Algorithm 7, `wots_sign`. -/
def wotsSign (msg skSeed pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let digits := wotsDigits msg
  (List.range len).flatMap fun i =>
    let sk := PRF pkSeed skSeed { wotsSkAdrs adrs with word2 := i }
    chain sk 0 digits[i]! pkSeed { adrs with word2 := i }

/-- Algorithm 8, `wots_pkFromSig`. -/
def wotsPkFromSig (sig msg pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let digits := wotsDigits msg
  let tmp := (List.range len).flatMap fun i =>
    chain (block sig i) digits[i]! (w - 1 - digits[i]!) pkSeed { adrs with word2 := i }
  T pkSeed (wotsPkAdrs adrs) tmp

/-! ## XMSS (§6) -/

/-- Algorithm 9, `xmss_node`. -/
def xmssNode (skSeed : Bytes) (i : Nat) (z : Nat) (pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  match z with
  | 0 => wotsPkGen skSeed pkSeed { adrs.setTypeAndClear WOTS_HASH with keypair := i }
  | z + 1 =>
    let lnode := xmssNode skSeed (2 * i) z pkSeed adrs
    let rnode := xmssNode skSeed (2 * i + 1) z pkSeed adrs
    H pkSeed { adrs.setTypeAndClear TREE with word2 := z + 1, word3 := i } (lnode ++ rnode)

/-- Algorithm 10, `xmss_sign`: `sig ‖ AUTH`. -/
def xmssSign (msg skSeed : Bytes) (idx : Nat) (pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let auth := (List.range hp).flatMap fun j =>
    xmssNode skSeed ((idx / 2 ^ j) ^^^ 1) j pkSeed adrs
  let sig := wotsSign msg skSeed pkSeed { adrs.setTypeAndClear WOTS_HASH with keypair := idx }
  sig ++ auth

/-- Climbing an authentication path: Algorithm 11 lines 8–18 and Algorithm 17
lines 9–19. `idx` is the leaf index whose bits select left or right; `treeIdx`
is the tree index stored in the address, halved at every level. -/
def climb (node : Bytes) (idx treeIdx : Nat) (auth : Bytes) (height : Nat)
    (pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  ((List.range height).foldl (fun (st : Bytes × Nat) j =>
    let (node, ti) := st
    if (idx / 2 ^ j) % 2 = 0 then
      let ti := ti / 2
      (H pkSeed { adrs with word2 := j + 1, word3 := ti } (node ++ block auth j), ti)
    else
      let ti := (ti - 1) / 2
      (H pkSeed { adrs with word2 := j + 1, word3 := ti } (block auth j ++ node), ti))
    (node, treeIdx)).1

/-- Algorithm 11, `xmss_pkFromSig`. -/
def xmssPkFromSig (idx : Nat) (sig msg pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let wsig := sig.take (len * n)
  let auth := (sig.drop (len * n)).take (hp * n)
  let node := wotsPkFromSig wsig msg pkSeed { adrs.setTypeAndClear WOTS_HASH with keypair := idx }
  climb node idx idx auth hp pkSeed (adrs.setTypeAndClear TREE)

/-! ## Hypertree (§7)

Algorithms 12 and 13 treat layer 0 before their loop; here every layer is one
iteration of the same fold, which computes the same values. -/

def xmssSigBytes : Nat := (len + hp) * n

/-- Algorithm 12, `ht_sign`. -/
def htSign (msg skSeed pkSeed : Bytes) (idxTree idxLeaf : Nat) : Bytes :=
  ((List.range d).foldl (fun (st : Bytes × Bytes × Nat × Nat) j =>
    let (sig, root, tree, leaf) := st
    let adrs := { Spec.Adrs.zero with layer := j, tree := tree }
    let s := xmssSign root skSeed leaf pkSeed adrs
    (sig ++ s, xmssPkFromSig leaf s root pkSeed adrs, tree >>> hp, tree % 2 ^ hp))
    ([], msg, idxTree, idxLeaf)).1

/-- Algorithm 13, `ht_verify`. -/
def htVerify (msg sig pkSeed : Bytes) (idxTree idxLeaf : Nat) (pkRoot : Bytes) : Bool :=
  let (node, _, _) := (List.range d).foldl (fun (st : Bytes × Nat × Nat) j =>
    let (node, tree, leaf) := st
    let adrs := { Spec.Adrs.zero with layer := j, tree := tree }
    let s := (sig.drop (j * xmssSigBytes)).take xmssSigBytes
    (xmssPkFromSig leaf s node pkSeed adrs, tree >>> hp, tree % 2 ^ hp))
    (msg, idxTree, idxLeaf)
  node == pkRoot

/-! ## FORS (§8) -/

/-- Algorithm 14, `fors_skGen`. -/
def forsSkGen (skSeed pkSeed : Bytes) (adrs : Adrs) (idx : Nat) : Bytes :=
  PRF pkSeed skSeed
    { adrs.setTypeAndClear FORS_PRF with keypair := adrs.keypair, word3 := idx }

/-- Algorithm 15, `fors_node`. -/
def forsNode (skSeed : Bytes) (i : Nat) (z : Nat) (pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  match z with
  | 0 => F pkSeed { adrs with word2 := 0, word3 := i } (forsSkGen skSeed pkSeed adrs i)
  | z + 1 =>
    let lnode := forsNode skSeed (2 * i) z pkSeed adrs
    let rnode := forsNode skSeed (2 * i + 1) z pkSeed adrs
    H pkSeed { adrs with word2 := z + 1, word3 := i } (lnode ++ rnode)

/-- Algorithm 16, `fors_sign`. -/
def forsSign (md skSeed pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let indices := base2b md a k
  (List.range k).flatMap fun i =>
    forsSkGen skSeed pkSeed adrs (i * 2 ^ a + indices[i]!) ++
      (List.range a).flatMap fun j =>
        let s := (indices[i]! / 2 ^ j) ^^^ 1
        forsNode skSeed (i * 2 ^ (a - j) + s) j pkSeed adrs

/-- Algorithm 17, `fors_pkFromSig`. -/
def forsPkFromSig (sig md pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let indices := base2b md a k
  let roots := (List.range k).flatMap fun i =>
    let sk := block sig (i * (a + 1))
    let leaf := i * 2 ^ a + indices[i]!
    let node := F pkSeed { adrs with word2 := 0, word3 := leaf } sk
    let auth := (sig.drop ((i * (a + 1) + 1) * n)).take (a * n)
    climb node indices[i]! leaf auth a pkSeed adrs
  T pkSeed { adrs.setTypeAndClear FORS_ROOTS with keypair := adrs.keypair } roots

/-! ## SLH-DSA (§9, §10) -/

def mdBytes : Nat := (k * a + 7) / 8
def treeBytes : Nat := (h - h / d + 7) / 8
def leafBytes : Nat := (h / d + 7) / 8
def forsSigBytes : Nat := k * (1 + a) * n
def sigBytes : Nat := (1 + k * (1 + a) + h + d * len) * n

def digestTree (digest : Bytes) : Nat :=
  toInt ((digest.drop mdBytes).take treeBytes) % 2 ^ (h - h / d)

def digestLeaf (digest : Bytes) : Nat :=
  toInt ((digest.drop (mdBytes + treeBytes)).take leafBytes) % 2 ^ (h / d)

/-- Algorithm 18, `slh_keygen_internal`: returns `(SK, PK)`. -/
def slhKeygenInternal (skSeed skPrf pkSeed : Bytes) : Bytes × Bytes :=
  let adrs := { Spec.Adrs.zero with layer := d - 1 }
  let pkRoot := xmssNode skSeed 0 hp pkSeed adrs
  (skSeed ++ skPrf ++ pkSeed ++ pkRoot, pkSeed ++ pkRoot)

/-- Algorithm 19, `slh_sign_internal`, with `opt_rand = addrnd`. -/
def slhSignInternal (msg sk addrnd : Bytes) : Bytes :=
  let skSeed := block sk 0
  let skPrf := block sk 1
  let pkSeed := block sk 2
  let pkRoot := block sk 3
  let r := PRFmsg skPrf addrnd msg
  let digest := Hmsg r pkSeed pkRoot msg
  let md := digest.take mdBytes
  let idxTree := digestTree digest
  let idxLeaf := digestLeaf digest
  let adrs := { { Spec.Adrs.zero with tree := idxTree }.setTypeAndClear FORS_TREE with keypair := idxLeaf }
  let sigFors := forsSign md skSeed pkSeed adrs
  let pkFors := forsPkFromSig sigFors md pkSeed adrs
  let sigHt := htSign pkFors skSeed pkSeed idxTree idxLeaf
  r ++ sigFors ++ sigHt

/-- Algorithm 20, `slh_verify_internal`. -/
def slhVerifyInternal (msg sig pk : Bytes) : Bool :=
  if sig.length ≠ sigBytes then false else
  let pkSeed := block pk 0
  let pkRoot := block pk 1
  let r := sig.take n
  let sigFors := (sig.drop n).take forsSigBytes
  let sigHt := sig.drop (n + forsSigBytes)
  let digest := Hmsg r pkSeed pkRoot msg
  let md := digest.take mdBytes
  let idxTree := digestTree digest
  let idxLeaf := digestLeaf digest
  let adrs := { { Spec.Adrs.zero with tree := idxTree }.setTypeAndClear FORS_TREE with keypair := idxLeaf }
  let pkFors := forsPkFromSig sigFors md pkSeed adrs
  htVerify pkFors sigHt pkSeed idxTree idxLeaf pkRoot

/-- Algorithm 22, `slh_sign`, with caller-supplied randomness. -/
def slhSign (msg ctx sk addrnd : Bytes) : Option Bytes :=
  if ctx.length > 255 then none else some (slhSignInternal (withContext msg ctx) sk addrnd)

/-- Algorithm 24, `slh_verify`. -/
def slhVerify (msg sig ctx pk : Bytes) : Bool :=
  if ctx.length > 255 then false else slhVerifyInternal (withContext msg ctx) sig pk


/-! ## The checked signer (`../lean/Spec/Checked.lean`) -/


/-- The FORS public key from the secret seed alone: the roots of the `k`
trees (`forsNode … i a …`), compressed as in Algorithm 17, line 21. -/
def forsPkGen (skSeed pkSeed : Bytes) (adrs : Adrs) : Bytes :=
  let roots := (List.range k).flatMap fun i => forsNode skSeed i a pkSeed adrs
  T pkSeed { adrs.setTypeAndClear FORS_ROOTS with keypair := adrs.keypair } roots

/-- One layer of the checked hypertree signer. The state is
`(sig, msgA, msgB, ok, tree, leaf)`: the layer signs `msgA`, recomputes the
root from that signature with `msgB` as the message (`rootA`), computes the
root again from the secret seed (`rootB`; on the top layer, `PK.root`), and
clears `ok` if the two differ. -/
def htCheckedStep (skSeed pkSeed pkRoot : Bytes)
    (st : Bytes × Bytes × Bytes × Bool × Nat × Nat) (j : Nat) :
    Bytes × Bytes × Bytes × Bool × Nat × Nat :=
  let (sig, msgA, msgB, ok, tree, leaf) := st
  let adrs := { Spec.Adrs.zero with layer := j, tree := tree }
  let s := xmssSign msgA skSeed leaf pkSeed adrs
  let rootA := xmssPkFromSig leaf s msgB pkSeed adrs
  let rootB := if j + 1 < d then xmssNode skSeed 0 hp pkSeed adrs else pkRoot
  (sig ++ s, rootA, rootB, ok && rootA == rootB, tree >>> hp, tree % 2 ^ hp)

/-- The checked hypertree signer (`ht_sign_checked`): the signature, and
whether `mA = mB` and every pair of roots agreed. -/
def htSignChecked (mA mB skSeed pkSeed : Bytes) (idxTree idxLeaf : Nat) (pkRoot : Bytes) :
    Bytes × Bool :=
  let (sig, _, _, ok, _, _) := (List.range d).foldl (htCheckedStep skSeed pkSeed pkRoot)
    ([], mA, mB, mA == mB, idxTree, idxLeaf)
  (sig, ok)

/-- The checked signer (`slh_sign_internal_checked`): Algorithm 19, with the
FORS public key computed both from the FORS signature and from the secret
seed, and the hypertree signed by `htSignChecked`. -/
def slhSignInternalChecked (msg sk addrnd : Bytes) : Option Bytes :=
  let skSeed := block sk 0
  let skPrf := block sk 1
  let pkSeed := block sk 2
  let pkRoot := block sk 3
  let r := PRFmsg skPrf addrnd msg
  let digest := Hmsg r pkSeed pkRoot msg
  let md := digest.take mdBytes
  let idxTree := digestTree digest
  let idxLeaf := digestLeaf digest
  let adrs := { { Spec.Adrs.zero with tree := idxTree }.setTypeAndClear FORS_TREE with keypair := idxLeaf }
  let sigFors := forsSign md skSeed pkSeed adrs
  let pkForsA := forsPkFromSig sigFors md pkSeed adrs
  let pkForsB := forsPkGen skSeed pkSeed adrs
  let (sigHt, ok) := htSignChecked pkForsA pkForsB skSeed pkSeed idxTree idxLeaf pkRoot
  if ok then some (r ++ sigFors ++ sigHt) else none

/-- Algorithm 22 on the checked signer (`slh_sign_checked`). -/
def slhSignChecked (msg ctx sk addrnd : Bytes) : Option Bytes :=
  if ctx.length > 255 then none else slhSignInternalChecked (withContext msg ctx) sk addrnd

/-- A private key is well formed when its last block is the root that key
generation (Algorithm 18) derives from its first and third blocks. -/
def KeyOk (sk : Bytes) : Prop :=
  block sk 3 = xmssNode (block sk 0) 0 hp (block sk 2) { Spec.Adrs.zero with layer := d - 1 }

/-- The public key held in a private key: `PK.seed ‖ PK.root`, its last two blocks. -/
def skPk (sk : Bytes) : Bytes := sk.drop (2 * n)

end Spec128
