import Spec.SlhDsa

/-!
# The checked signer

Not part of FIPS 205. The crate's signer recomputes every value that a
one-time key signs by a second route and releases a signature only when the
two agree (see `rust/src/ht.rs`, `rust/src/slh.rs`). This file transcribes
that signer over the definitions of `Spec/SlhDsa.lean`, which it does not
change. `Spec/Correctness.lean` proves what it computes: the signature of the
standard whenever it returns one, a signature that verifies, and always a
signature for a key that key generation produces.
-/

namespace Spec

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
  let adrs := { Adrs.zero with layer := j, tree := tree }
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
  let adrs := { { Adrs.zero with tree := idxTree }.setTypeAndClear FORS_TREE with keypair := idxLeaf }
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
  block sk 3 = xmssNode (block sk 0) 0 hp (block sk 2) { Adrs.zero with layer := d - 1 }

/-- The public key held in a private key: `PK.seed ‖ PK.root`, its last two blocks. -/
def skPk (sk : Bytes) : Bytes := sk.drop (2 * n)

end Spec
