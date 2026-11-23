import PeerEquality.Layers

namespace slhdsa.PeerCall
open Spec

structure Key where
  seed : Bytes
  prf : Bytes
  publicSeed : Bytes
  root : Bytes

structure PublicKey where
  seed : Bytes
  root : Bytes

structure Signature where
  r : Bytes
  fors : Bytes
  tree : Bytes

def Key.bytes (k : Key) := k.seed ++ k.prf ++ k.publicSeed ++ k.root
def Key.public (k : Key) : PublicKey := ⟨k.publicSeed,k.root⟩
def PublicKey.bytes (k : PublicKey) := k.seed ++ k.root
def Signature.bytes (s : Signature) := s.r ++ s.fors ++ s.tree

abbrev Parts := List (List Bytes)

structure Children where
  xmss : Xmss
  prfMsg : Bytes → Bytes → Parts → Bytes
  hMsg : Bytes → Bytes → Bytes → Parts → Bytes
  split : Bytes → Bytes × Nat × Nat
  forsSign : Bytes → Bytes → Bytes → Adrs → Bytes
  forsRecover : Bytes → Bytes → Bytes → Adrs → Bytes
  htVerify : Bytes → Bytes → Bytes → Nat → Nat → Bytes → Bool

def specChildren (p : Params) : Children :=
  ⟨xmssSpec p, fun k r m => PRFmsg p k r m.flatten.flatten,
   fun r s root m => Hmsg p r s root m.flatten.flatten,
   fun d => (d.take p.mdBytes,digestTree p d,digestLeaf p d), forsSign p,forsPkFromSig p,htVerify p⟩

def forsAddress (tree leaf : Nat) : Adrs :=
  { Adrs.zero with tree := tree, typ := FORS_TREE, keypair := leaf }

def contextParts (ctx : Bytes) (msg : List Bytes) : Parts :=
  [[[0#8],[BitVec.ofNat 8 ctx.length],ctx],msg]

end slhdsa.PeerCall
