import PeerEquality.Xmss
import PeerEquality.VerifyLayers
import PeerEquality.DigestSplit

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
  wots : PeerXmss.Children
  prfMsg : Bytes → Bytes → Parts → Bytes
  hMsg : Bytes → Bytes → Bytes → Parts → Bytes
  forsSign : Bytes → Bytes → Bytes → Adrs → Bytes
  forsRecover : Bytes → Bytes → Bytes → Adrs → Bytes

def Children.xmss (c : Children) (p : Params) := PeerXmss.operations c.wots p

def specChildren (p : Params) : Children :=
  ⟨PeerXmss.children p, fun k r m => PRFmsg p k r m.flatten.flatten,
   fun r s root m => Hmsg p r s root m.flatten.flatten,
   forsSign p,forsPkFromSig p⟩

def forsAddress (tree leaf : Nat) : Adrs :=
  { Adrs.zero with tree := tree, typ := FORS_TREE, keypair := leaf }

def contextParts (ctx : Bytes) (msg : List Bytes) : Parts :=
  [[[0#8],[BitVec.ofNat 8 ctx.length],ctx],msg]

end slhdsa.PeerCall
