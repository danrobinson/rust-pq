-- Generated from the locked peer by scripts/extract-peer-callers.py.
import PeerEquality.CallerTypes

namespace slhdsa.PeerCall
open Spec

def keygen (c : Children) (p : Params) (sk prf pk : Bytes) : Key :=
  let root := c.xmss.node sk 0 p.hp pk (layer (p.d-1) 0)
  ⟨sk,prf,pk,root⟩

def rawSign (c : Children) (p : Params) (k : Key) (msg : Parts) (opt_rand : Option Bytes) : Signature :=
  let rand := opt_rand.getD k.publicSeed
  let sk_seed := k.seed
  let pk_seed := k.publicSeed
  let ht := pk_seed
  let randomizer := c.prfMsg k.prf rand msg
  let digest := c.hMsg randomizer pk_seed k.root msg
  let (md, idx_tree, idx_leaf) := splitResult p digest
  let adrs := forsAddress idx_tree idx_leaf
  let fors_sig := c.forsSign md sk_seed ht adrs
  let fors_pk := c.forsRecover fors_sig md ht adrs
  let ht_sig := PeerCall.ht c.xmss p fors_pk sk_seed ht idx_tree idx_leaf
  ⟨randomizer, fors_sig, ht_sig⟩

def rawVerify (c : Children) (p : Params) (k : PublicKey) (msg : Parts) (signature : Signature) : Bool :=
  let pk_seed := k.seed
  let ht := pk_seed
  let randomizer := signature.r
  let fors_sig := signature.fors
  let ht_sig := signature.tree
  let digest := c.hMsg randomizer pk_seed k.root msg
  let (md, idx_tree, idx_leaf) := splitResult p digest
  let adrs := forsAddress idx_tree idx_leaf
  let fors_pk := c.forsRecover fors_sig md ht adrs
  htVerifyWith c.xmss p fors_pk ht_sig ht idx_tree idx_leaf k.root

def signCtx (c : Children) (p : Params) (k : Key) (msg : List Bytes) (ctx : Bytes) (rand : Option Bytes) : Option Signature :=
  if ctx.length ≤ 255 then some (rawSign c p k (contextParts ctx msg) rand) else none

def verifyCtx (c : Children) (p : Params) (k : PublicKey) (msg : List Bytes) (ctx : Bytes) (s : Signature) : Bool :=
  if ctx.length ≤ 255 then rawVerify c p k (contextParts ctx msg) s else false

end slhdsa.PeerCall
