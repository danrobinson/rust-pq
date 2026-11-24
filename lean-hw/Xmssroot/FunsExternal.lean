module
public import Xmssroot.Types
public import Xmsskeys.Funs
public import Treehash.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace XmssRootRust
def keySeed {N} (s : hash.Seed N) : XmssKeysRust.hash.Seed N := ⟨s.pk_seed,s.state,s.state512⟩
def keyAddr (a : address.Adrs) : XmssKeysRust.address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def parentSeed {N} (s : hash.Seed N) : TreeHashRust.hash.Seed N := ⟨s.pk_seed,s.state,s.state512⟩
def parentAddr (a : address.Adrs) : TreeHashRust.address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def xmss.hash2 {N} (seed : hash.Seed N) (a : address.Adrs) :=
  TreeHashRust.xmss.hash2 (parentSeed seed) (parentAddr a)
def xmss.wide.keys {N} (G L : Usize) (s : hash.Seed N) (sk : Array U8 N) (a : address.Adrs) :=
  XmssKeysRust.xmss.wide.keys G L (keySeed s) sk (keyAddr a)
end XmssRootRust
