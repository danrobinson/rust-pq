module
public import Xfors.Types
public import Leaf256.Funs
public import Parent256.Funs
public import Parentx86.Funs
public import Treehash.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace XForsRust
def leafAddr (a : address.Adrs) : LeafRust.address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def parentAddr (a : address.Adrs) : TreeRust.address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def scalarAddr (a : address.Adrs) : TreeHashRust.address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def coreAddr (a : address.Adrs) : slhdsa.address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def scalarSeed {N} (s : hash.Seed N) : TreeHashRust.hash.Seed N := ⟨s.pk_seed,s.state,s.state512⟩
def hash.thash_pair {N} (s : hash.Seed N) (a : address.Adrs) := TreeHashRust.hash.thash_pair (scalarSeed s) (scalarAddr a)
def sha256.x86.fors_leaves {N} (st : Array U32 8#usize) (sk : Array U8 N) (a : address.Adrs) :=
  LeafRust.sha256.x86.fors_leaves st sk (leafAddr a)
def sha256.x86.fors_parents {N : Usize} (st : Array U32 8#usize) (a : address.Adrs) :=
  TreeRust.sha256.x86.fors_parents (N:=N) st (parentAddr a)
def sha512.parents.parents {N : Usize} (st : Array U64 8#usize) (a : address.Adrs) :=
  Parentx86Rust.sha512.parents.parents (N:=N) st (coreAddr a)
end XForsRust
