module
public import Slhdsa.Funs
public import Parentblock.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformParent.Driver

def blockAddress (a : address.Adrs) : ParentBlockRust.address.Adrs :=
  ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩

def makeBlock (n : Usize) (b : Array U8 128#usize) (a : address.Adrs) (l r : Slice U8) :=
  ParentBlockRust.sha512.parents.parent_block n b (blockAddress a) l r

abbrev Blocks (g : Usize) := Array (Array U8 128#usize) g
abbrev Nodes (n : Usize) := Slice (Array U8 n)
structure Kernel (g : Usize) where
  available : Result Bool
  compress {n : Usize} : Array U64 8#usize → Blocks g → Nodes n → Result (Nodes n)

end slhdsa.PlatformParent.Driver
