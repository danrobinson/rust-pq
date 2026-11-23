module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result
namespace XmssKeysRust
structure core.slice.iter.ChunksMut (T : Type u) where
  slice : Slice T
  width : Usize
  offset : Nat
end XmssKeysRust
