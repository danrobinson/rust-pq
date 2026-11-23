import Slhdsa.Funs
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch

/-- The immutable slice chunk iterator keeps the unconsumed suffix and chunk size. -/
structure core.slice.iter.Chunks (T : Type u) where
  rest : Slice T
  width : Usize

def core.slice.Slice.chunks {T : Type u} (xs : Slice T) (width : Usize) : Result (core.slice.iter.Chunks T) :=
  if width.val=0 then fail .panic else ok ⟨xs,width⟩

def core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next {T : Type u}
    (it : core.slice.iter.Chunks T) : Result (Option (Slice T) × core.slice.iter.Chunks T) :=
  if it.rest.val.isEmpty then ok (none,it)
  else if it.width.val=0 then fail .panic
  else
    let head := Slice.from (it.rest.val.take it.width.val) (by have := it.rest.property;simp <;> omega)
    let tail := Slice.from (it.rest.val.drop it.width.val) (by have := it.rest.property;simp <;> omega)
    ok (some head,⟨tail,it.width⟩)

end slhdsa.ShakeBatch
