import Ct.Check

/-!
# Tests of the leakage-model checks

1. Name resolution: inside `namespace slhdsa_leak` (and inside a nested namespace, as in the
   body of `def sha256.f`), with the `open`s of the generated file, every shadowed name of the
   text resolves to the instrumented definition, and the infix `/` and `%` elaborate to the
   leaking instances.
2. The checker rejects un-instrumented operations (positive controls).
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open slhdsa

namespace slhdsa_leak

#ct_resolves Result
#ct_resolves ok
#ct_resolves lift
#ct_resolves loop
#ct_resolves Array.index_usize
#ct_resolves Array.update
#ct_resolves Array.index_mut_usize
#ct_resolves Slice.index_usize
#ct_resolves Slice.update
#ct_resolves Slice.index_mut_usize
#ct_resolves core.slice.index.SliceIndexRangeUsizeSlice
#ct_resolves core.slice.index.SliceIndexUsizeSlice
#ct_resolves core.ops.index.IndexSlice
#ct_resolves core.ops.index.IndexMutSlice
#ct_resolves core.array.Array.index
#ct_resolves core.array.Array.index_mut
#ct_resolves core.slice.index.Slice.index
#ct_resolves alloc.vec.Vec.index
#ct_resolves core.slice.Slice.copy_from_slice
#ct_resolves alloc.vec.Vec.extend_from_slice
#ct_resolves alloc.vec.Vec.push
#ct_resolves core.array.equality.PartialEqArray.eq
#ct_resolves core.clone.Clone
#ct_resolves core.marker.Copy

namespace sha256
-- inside `def sha256.f` the current namespace is `slhdsa_leak.sha256`
#ct_resolves Array.index_usize
#ct_resolves alloc.vec.Vec.push
end sha256

/-- `/` and `%` on machine integers elaborate to the leaking operations. -/
example (x y : Std.Usize) : (x / y) = Ct.Leak.prim [.div x.val y.val] (UScalar.div x y) := rfl
example (x y : Std.U32) : (x % y) = Ct.Leak.prim [.rem x.val y.val] (UScalar.rem x y) := rfl

/-- A `match` on an `Option` in a `do` block elaborates to `Leak.matchOpt`, which emits the
branch (`Ct/Do.lean`); no other `match` is accepted there. -/
example (o : Option Std.U8) :
    (do
      match o with
      | none => ok 0#u8
      | some x => ok x : Ct.Leak Std.U8) =
    Ct.Leak.matchOpt o (Ct.Leak.pure 0#u8) (fun x => Ct.Leak.pure x) := rfl

end slhdsa_leak

namespace Ct.CheckTest

/-! Positive controls: each definition misuses an un-instrumented operation. -/

def badIndex (a : Std.Array Std.U8 4#usize) (i : Std.Usize) : Ct.Leak Std.U8 := do
  let x ← Aeneas.Std.Array.index_usize a i
  Ct.Leak.pure x
#ct_expect_reject badIndex Aeneas.Std.Array.index_usize

def badPureIf (b : Bool) : Ct.Leak Std.U8 := Ct.Leak.pure (if b then 1#u8 else 2#u8)
#ct_expect_reject badPureIf ite

def badDiv (x y : Std.U32) : Ct.Leak Std.U32 := do
  let z ← Aeneas.Std.UScalar.div x y
  Ct.Leak.pure z

#ct_expect_reject badDiv Aeneas.Std.UScalar.div

def badCopy (s t : Aeneas.Std.Slice Std.U8) : Ct.Leak (Aeneas.Std.Slice Std.U8) := do
  let r ← Aeneas.Std.core.slice.Slice.copy_from_slice Aeneas.Std.core.marker.CopyU8 s t
  Ct.Leak.pure r
#ct_expect_reject badCopy Aeneas.Std.core.slice.Slice.copy_from_slice

def badLoop (x : Std.U32) : Ct.Leak Std.U32 := do
  let r ← Aeneas.Std.loop (fun (y : Std.U32) => Result.ok (ControlFlow.done y)) x
  Ct.Leak.pure r
#ct_expect_reject badLoop Aeneas.Std.loop

def badMatch (o : Option Std.U8) : Ct.Leak Std.U8 :=
  match o with
  | some x => Ct.Leak.pure x
  | none => Ct.Leak.pure 0#u8
set_option linter.auxLemma false in
#ct_expect_reject badMatch Ct.CheckTest.badMatch.match_1

end Ct.CheckTest
