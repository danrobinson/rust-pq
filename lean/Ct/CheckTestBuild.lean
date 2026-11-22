import Ct.Check

/-!
# Tests of the leakage-model checks for this tree

The one primitive of this translation that `Ct/Model.lean` does not cover,
`core.slice.index.Slice.index_mut` (`Ct/ModelBuild.lean`), resolves to its instrumented
version in the generated text and emits the range; the checker rejects the un-instrumented one
and the un-whitelisted 128-bit operations are still caught when they leak (division).
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open slhdsa

namespace slhdsa_leak

#ct_resolves core.slice.index.Slice.index_mut

namespace hash
-- inside `def hash.f` the current namespace is `slhdsa_leak.hash`
#ct_resolves core.slice.index.Slice.index_mut
end hash

/-- A mutable sub-slice of a slice emits its range and the slice's length. -/
example (s : Aeneas.Std.Slice Std.U8) (a b : Std.Usize) :
    core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s
      { start := a, «end» := b } =
    Ct.Leak.prim [.range a.val b.val s.length]
      (Aeneas.Std.core.slice.index.Slice.index_mut
        (Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s
        { start := a, «end» := b }) := rfl

/-- `/` on 64-bit and 128-bit integers is the leaking division. -/
example (x y : Std.U64) : (x / y) = Ct.Leak.prim [.div x.val y.val] (UScalar.div x y) := rfl
example (x y : Std.U128) : (x / y) = Ct.Leak.prim [.div x.val y.val] (UScalar.div x y) := rfl

end slhdsa_leak

namespace Ct.CheckTestBuild

def badSliceIndexMut (s : Aeneas.Std.Slice Std.U8) :
    Ct.Leak (Aeneas.Std.Slice Std.U8 × (Aeneas.Std.Slice Std.U8 → Aeneas.Std.Slice Std.U8)) := do
  let r ← Aeneas.Std.core.slice.index.Slice.index_mut
    (Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice Std.U8) s
    { start := 0#usize, «end» := 1#usize }
  Ct.Leak.pure r
#ct_expect_reject badSliceIndexMut Aeneas.Std.core.slice.index.Slice.index_mut

def badDiv128 (x y : Std.U128) : Ct.Leak Std.U128 := do
  let z ← Aeneas.Std.UScalar.div x y
  Ct.Leak.pure z
#ct_expect_reject badDiv128 Aeneas.Std.UScalar.div

end Ct.CheckTestBuild
