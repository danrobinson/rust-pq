import Ct.Model

/-!
# The leakage model, build-specific part: the six-set crate, portable build

`Ct/Model.lean` (the single-set tree's table, unchanged) covers every primitive of this
translation but one: `core.slice.index.Slice.index_mut`, a mutable sub-slice of a *slice*
(`&mut blocks[a..b]` where `blocks` is itself a slice; the single-set tree only borrows sub-slices
of arrays mutably). It is instrumented exactly like its read-only counterpart
`core.slice.index.Slice.index` of `Ct/Model.lean`: the dictionary's event, i.e. for a range
`range r.start r.end s.length`.

| text                                        | event emitted                          |
|---------------------------------------------|----------------------------------------|
| `core.slice.index.Slice.index_mut inst s r` | `inst`'s event on `s` (`range`/`index`)|
-/

open Aeneas Aeneas.Std

namespace slhdsa_leak

open Ct

abbrev core.slice.index.Slice.index_mut {T I Output : Type _}
    (inst : LSliceIndex I (Aeneas.Std.Slice T) Output) (s : Aeneas.Std.Slice T) (i : I) :
    Ct.Leak (Output × (Output → Aeneas.Std.Slice T)) :=
  Leak.prim (inst.ev i s) (Aeneas.Std.core.slice.index.Slice.index_mut inst.base s i)

end slhdsa_leak

namespace Ct.Build

/-- The instrumented primitives of this build beyond those of `Ct/Model.lean`. -/
def modelConsts : List Lean.Name := [``slhdsa_leak.core.slice.index.Slice.index_mut]

end Ct.Build
