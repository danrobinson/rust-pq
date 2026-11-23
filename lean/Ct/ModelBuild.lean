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
| `massert c` (Aeneas's `assert!`)            | `branch (decide c)`                    |

`massert` (added 2026-11-22, for the `assert!`s of `rust/src/adapter.rs`, which check the
lengths of a randomizer and of seeds) is the entry of the `hw-sha2` build's model
(`../lean-hw/Ct/ModelBuild.lean`, from the single-set tree), unchanged: an `if` that panics,
recorded as a branch.
-/

open Aeneas Aeneas.Std

namespace slhdsa_leak

open Ct

abbrev core.slice.index.Slice.index_mut {T I Output : Type _}
    (inst : LSliceIndex I (Aeneas.Std.Slice T) Output) (s : Aeneas.Std.Slice T) (i : I) :
    Ct.Leak (Output × (Output → Aeneas.Std.Slice T)) :=
  Leak.prim (inst.ev i s) (Aeneas.Std.core.slice.index.Slice.index_mut inst.base s i)

/-- `assert!(c)`: an `if` that panics; the outcome is recorded as a branch. -/
abbrev massert (c : Prop) [Decidable c] : Ct.Leak Unit :=
  Leak.prim [.branch (decide c)] (Aeneas.Std.massert c)

end slhdsa_leak

namespace Ct.Build

/-- The instrumented primitives of this build beyond those of `Ct/Model.lean`. -/
def modelConsts : List Lean.Name :=
  [``slhdsa_leak.core.slice.index.Slice.index_mut, ``slhdsa_leak.massert]

end Ct.Build
