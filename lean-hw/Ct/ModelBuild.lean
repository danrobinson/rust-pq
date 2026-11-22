import Ct.Model
import Slhdsa.FunsExternal

/-!
# The leakage model, build-specific part: the six-set crate built with `hw-sha2` (TRUSTED)

The union of two existing tables, nothing new:

* the eighteen intrinsic wrappers of `sha256::hw::arm`, the `Clone` of `uint32x4_t` and
  `massert`: the single-set tree's `lean-hw/Ct/ModelBuild.lean` (git `26aa3d8`), COPIED (not linked, because
  both files define `Ct.Build.modelConsts`) with every definition and event unchanged. This
  tree's `hw-sha2` translation calls the same eighteen wrappers, defined by the same
  `Slhdsa/FunsExternal.lean` (the single-set tree's file, unchanged); the kernel
  generic in `N` uses no other wrapper. `diff` against the single-set tree's file shows, below the
  documentation, only the added `Slice.index_mut` block and its entry in `modelConsts`;
* `core.slice.index.Slice.index_mut`: this tree's portable `../lean/Ct/ModelBuild.lean`,
  copied unchanged (mutable sub-slices of slices emit the range, as `Slice.index`).

The single-set tree's description of the wrappers' events, quoted:

| wrapper                                      | event emitted                                   |
|----------------------------------------------|-------------------------------------------------|
| `available`                                  | none                                            |
| `zero`, `pair`, `add`, `or`, `and`, `shr16`, `shl16`, `ext2`, `ext3`, `sha256h`, `sha256h2`, `sha256su0`, `sha256su1`, `store_words` | none (see the assumption below) |
| `load_words w at`                            | `range at (at + 4) w.length`                    |
| `load_be b at`                               | `range at (at + 16) b.length`                   |
| `store_be b at v`                            | `range at (at + 16) b.length`                   |
| `uint32x4_t`'s `clone`                       | none                                            |
| `massert c` (Aeneas's `assert!`)             | `branch (decide c)`                             |
| `core.slice.index.Slice.index_mut inst s r`  | `inst`'s event on `s` (`range`/`index`)         |

* `available` (`is_aarch64_feature_detected!`) emits nothing of its own. The `if` on its result
  is recorded as a branch like any other `if` of the program: whether the processor has the
  instructions is public.
* **Assumption about the processor.** The register-only wrappers, and `store_words` (which
  writes the two vectors into an array of its own, at fixed positions), emit nothing. These are
  fixed-latency vector instructions (`DUP`, `INS`, `ADD`, `ORR`, `AND`, `USHR`, `SHL`, `EXT`,
  `SHA256H`, `SHA256H2`, `SHA256SU0`, `SHA256SU1`, `ST1`), which Arm lists as data-independent
  in time when the data-independent-timing mode (`PSTATE.DIT`) is on. The crate does not set
  that mode itself; the application has to.
* The memory accesses `load_words`, `load_be` and `store_be` emit the range they touch and the
  length of the slice, as a sub-slice does in `Ct/Model.lean`.
* A run that fails (out of bounds, or an instruction without the feature: every wrapper but
  `available` is `fail .undef` when `Arm.haveSha2 = false`) has no trace, as elsewhere in the
  library: `Leak.prim` of a failing computation fails.
* `massert` is Aeneas's translation of `assert!`, an `if` that panics, and is recorded as a
  branch.

`Ct/Check.lean` accepts exactly the names of `Ct.Build.modelConsts` below in addition to the
model of `Ct/Model.lean`; in particular the un-instrumented `slhdsa.sha256.hw.arm.*` and
`Aeneas.Std.core.slice.index.Slice.index_mut` are rejected (`Ct/CheckTestBuild.lean`).
-/

open Aeneas Aeneas.Std

set_option linter.dupNamespace false

namespace slhdsa_leak

open Ct

/-- The vector type of the wrappers. -/
abbrev V := core.core_arch.arm_shared.neon.uint32x4_t

/-! ## The feature test -/

abbrev sha256.hw.arm.available : Ct.Leak Bool :=
  Leak.prim [] slhdsa.sha256.hw.arm.available

/-! ## Register-only wrappers (no event: assumption about the processor, see above) -/

abbrev sha256.hw.arm.zero : Ct.Leak V :=
  Leak.prim [] slhdsa.sha256.hw.arm.zero

abbrev sha256.hw.arm.pair (a b : U32) : Ct.Leak V :=
  Leak.prim [] (slhdsa.sha256.hw.arm.pair a b)

abbrev sha256.hw.arm.add (a b : V) : Ct.Leak V :=
  Leak.prim [] (slhdsa.sha256.hw.arm.add a b)

abbrev sha256.hw.arm.or (a b : V) : Ct.Leak V :=
  Leak.prim [] (slhdsa.sha256.hw.arm.or a b)

abbrev sha256.hw.arm.and (a b : V) : Ct.Leak V :=
  Leak.prim [] (slhdsa.sha256.hw.arm.and a b)

abbrev sha256.hw.arm.shr16 (a : V) : Ct.Leak V :=
  Leak.prim [] (slhdsa.sha256.hw.arm.shr16 a)

abbrev sha256.hw.arm.shl16 (a : V) : Ct.Leak V :=
  Leak.prim [] (slhdsa.sha256.hw.arm.shl16 a)

abbrev sha256.hw.arm.ext2 (a b : V) : Ct.Leak V :=
  Leak.prim [] (slhdsa.sha256.hw.arm.ext2 a b)

abbrev sha256.hw.arm.ext3 (a b : V) : Ct.Leak V :=
  Leak.prim [] (slhdsa.sha256.hw.arm.ext3 a b)

abbrev sha256.hw.arm.sha256h (abcd efgh wk : V) : Ct.Leak V :=
  Leak.prim [] (slhdsa.sha256.hw.arm.sha256h abcd efgh wk)

abbrev sha256.hw.arm.sha256h2 (efgh abcd wk : V) : Ct.Leak V :=
  Leak.prim [] (slhdsa.sha256.hw.arm.sha256h2 efgh abcd wk)

abbrev sha256.hw.arm.sha256su0 (w0_3 w4_7 : V) : Ct.Leak V :=
  Leak.prim [] (slhdsa.sha256.hw.arm.sha256su0 w0_3 w4_7)

abbrev sha256.hw.arm.sha256su1 (tw0_3 w8_11 w12_15 : V) : Ct.Leak V :=
  Leak.prim [] (slhdsa.sha256.hw.arm.sha256su1 tw0_3 w8_11 w12_15)

/-- Writes an array of its own (fixed positions): no event. -/
abbrev sha256.hw.arm.store_words (a e : V) : Ct.Leak (Aeneas.Std.Array U32 8#usize) :=
  Leak.prim [] (slhdsa.sha256.hw.arm.store_words a e)

/-! ## Memory accesses -/

abbrev sha256.hw.arm.load_words (w : Aeneas.Std.Slice U32) (at' : Usize) : Ct.Leak V :=
  Leak.prim [.range at'.val (at'.val + 4) w.length] (slhdsa.sha256.hw.arm.load_words w at')

abbrev sha256.hw.arm.load_be (b : Aeneas.Std.Slice U8) (at' : Usize) : Ct.Leak V :=
  Leak.prim [.range at'.val (at'.val + 16) b.length] (slhdsa.sha256.hw.arm.load_be b at')

abbrev sha256.hw.arm.store_be (b : Aeneas.Std.Slice U8) (at' : Usize) (v : V) :
    Ct.Leak (Aeneas.Std.Slice U8) :=
  Leak.prim [.range at'.val (at'.val + 16) b.length] (slhdsa.sha256.hw.arm.store_be b at' v)

/-! ## `Clone` of the vector type, and `assert!` -/

abbrev core.core_arch.arm_shared.neon.uint32x4_t.Insts.CoreCloneClone.clone (v : V) :
    Ct.Leak V :=
  Leak.prim [] (slhdsa.core.core_arch.arm_shared.neon.uint32x4_t.Insts.CoreCloneClone.clone v)

/-- `assert!(c)`: an `if` that panics; the outcome is recorded as a branch. -/
abbrev massert (c : Prop) [Decidable c] : Ct.Leak Unit :=
  Leak.prim [.branch (decide c)] (Aeneas.Std.massert c)

/-! ## Mutable sub-slices of slices (this tree's portable `Ct/ModelBuild.lean`, unchanged) -/

abbrev core.slice.index.Slice.index_mut {T I Output : Type _}
    (inst : LSliceIndex I (Aeneas.Std.Slice T) Output) (s : Aeneas.Std.Slice T) (i : I) :
    Ct.Leak (Output × (Output → Aeneas.Std.Slice T)) :=
  Leak.prim (inst.ev i s) (Aeneas.Std.core.slice.index.Slice.index_mut inst.base s i)

end slhdsa_leak

namespace Ct.Build

/-- The instrumented primitives of this build beyond those of `Ct/Model.lean`. -/
def modelConsts : List Lean.Name := [
  ``slhdsa_leak.sha256.hw.arm.available,
  ``slhdsa_leak.sha256.hw.arm.zero, ``slhdsa_leak.sha256.hw.arm.pair,
  ``slhdsa_leak.sha256.hw.arm.add, ``slhdsa_leak.sha256.hw.arm.or,
  ``slhdsa_leak.sha256.hw.arm.and, ``slhdsa_leak.sha256.hw.arm.shr16,
  ``slhdsa_leak.sha256.hw.arm.shl16, ``slhdsa_leak.sha256.hw.arm.ext2,
  ``slhdsa_leak.sha256.hw.arm.ext3, ``slhdsa_leak.sha256.hw.arm.sha256h,
  ``slhdsa_leak.sha256.hw.arm.sha256h2, ``slhdsa_leak.sha256.hw.arm.sha256su0,
  ``slhdsa_leak.sha256.hw.arm.sha256su1, ``slhdsa_leak.sha256.hw.arm.store_words,
  ``slhdsa_leak.sha256.hw.arm.load_words, ``slhdsa_leak.sha256.hw.arm.load_be,
  ``slhdsa_leak.sha256.hw.arm.store_be,
  ``slhdsa_leak.core.core_arch.arm_shared.neon.uint32x4_t.Insts.CoreCloneClone.clone,
  ``slhdsa_leak.massert,
  ``slhdsa_leak.core.slice.index.Slice.index_mut
]

end Ct.Build
