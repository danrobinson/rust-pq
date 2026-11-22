import Ct.Do

/-!
# The leakage model: instrumented primitives

`Ct/Funs.lean` is the text of `Slhdsa/Funs.lean` (unchanged except for its header) placed in the
namespace `slhdsa_leak`. Inside that namespace, Lean resolves a name `X` to `slhdsa_leak.X`
before it looks at opened namespaces (`Aeneas.Std`, `Aeneas.Std.Result`, …). The definitions
below therefore *shadow* the corresponding Aeneas names for the generated text, and the same
text elaborates to the instrumented program. (`Ct/Check.lean` verifies, on the elaborated terms,
that every Aeneas constant left in the instrumented definitions is on an explicit whitelist of
non-leaking operations, so a name that is not shadowed cannot silently drop events.)

This file is the trusted leakage table. Every leaking primitive is the Aeneas primitive itself,
run through `Ct.Leak.prim events`, so erasure is immediate and the events are visibly the
arguments of the call:

| text                                   | event emitted                                  |
|----------------------------------------|------------------------------------------------|
| `if c then … else …` (`do`-level)      | `branch (decide c)` (via `Ct/Do.lean`)         |
| `Array.index_usize a i`                | `index i n` (`n` the array length)             |
| `Array.update a i x`                   | `index i n`                                    |
| `Array.index_mut_usize a i`            | `index i n`                                    |
| `Slice.index_usize s i`                | `index i s.length`                             |
| `Slice.update s i x`                   | `index i s.length`                             |
| `Slice.index_mut_usize s i`            | `index i s.length`                             |
| `core.array.Array.index inst a r`      | `inst`'s event (`range`/`index`) on `a`        |
| `core.array.Array.index_mut inst a r`  | `inst`'s event on `a`                          |
| `core.slice.index.Slice.index inst s r`| `inst`'s event on `s`                          |
| `alloc.vec.Vec.index inst v i`         | `inst`'s event on `v`                          |
|   with `SliceIndexRangeUsizeSlice`     | `range r.start r.end len`                      |
|   with `SliceIndexUsizeSlice`          | `index i len`                                  |
| `core.slice.Slice.copy_from_slice _ d s` | `copy d.length s.length`                     |
| `alloc.vec.Vec.extend_from_slice _ v s`| `extend v.length s.length`                     |
| `alloc.vec.Vec.push v x`               | `extend v.length 1`                            |
| `core.array.equality.PartialEqArray.eq _ a b` | `cmp (commonPrefix a b) n`  |
| `x / y` on `UScalar`                   | `div x.val y.val`                              |
| `x % y` on `UScalar`                   | `rem x.val y.val`                              |

Non-leaking plumbing: `Result` is `Ct.Leak`, `ok` is `Ct.Leak.pure`, `lift` is `Ct.Leak.pure`,
`loop` is `Ct.Leak.loop`; other `Result`-valued operations (checked `+ - *`, shifts) are lifted
by Lean's automatic monad lift `MonadLift Result Leak`, which emits nothing (and still fails on
overflow, as before). The trait-dictionary types `core.clone.Clone` and `core.marker.Copy` are
redefined with `Leak`-valued methods (they only occur in the two `Clone`/`Copy` instances of the
crate, which are never called).
-/

open Aeneas Aeneas.Std

set_option linter.dupNamespace false

namespace Ct

/-- An instrumented `SliceIndex` dictionary: Aeneas's dictionary and the events of an access. -/
structure LSliceIndex (I T Output : Type _) where
  base : Aeneas.Std.core.slice.index.SliceIndex I T Output
  ev : I → T → Trace

/-- An instrumented `Index` dictionary. -/
structure LIndex (Self I Output : Type _) where
  base : Aeneas.Std.core.ops.index.Index Self I Output
  ev : Self → I → Trace

/-- An instrumented `IndexMut` dictionary. -/
structure LIndexMut (Self I Output : Type _) where
  base : Aeneas.Std.core.ops.index.IndexMut Self I Output
  ev : Self → I → Trace

end Ct

namespace slhdsa_leak

open Ct

/-! ## Plumbing -/

/-- In the instrumented text, `Result` is the leakage monad. -/
abbrev Result (α : Type u) : Type u := Ct.Leak α

/-- `ok` returns without emitting. -/
abbrev ok {α : Type u} (a : α) : Ct.Leak α := Ct.Leak.pure a

/-- `lift` wraps a pure (total) operation; it emits nothing. -/
abbrev lift {α : Type u} (a : α) : Ct.Leak α := Ct.Leak.pure a

/-- Loops. -/
abbrev loop {α : Type u} {β : Type v} (body : α → Ct.Leak (ControlFlow α β)) (x : α) :
    Ct.Leak β :=
  Ct.Leak.loop body x

/-! ## Element accesses -/

abbrev Array.index_usize {α : Type u} {n : Usize} (v : Aeneas.Std.Array α n) (i : Usize) :
    Ct.Leak α :=
  Leak.prim [.index i.val n.val] (Aeneas.Std.Array.index_usize v i)

abbrev Array.update {α : Type u} {n : Usize} (v : Aeneas.Std.Array α n) (i : Usize) (x : α) :
    Ct.Leak (Aeneas.Std.Array α n) :=
  Leak.prim [.index i.val n.val] (Aeneas.Std.Array.update v i x)

abbrev Array.index_mut_usize {α : Type u} {n : Usize} (v : Aeneas.Std.Array α n) (i : Usize) :
    Ct.Leak (α × (α → Aeneas.Std.Array α n)) :=
  Leak.prim [.index i.val n.val] (Aeneas.Std.Array.index_mut_usize v i)

abbrev Slice.index_usize {α : Type u} (s : Aeneas.Std.Slice α) (i : Usize) : Ct.Leak α :=
  Leak.prim [.index i.val s.length] (Aeneas.Std.Slice.index_usize s i)

abbrev Slice.update {α : Type u} (s : Aeneas.Std.Slice α) (i : Usize) (x : α) :
    Ct.Leak (Aeneas.Std.Slice α) :=
  Leak.prim [.index i.val s.length] (Aeneas.Std.Slice.update s i x)

abbrev Slice.index_mut_usize {α : Type u} (s : Aeneas.Std.Slice α) (i : Usize) :
    Ct.Leak (α × (α → Aeneas.Std.Slice α)) :=
  Leak.prim [.index i.val s.length] (Aeneas.Std.Slice.index_mut_usize s i)

/-! ## Indexing through trait dictionaries (ranges and `usize` indices) -/

/-- `s[r.start..r.end]`: emits the range and the length of the sliced container. -/
abbrev core.slice.index.SliceIndexRangeUsizeSlice (T : Type _) :
    LSliceIndex (core.ops.range.Range Usize) (Aeneas.Std.Slice T) (Aeneas.Std.Slice T) where
  base := Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice T
  ev r s := [.range r.start.val r.end.val s.length]

/-- `s[i]`: emits the index and the length. -/
abbrev core.slice.index.SliceIndexUsizeSlice (T : Type _) :
    LSliceIndex Usize (Aeneas.Std.Slice T) T where
  base := Aeneas.Std.core.slice.index.SliceIndexUsizeSlice T
  ev i s := [.index i.val s.length]

abbrev core.ops.index.IndexSlice {T I Output : Type _}
    (inst : LSliceIndex I (Aeneas.Std.Slice T) Output) :
    LIndex (Aeneas.Std.Slice T) I Output where
  base := Aeneas.Std.core.ops.index.IndexSlice inst.base
  ev s i := inst.ev i s

abbrev core.ops.index.IndexMutSlice {T I Output : Type _}
    (inst : LSliceIndex I (Aeneas.Std.Slice T) Output) :
    LIndexMut (Aeneas.Std.Slice T) I Output where
  base := Aeneas.Std.core.ops.index.IndexMutSlice inst.base
  ev s i := inst.ev i s

abbrev core.array.Array.index {T I Output : Type _} {N : Usize}
    (inst : LIndex (Aeneas.Std.Slice T) I Output) (a : Aeneas.Std.Array T N) (i : I) :
    Ct.Leak Output :=
  Leak.prim (inst.ev a.to_slice i) (Aeneas.Std.core.array.Array.index inst.base a i)

abbrev core.array.Array.index_mut {T I Output : Type _} {N : Usize}
    (inst : LIndexMut (Aeneas.Std.Slice T) I Output) (a : Aeneas.Std.Array T N) (i : I) :
    Ct.Leak (Output × (Output → Aeneas.Std.Array T N)) :=
  Leak.prim (inst.ev a.to_slice i) (Aeneas.Std.core.array.Array.index_mut inst.base a i)

abbrev core.slice.index.Slice.index {T I Output : Type _}
    (inst : LSliceIndex I (Aeneas.Std.Slice T) Output) (s : Aeneas.Std.Slice T) (i : I) :
    Ct.Leak Output :=
  Leak.prim (inst.ev i s) (Aeneas.Std.core.slice.index.Slice.index inst.base s i)

abbrev alloc.vec.Vec.index {T I Output : Type _}
    (inst : LSliceIndex I (Aeneas.Std.Slice T) Output) (v : Aeneas.Std.alloc.vec.Vec T) (i : I) :
    Ct.Leak Output :=
  Leak.prim (inst.ev i (Aeneas.Std.alloc.vec.Vec.deref v))
    (Aeneas.Std.alloc.vec.Vec.index inst.base v i)

/-! ## Copies and vector growth -/

abbrev core.slice.Slice.copy_from_slice {T : Type _} (c : Aeneas.Std.core.marker.Copy T)
    (s : Aeneas.Std.Slice T) (src : Aeneas.Std.Slice T) : Ct.Leak (Aeneas.Std.Slice T) :=
  Leak.prim [.copy s.length src.length] (Aeneas.Std.core.slice.Slice.copy_from_slice c s src)

abbrev alloc.vec.Vec.extend_from_slice {T : Type _} (c : Aeneas.Std.core.clone.Clone T)
    (v : Aeneas.Std.alloc.vec.Vec T) (s : Aeneas.Std.Slice T) :
    Ct.Leak (Aeneas.Std.alloc.vec.Vec T) :=
  Leak.prim [.extend v.length s.length] (Aeneas.Std.alloc.vec.Vec.extend_from_slice c v s)

abbrev alloc.vec.Vec.push {T : Type _} (v : Aeneas.Std.alloc.vec.Vec T) (x : T) :
    Ct.Leak (Aeneas.Std.alloc.vec.Vec T) :=
  Leak.prim [.extend v.length 1] (Aeneas.Std.alloc.vec.Vec.push v x)

/-! ## Comparison of arrays

Rust's `==` on arrays may stop at the first difference, so it leaks the length of the common
prefix. (Only used in `ht_verify`, on public data.) -/

abbrev core.array.equality.PartialEqArray.eq {T : Type _} [DecidableEq T] {N : Usize}
    (inst : Aeneas.Std.core.cmp.PartialEq T T) (a0 a1 : Aeneas.Std.Array T N) : Ct.Leak Bool :=
  Leak.prim [.cmp (commonPrefix a0.val a1.val) N.val]
    (Aeneas.Std.core.array.equality.PartialEqArray.eq inst a0 a1)

/-! ## Division and remainder

The infix operators elaborate through `HDiv`/`HMod`, whose output type is an `outParam`; these
scoped instances (active inside `namespace slhdsa_leak`) have higher priority than Aeneas's
`Result`-valued ones, so `x / y` and `x % y` in the generated text elaborate to the leaking
versions. -/

abbrev UScalar.div_leak {ty : UScalarTy} (x y : UScalar ty) : Ct.Leak (UScalar ty) :=
  Leak.prim [.div x.val y.val] (Aeneas.Std.UScalar.div x y)

abbrev UScalar.rem_leak {ty : UScalarTy} (x y : UScalar ty) : Ct.Leak (UScalar ty) :=
  Leak.prim [.rem x.val y.val] (Aeneas.Std.UScalar.rem x y)

scoped instance (priority := high) instHDivUScalarLeak {ty : UScalarTy} :
    HDiv (UScalar ty) (UScalar ty) (Ct.Leak (UScalar ty)) where
  hDiv := UScalar.div_leak

scoped instance (priority := high) instHModUScalarLeak {ty : UScalarTy} :
    HMod (UScalar ty) (UScalar ty) (Ct.Leak (UScalar ty)) where
  hMod := UScalar.rem_leak

/-! ## Trait dictionaries with methods -/

/-- `Clone`, with a `Leak`-valued method. -/
structure core.clone.Clone (Self : Type _) where
  clone : Self → Ct.Leak Self
  clone_from : Self → Self → Ct.Leak Self := fun _ => clone

/-- `Copy`. -/
structure core.marker.Copy (Self : Type _) where
  cloneInst : core.clone.Clone Self

/-- Erasure of an instrumented `Clone` dictionary. -/
def core.clone.Clone.erase {Self : Type _} (c : core.clone.Clone Self) :
    Aeneas.Std.core.clone.Clone Self where
  clone x := (c.clone x).erase
  clone_from x y := (c.clone_from x y).erase

/-- Erasure of an instrumented `Copy` dictionary. -/
def core.marker.Copy.erase {Self : Type _} (c : core.marker.Copy Self) :
    Aeneas.Std.core.marker.Copy Self where
  cloneInst := c.cloneInst.erase

end slhdsa_leak
