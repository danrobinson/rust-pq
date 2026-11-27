import Cacheops.FunsExternal

open Aeneas Aeneas.Std Result
namespace CacheopsRust.cache.mutation

abbrev Builder (N : Usize) := U32 → U32 → U64 → Array U8 N → Array U8 N →
  Result (alloc.vec.Vec (Array U8 N))

/-- Models the three Rust standard-library operations on owned vector entries.
The bundled Aeneas insert model rejects insertion at len; Rust permits it. -/
def insert {T} (v : alloc.vec.Vec T) (i : Usize) (e : T) : Result (alloc.vec.Vec T) :=
  if i.val ≤ v.length then
    if h : v.val.length < Usize.max then
      ok (.from (v.val.insertIdx i.val e) (List.length_insertIdx_le_succ.trans h))
    else fail .maximumSizeExceeded
  else fail .arrayOutOfBounds

def remove {T} (_ : Type) (v : alloc.vec.Vec T) (i : Usize) : Result (T × alloc.vec.Vec T) :=
  if h : i.val < v.val.length then
    ok (v.val[i.val], .from (v.val.eraseIdx i.val) (by
      rw [List.length_eraseIdx_of_lt h]; have := v.property; omega))
  else fail .arrayOutOfBounds

def pop {T} (_ : Type) (v : alloc.vec.Vec T) : Result (Option T × alloc.vec.Vec T) :=
  ok (v.val.getLast?, .from v.val.dropLast (Nat.le_trans (by simp) v.property))

def find {N : Usize} (entries : Slice (LayerD2Entry N)) (target : U64) :=
  slhdsa.cache.find_cached_index (toSearchSlice entries) target

end CacheopsRust.cache.mutation
