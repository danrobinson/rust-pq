module
public import Aeneas
public import Cacheops.Types
public import Cachepath.Funs
public import Cachesearch.Funs
public import Slhdsa.Funs
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false

/-- Rust `Vec::truncate`: keeps at most `len` elements without reallocation. -/
@[reducible]
def alloc.vec.Vec.truncate {T : Type _} (_A : Type _)
    (v : alloc.vec.Vec T) (len : Std.Usize) : Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.from (v.val.take len.val) (by simp [v.property]))

/-- Rust `Vec::as_slice`: views the vector's backing buffer as a slice. -/
@[reducible]
def alloc.vec.Vec.as_slice {T : Type _} (_A : Type _)
    (v : alloc.vec.Vec T) : Result (Slice T) :=
  ok (alloc.vec.Vec.deref v)

namespace CacheopsRust

@[reducible]
def toSlhParams (p : params.Params) : slhdsa.params.Params :=
  ⟨p.n, p.h, p.d, p.hp, p.a, p.k, p.m⟩

@[reducible]
def toSlhAdrs (a : address.Adrs) : slhdsa.address.Adrs :=
  ⟨a.layer, a.tree, a.typ, a.keypair, a.word2, a.word3⟩

@[reducible]
def toSlhSeed {N : Std.Usize} (s : hash.Seed N) : slhdsa.hash.Seed N :=
  ⟨s.pk_seed, s.state, s.state512⟩

@[reducible]
def fromSlhSeed {N : Std.Usize} (s : slhdsa.hash.Seed N) : hash.Seed N :=
  ⟨s.pk_seed, s.state, s.state512⟩

@[reducible]
def toSearchEntry {N : Std.Usize} (e : cache.LayerD2Entry N) : slhdsa.cache.LayerD2Entry N :=
  ⟨e.tree_index, e.nodes⟩

@[reducible]
def toSearchSlice {N : Std.Usize} (entries : Slice (cache.LayerD2Entry N)) :
    Slice (slhdsa.cache.LayerD2Entry N) :=
  Slice.from (entries.val.map toSearchEntry) (by simp [entries.property])

@[reducible]
def cache.append_auth_path {N : Std.Usize} (tree : Slice (Array Std.U8 N))
    (hp leaf : Std.U32) (out : alloc.vec.Vec Std.U8) : Result (alloc.vec.Vec Std.U8) :=
  slhdsa.cache.append_auth_path tree hp leaf out

@[reducible]
def cache.tree_root {N : Std.Usize} (tree : Slice (Array Std.U8 N)) : Result (Array Std.U8 N) :=
  slhdsa.cache.tree_root tree

@[reducible]
def cache.lookup_cached_index {N : Std.Usize} (entries : Slice (cache.LayerD2Entry N))
    (tree_index : Std.U64) : Result (Option Std.Usize) :=
  slhdsa.cache.lookup_cached_index (toSearchSlice entries) tree_index

@[reducible]
def hash.seed_ctx {N : Std.Usize} (pk_seed : Array Std.U8 N) : Result (hash.Seed N) := do
  let s ← slhdsa.hash.seed_ctx pk_seed
  ok (fromSlhSeed s)

@[reducible]
def xmss.xmss_pk_from_sig {N : Std.Usize} (p : params.Params) (idx : Std.U32)
    (sig : Slice Std.U8) (m : Array Std.U8 N) (seed : hash.Seed N) (a : address.Adrs) :
    Result (Array Std.U8 N) :=
  slhdsa.xmss.xmss_pk_from_sig (toSlhParams p) idx sig m (toSlhSeed seed) (toSlhAdrs a)

@[reducible]
def xmss.xmss_sign {N : Std.Usize} (p : params.Params) (m : Array Std.U8 N)
    (sk_seed : Array Std.U8 N) (idx : Std.U32) (seed : hash.Seed N) (a : address.Adrs) :
    Result (alloc.vec.Vec Std.U8) :=
  slhdsa.xmss.xmss_sign (toSlhParams p) m sk_seed idx (toSlhSeed seed) (toSlhAdrs a)

@[reducible]
def wots.wots_sign {N : Std.Usize} (m : Array Std.U8 N) (sk_seed : Array Std.U8 N)
    (seed : hash.Seed N) (a : address.Adrs) : Result (alloc.vec.Vec Std.U8) :=
  slhdsa.wots.wots_sign m sk_seed (toSlhSeed seed) (toSlhAdrs a)

@[reducible]
def fors.fors_pk_from_sig {N : Std.Usize} (p : params.Params) (sig md : Slice Std.U8)
    (seed : hash.Seed N) (a : address.Adrs) : Result (Array Std.U8 N) :=
  slhdsa.fors.fors_pk_from_sig (toSlhParams p) sig md (toSlhSeed seed) (toSlhAdrs a)

@[reducible]
def fors.fors_sign {N : Std.Usize} (p : params.Params) (md : Slice Std.U8)
    (sk_seed : Array Std.U8 N) (seed : hash.Seed N) (a : address.Adrs) :
    Result (alloc.vec.Vec Std.U8) :=
  slhdsa.fors.fors_sign (toSlhParams p) md sk_seed (toSlhSeed seed) (toSlhAdrs a)

/-! Functional models for the cache SHAKE calls at the extraction boundary. -/
abbrev shake256.Sponge.new := slhdsa.shake256.Sponge.new
abbrev shake256.Sponge.absorb := slhdsa.shake256.Sponge.absorb
abbrev shake256.Sponge.finish := slhdsa.shake256.Sponge.finish

@[reducible]
def cache.shake_ops.xmss_node {N : Std.Usize} (sk : Array Std.U8 N) (i z : Std.U32)
    (seed : Array Std.U8 N) (a : address.Adrs) := slhdsa.shake.xmss.xmss_node sk i z seed (toSlhAdrs a)

@[reducible]
def cache.shake_ops.wots_pk_from_sig {N : Std.Usize} (sig : Slice Std.U8)
    (m seed : Array Std.U8 N) (a : address.Adrs) := slhdsa.shake.wots.wots_pk_from_sig sig m seed (toSlhAdrs a)

@[reducible]
def cache.shake_ops.wots_sign {N : Std.Usize} (m : Array Std.U8 N) (sk_seed : Array Std.U8 N)
    (seed : Array Std.U8 N) (a : address.Adrs) : Result (alloc.vec.Vec Std.U8) :=
  slhdsa.shake.wots.wots_sign m sk_seed seed (toSlhAdrs a)

@[reducible]
def cache.shake_ops.fors_pk_from_sig {N : Std.Usize} (p : params.Params) (sig md : Slice Std.U8)
    (seed : Array Std.U8 N) (a : address.Adrs) : Result (Array Std.U8 N) :=
  slhdsa.shake.fors.fors_pk_from_sig (toSlhParams p) sig md seed (toSlhAdrs a)

@[reducible]
def cache.shake_ops.fors_sign {N : Std.Usize} (p : params.Params) (md : Slice Std.U8)
    (sk_seed : Array Std.U8 N) (seed : Array Std.U8 N) (a : address.Adrs) :
    Result (alloc.vec.Vec Std.U8) :=
  slhdsa.shake.fors.fors_sign (toSlhParams p) md sk_seed seed (toSlhAdrs a)

end CacheopsRust
