import Cacheops.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
namespace CacheopsRust.cache.parallelSign

/-- Worker call boundary in the parallel-enabled Rust caller. -/
abbrev sha2Worker (N : Std.Usize) :=
  params.Params → Slice Std.U8 → Array Std.U8 N → hash.Seed N →
  address.Adrs → Array Std.U8 N → Std.U64 → Std.U32 → Slice (Array Std.U8 N) →
  Option (Slice (Array Std.U8 N)) → Result (Option (alloc.vec.Vec Std.U8))

/-- Fresh Aeneas caller parameterized over the worker. -/
def sha2Caller
  {N : Std.Usize} (worker : sha2Worker N) (p : params.Params) (sk_seed : Array Std.U8 N)
  (pk_seed : Array Std.U8 N) (r : Array Std.U8 N) (digest : Slice Std.U8)
  (top_tree : Slice (Array Std.U8 N))
  (layer_d2_hit : Option (Slice (Array Std.U8 N))) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let idx_tree ← cache.digest_tree p digest
  let idx_leaf ← cache.digest_leaf p digest
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_tree a idx_tree
  let a2 ← address.Adrs.with_type a1 address.FORS_TREE
  let fors_adrs ← address.Adrs.with_keypair a2 idx_leaf
  let seed ← hash.seed_ctx pk_seed
  let i ← params.Params.md_bytes p
  let md ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) digest { start := 0#usize, «end» := i }
  let o ←
    worker p md sk_seed seed fors_adrs r idx_tree
      idx_leaf top_tree layer_d2_hit
  match o with
  | none =>
    let sig_fors ← fors.fors_sign p md sk_seed seed fors_adrs
    let s := alloc.vec.Vec.deref sig_fors
    let root ← fors.fors_pk_from_sig p s md seed fors_adrs
    let i1 ← params.Params.sig_bytes p
    let sig := alloc.vec.Vec.with_capacity Std.U8 i1
    let s1 ← lift (Array.to_slice r)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s1
    let s2 := alloc.vec.Vec.deref sig_fors
    let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig1 s2
    cache.sha2_ops.sign_from_digest_loop a { start := 0#u32, «end» := p.d }
      p.n p.h p.d p.hp p.a p.k p.m sk_seed top_tree layer_d2_hit seed root sig2
      idx_tree idx_leaf
  | some sig => ok sig

/-- Worker call boundary in the parallel-enabled Rust caller. -/
abbrev shakeWorker (N : Std.Usize) :=
  params.Params → Slice Std.U8 → Array Std.U8 N → Array Std.U8 N →
  address.Adrs → Array Std.U8 N → Std.U64 → Std.U32 → Slice (Array Std.U8 N) →
  Option (Slice (Array Std.U8 N)) → Result (Option (alloc.vec.Vec Std.U8))

/-- Fresh Aeneas caller parameterized over the worker. -/
def shakeCaller
  {N : Std.Usize} (worker : shakeWorker N) (p : params.Params) (sk_seed : Array Std.U8 N)
  (pk_seed : Array Std.U8 N) (r : Array Std.U8 N) (digest : Slice Std.U8)
  (top_tree : Slice (Array Std.U8 N))
  (layer_d2_hit : Option (Slice (Array Std.U8 N))) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let idx_tree ← cache.digest_tree p digest
  let idx_leaf ← cache.digest_leaf p digest
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_tree a idx_tree
  let a2 ← address.Adrs.with_type a1 address.FORS_TREE
  let fors_adrs ← address.Adrs.with_keypair a2 idx_leaf
  let i ← params.Params.md_bytes p
  let md ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) digest { start := 0#usize, «end» := i }
  let o ←
    worker p md sk_seed pk_seed fors_adrs r idx_tree
      idx_leaf top_tree layer_d2_hit
  match o with
  | none =>
    let sig_fors ← cache.shake_ops.fors_sign p md sk_seed pk_seed fors_adrs
    let s := alloc.vec.Vec.deref sig_fors
    let root ← cache.shake_ops.fors_pk_from_sig p s md pk_seed fors_adrs
    let i1 ← params.Params.sig_bytes p
    let sig := alloc.vec.Vec.with_capacity Std.U8 i1
    let s1 ← lift (Array.to_slice r)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s1
    let s2 := alloc.vec.Vec.deref sig_fors
    let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig1 s2
    cache.shake_ops.sign_from_digest_loop a { start := 0#u32, «end» := p.d }
      p.n p.h p.d p.hp p.a p.k p.m sk_seed pk_seed top_tree layer_d2_hit root
      sig2 idx_tree idx_leaf
  | some sig => ok sig

end CacheopsRust.cache.parallelSign
