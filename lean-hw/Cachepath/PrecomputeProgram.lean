import Cachepath.BuiltSession
open Aeneas Aeneas.Std Result ControlFlow Error
namespace CacheopsRust.Public

/-- Rust loop body for the exhaustive layer cache. -/
@[rust_loop_body]
def cache.TopTreeCache.precompute_layer_d2_loop.body
  {N : Std.Usize} [b : Builders N] (i : Std.U32) (i1 : Std.U32) (sk_seed : Array Std.U8 N)
  (pk_seed : Array Std.U8 N) (iter : core.ops.range.Range Std.U64)
  (self : cache.TopTreeCache N)
  (entries : alloc.vec.Vec (cache.LayerD2Entry N)) :
  Result (ControlFlow ((core.ops.range.Range Std.U64) × (cache.TopTreeCache N)
    × (alloc.vec.Vec (cache.LayerD2Entry N))) ((cache.TopTreeCache N) ×
    (alloc.vec.Vec (cache.LayerD2Entry N))))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU64 iter
  match o with
  | none => ok (done (self, entries))
  | some tree_idx =>
    let (hf, nodes) ←
      match self.family with
      | cache.HashFamily.Sha2 =>
        do
        let i2 ← i - 2#u32
        let nodes1 ←
          b.sha2 i1 i2 tree_idx sk_seed pk_seed
        ok (cache.HashFamily.Sha2, nodes1)
      | cache.HashFamily.Shake =>
        do
        let i2 ← i - 2#u32
        let nodes1 ←
          b.shake i1 i2 tree_idx sk_seed pk_seed
        ok (cache.HashFamily.Shake, nodes1)
    let entries1 ←
      alloc.vec.Vec.push entries ({ tree_index := tree_idx, nodes } :
        cache.LayerD2Entry N)
    ok (cont (iter1, { self with family := hf }, entries1))

/-- Rust loop for the exhaustive layer cache. -/
@[rust_loop]
def cache.TopTreeCache.precompute_layer_d2_loop
  {N : Std.Usize} [b : Builders N] (iter : core.ops.range.Range Std.U64)
  (self : cache.TopTreeCache N) (i : Std.U32) (i1 : Std.U32)
  (sk_seed : Array Std.U8 N) (pk_seed : Array Std.U8 N)
  (entries : alloc.vec.Vec (cache.LayerD2Entry N)) :
  Result ((cache.TopTreeCache N) × (alloc.vec.Vec (cache.LayerD2Entry N)))
  := do
  loop
    (fun (iter1, self1, entries1) =>
      cache.TopTreeCache.precompute_layer_d2_loop.body i i1 sk_seed pk_seed
      iter1 self1 entries1)
    (iter, self, entries)

/-- Rust entry for the exhaustive layer cache. -/
def cache.TopTreeCache.precompute_layer_d2
  {N : Std.Usize} [b : Builders N] (self : cache.TopTreeCache N) (p : params.Params)
  (sk : Slice Std.U8) :
  Result (cache.TopTreeCache N)
  := do
  cache.TopTreeCache.assert_compatible self p sk
  if p.d < 2#u32
  then ok self
  else
    let sk_seed ← util.block N sk 0#usize
    let pk_seed ← util.block N sk 2#usize
    let count ← 1#u64 <<< p.hp
    let i ← lift (UScalar.cast .Usize count)
    let entries := alloc.vec.Vec.with_capacity (cache.LayerD2Entry N) i
    let (self1, entries1) ←
      cache.TopTreeCache.precompute_layer_d2_loop
        { start := 0#u64, «end» := count } self p.d p.hp sk_seed pk_seed
        entries
    let i1 ← lift (UScalar.cast .Usize count)
    if self1.layer_d2_capacity < i1
    then
      let i2 ← lift (UScalar.cast .Usize count)
      ok { self1 with layer_d2 := entries1, layer_d2_capacity := i2 }
    else ok { self1 with layer_d2 := entries1 }

end CacheopsRust.Public
