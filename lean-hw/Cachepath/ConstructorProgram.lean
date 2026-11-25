import Cachepath.Mutation

open Aeneas Aeneas.Std Result ControlFlow Error
namespace CacheopsRust.cache.constructor

/-- Translation of the public Rust constructor with parameters for the two tree builders. -/
def newCache
  (N : Std.Usize) (sha2 shake : cache.mutation.Builder N) (family : cache.HashFamily) (p : params.Params)
  (sk : Slice Std.U8) :
  Result (cache.TopTreeCache N)
  := do
  if N = p.n
  then
    let left_val := Slice.len sk
    let _ ← 4#usize * N
    let i ← lift (Std.Usize.wrapping_mul 4#usize N)
    if left_val = i
    then
      let sk_seed ← util.block N sk 0#usize
      let pk_seed ← util.block N sk 2#usize
      let pk_root ← util.block N sk 3#usize
      let top_tree ←
        match family with
        | cache.HashFamily.Sha2 =>
          do
          let i1 ← p.d - 1#u32
          sha2 p.hp i1 0#u64 sk_seed pk_seed
        | cache.HashFamily.Shake =>
          do
          let i1 ← p.d - 1#u32
          shake p.hp i1 0#u64 sk_seed pk_seed
      let s := alloc.vec.Vec.deref top_tree
      let left_val1 ← cache.tree_root s
      let b ←
        core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 left_val1
          pk_root
      if b
      then
        ok
          {
            family,
            hp := p.hp,
            d := p.d,
            pk_seed,
            top_tree,
            layer_d2 := (alloc.vec.Vec.new (cache.LayerD2Entry N)),
            layer_d2_capacity := 0#usize
          }
      else
        let _ ←
          core.fmt.Arguments.from_str (toStr
            "TopTreeCache: secret key PK.root does not match computed top-tree root")
        fail panic
    else
      let _ ←
        core.fmt.Arguments.from_str (toStr
          "TopTreeCache: secret key must be 4*N bytes")
      fail panic
  else
    let _ ←
      core.fmt.Arguments.from_str (toStr "TopTreeCache: N must match p.n")
    fail panic

end CacheopsRust.cache.constructor
