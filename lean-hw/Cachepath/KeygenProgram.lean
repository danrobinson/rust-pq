import Cachepath.Constructor
open Aeneas Aeneas.Std Result ControlFlow Error
namespace CacheopsRust.cache.generatedKeys

/-- Extracted Rust key generation with selectable tree builders. -/
def keygen
  (N : Std.Usize) (sha2 shake : cache.mutation.Builder N) (family : cache.HashFamily) (p : params.Params)
  (seeds : Slice Std.U8) (sk : Slice Std.U8) (pk : Slice Std.U8) :
  Result ((cache.TopTreeCache N) × (Slice Std.U8) × (Slice Std.U8))
  := do
  if N = p.n
  then
    let left_val := Slice.len seeds
    let i ← 3#usize * N
    let i1 ← lift (Std.Usize.wrapping_mul 3#usize N)
    if left_val = i1
    then
      let left_val1 := Slice.len sk
      let i2 ← 4#usize * N
      let i3 ← lift (Std.Usize.wrapping_mul 4#usize N)
      if left_val1 = i3
      then
        let left_val2 := Slice.len pk
        let i4 ← 2#usize * N
        let i5 ← lift (Std.Usize.wrapping_mul 2#usize N)
        if left_val2 = i5
        then
          let sk_seed ← util.block N seeds 0#usize
          let sk_prf ← util.block N seeds 1#usize
          let pk_seed ← util.block N seeds 2#usize
          let top_tree ←
            match family with
            | cache.HashFamily.Sha2 =>
              do
              let i6 ← p.d - 1#u32
              sha2 p.hp i6 0#u64 sk_seed pk_seed
            | cache.HashFamily.Shake =>
              do
              let i6 ← p.d - 1#u32
              shake p.hp i6 0#u64 sk_seed pk_seed
          let s := alloc.vec.Vec.deref top_tree
          let pk_root ← cache.tree_root s
          let (s1, index_mut_back) ←
            core.slice.index.Slice.index_mut
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk
              { start := 0#usize, «end» := N }
          let s2 ← lift (Array.to_slice sk_seed)
          let s3 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s1 s2
          let sk1 := index_mut_back s3
          let (s4, index_mut_back1) ←
            core.slice.index.Slice.index_mut
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk1
              { start := N, «end» := i4 }
          let s5 ← lift (Array.to_slice sk_prf)
          let s6 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s4 s5
          let sk2 := index_mut_back1 s6
          let (s7, index_mut_back2) ←
            core.slice.index.Slice.index_mut
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk2
              { start := i4, «end» := i }
          let s8 ← lift (Array.to_slice pk_seed)
          let s9 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s7 s8
          let sk3 := index_mut_back2 s9
          let (s10, index_mut_back3) ←
            core.slice.index.Slice.index_mut
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk3
              { start := i, «end» := i2 }
          let s11 ← lift (Array.to_slice pk_root)
          let s12 ←
            core.slice.Slice.copy_from_slice core.marker.CopyU8 s10 s11
          let (s13, index_mut_back4) ←
            core.slice.index.Slice.index_mut
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) pk
              { start := 0#usize, «end» := N }
          let s14 ← lift (Array.to_slice pk_seed)
          let s15 ←
            core.slice.Slice.copy_from_slice core.marker.CopyU8 s13 s14
          let pk1 := index_mut_back4 s15
          let (s16, index_mut_back5) ←
            core.slice.index.Slice.index_mut
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) pk1
              { start := N, «end» := i4 }
          let s17 ← lift (Array.to_slice pk_root)
          let s18 ←
            core.slice.Slice.copy_from_slice core.marker.CopyU8 s16 s17
          let sk4 := index_mut_back3 s12
          let pk2 := index_mut_back5 s18
          ok
            ({
               family,
               hp := p.hp,
               d := p.d,
               pk_seed,
               top_tree,
               layer_d2 := (alloc.vec.Vec.new (cache.LayerD2Entry N)),
               layer_d2_capacity := 0#usize
             }, sk4, pk2)
        else
          let _ ←
            core.fmt.Arguments.from_str (toStr
              "keygen_with_cache: pk must be 2*N bytes")
          fail panic
      else
        let _ ←
          core.fmt.Arguments.from_str (toStr
            "keygen_with_cache: sk must be 4*N bytes")
        fail panic
    else
      let _ ←
        core.fmt.Arguments.from_str (toStr
          "keygen_with_cache: seeds must be 3*N bytes")
      fail panic
  else
    let _ ←
      core.fmt.Arguments.from_str (toStr "keygen_with_cache: N must match p.n")
    fail panic

end CacheopsRust.cache.generatedKeys
