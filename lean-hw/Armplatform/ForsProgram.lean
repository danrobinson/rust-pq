import Armplatform.Parents
open Aeneas Aeneas.Std Result ControlFlow Error
open slhdsa
namespace slhdsa.PlatformFors.Program
@[rust_loop_body]
def fors.fors_batch_loop3.body (target : Target)
  {N : Std.Usize} (i : Std.U32) (z : Std.U32) (a : Array Std.U8 N)
  (a1 : Array Std.U32 8#usize) (a2 : Array Std.U64 8#usize) (i1 : Std.U32)
  (i2 : Std.U64) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (i6 : Std.U32)
  (blocks : Array (Array Std.U8 64#usize) 128#usize)
  (start : Array Std.U32 128#usize) («end» : Array Std.U32 128#usize)
  (vals : Array (Array Std.U8 N) 128#usize) (lvl : Std.U32) (cnt : Std.Usize) :
  Result (ControlFlow ((Array (Array Std.U8 64#usize) 128#usize) × (Array
    Std.U32 128#usize) × (Array Std.U32 128#usize) × (Array (Array Std.U8 N)
    128#usize) × Std.U32 × Std.Usize) (Array (Array Std.U8 N) 128#usize))
  := do
  if lvl <= z
  then
    if N = 16#usize
    then
      let (blocks1, start1, end1) ←
        fors.fors_batch_loop3_loop0 i z i1 i2 i3 i4 i5 i6 blocks start «end»
          vals lvl cnt 0#usize
      let (s, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
          blocks1 { start := 0#usize, «end» := cnt }
      let s1 ← lift (Array.to_slice start1)
      let s2 ← lift (Array.to_slice end1)
      let s3 ← hash.chain_blocks N a1 s s1 s2
      let blocks2 := index_mut_back s3
      let vals1 ← fors.fors_batch_loop3_loop1 blocks2 vals cnt 0#usize
      let cnt1 ← cnt / 2#usize
      let lvl1 ← lvl + 1#u32
      ok (cont (blocks2, start1, end1, vals1, lvl1, cnt1))
    else
      let a3 ←
        address.Adrs.with_word2
          {
            layer := i1,
            tree := i2,
            typ := i3,
            keypair := i4,
            word2 := i5,
            word3 := i6
          } lvl
      let i7 ← z - lvl
      let i8 ← i <<< i7
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut vals)
      let (j, s1) ← parents target a2 a3 i8 s cnt
      let vals1 := to_slice_mut_back s1
      let vals2 ←
        fors.fors_batch_loop3_loop2 i z a a1 a2 i1 i2 i3 i4 i5 i6 vals1 lvl cnt
          j
      let cnt1 ← cnt / 2#usize
      let lvl1 ← lvl + 1#u32
      ok (cont (blocks, start, «end», vals2, lvl1, cnt1))
  else ok (done vals)

@[rust_loop]
def fors.fors_batch_loop3 (target : Target)
  {N : Std.Usize} (i : Std.U32) (z : Std.U32) (a : Array Std.U8 N)
  (a1 : Array Std.U32 8#usize) (a2 : Array Std.U64 8#usize) (i1 : Std.U32)
  (i2 : Std.U64) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (i6 : Std.U32)
  (blocks : Array (Array Std.U8 64#usize) 128#usize)
  (start : Array Std.U32 128#usize) («end» : Array Std.U32 128#usize)
  (vals : Array (Array Std.U8 N) 128#usize) (lvl : Std.U32) (cnt : Std.Usize) :
  Result (Array (Array Std.U8 N) 128#usize)
  := do
  loop
    (fun (blocks1, start1, end1, vals1, lvl1, cnt1) =>
      fors.fors_batch_loop3.body target i z a a1 a2 i1 i2 i3 i4 i5 i6 blocks1 start1
      end1 vals1 lvl1 cnt1)
    (blocks, start, «end», vals, lvl, cnt)

@[rust_loop_body]
def fors.fors_pk_from_sig_loop2.body (target : Target)
  {N : Std.Usize} (sig : Slice Std.U8) (a : Array Std.U8 N)
  (a1 : Array Std.U32 8#usize) (a2 : Array Std.U64 8#usize)
  (adrs : address.Adrs) (a3 : Std.U32) (k : Std.Usize)
  (blocks : Array (Array Std.U8 64#usize) 35#usize)
  (idx : Array Std.U32 35#usize) («end» : Array Std.U32 35#usize)
  (vals : Array (Array Std.U8 N) 35#usize) (h : Std.U32) :
  Result (ControlFlow ((Array (Array Std.U8 64#usize) 35#usize) × (Array
    Std.U32 35#usize) × (Array Std.U32 35#usize) × (Array (Array Std.U8 N)
    35#usize) × Std.U32) (Array (Array Std.U8 N) 35#usize))
  := do
  if h < a3
  then
    if N = 16#usize
    then
      let (blocks1, idx1, end1) ←
        fors.fors_pk_from_sig_loop2_loop0 sig adrs a3 k blocks idx «end» vals
          h 0#usize
      let (s, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
          blocks1 { start := 0#usize, «end» := k }
      let s1 ← lift (Array.to_slice idx1)
      let s2 ← lift (Array.to_slice end1)
      let s3 ← hash.chain_blocks N a1 s s1 s2
      let blocks2 := index_mut_back s3
      let vals1 ← fors.fors_pk_from_sig_loop2_loop1 k blocks2 vals 0#usize
      let h1 ← h + 1#u32
      ok (cont (blocks2, idx1, end1, vals1, h1))
    else
      let i ← h + 1#u32
      let a4 ← address.Adrs.with_word2 adrs i
      let (s, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N))) vals
          { «end» := k }
      let (s1, to_slice_mut_back) ← lift (Array.to_slice_mut idx)
      let i1 ← lift (UScalar.cast .Usize a3)
      let i2 ← lift (UScalar.cast .Usize h)
      let (i3, s2, s3) ← PlatformFors.pathParents target a2 a4 s s1 sig i1 i2
      let idx1 := to_slice_mut_back s3
      let vals1 := index_mut_back s2
      let (idx2, vals2) ←
        fors.fors_pk_from_sig_loop2_loop2 sig a a1 a2 adrs a3 k idx1 vals1 h i3
      let h1 ← h + 1#u32
      ok (cont (blocks, idx2, «end», vals2, h1))
  else ok (done vals)

@[rust_loop]
def fors.fors_pk_from_sig_loop2 (target : Target)
  {N : Std.Usize} (sig : Slice Std.U8) (a : Array Std.U8 N)
  (a1 : Array Std.U32 8#usize) (a2 : Array Std.U64 8#usize)
  (adrs : address.Adrs) (a3 : Std.U32) (k : Std.Usize)
  (blocks : Array (Array Std.U8 64#usize) 35#usize)
  (idx : Array Std.U32 35#usize) («end» : Array Std.U32 35#usize)
  (vals : Array (Array Std.U8 N) 35#usize) (h : Std.U32) :
  Result (Array (Array Std.U8 N) 35#usize)
  := do
  loop
    (fun (blocks1, idx1, end1, vals1, h1) => fors.fors_pk_from_sig_loop2.body target
      sig a a1 a2 adrs a3 k blocks1 idx1 end1 vals1 h1)
    (blocks, idx, «end», vals, h)

end slhdsa.PlatformFors.Program
