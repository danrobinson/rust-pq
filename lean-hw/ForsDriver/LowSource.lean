import ForsDriver.Program
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsDriver
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]

def leafPrefix {N cap : Usize} (sk seed : Array U8 N) (addr : address.Adrs) (ids : Array U32 cap) (count : Usize) := do
  let s ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
    ids {«end»:=count}
  let (part,restore) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 N))) (Array.repeat cap (Array.repeat N 0#u8)) {«end»:=count}
  let out ← ForsWideRows.leaves sk seed addr s part
  ok (restore out)

def pairPrefix {N cap srcCap : Usize} (seed : Array U8 N) (tree : address.Adrs) (height : U32)
    (ids : Array U32 cap) (children : Array (Array U8 N) srcCap) (count childCount : Usize) := do
  let s ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
    ids {«end»:=count}
  let l ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 N)))
    children {«end»:=childCount}
  let (part,restore) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 N))) (Array.repeat cap (Array.repeat N 0#u8)) {«end»:=count}
  let out ← ForsWideRows.pairs seed tree height s l part
  ok (restore out)

def low0 {N : Usize} (p : params.Params) (choices : Slice U32) (sk seed : Array U8 N) (addr : address.Adrs)
    (stride : Usize) (sig : Buffer) := do
  let k := choices.len
  let ids ← sign_loop2 ⟨0#usize,k⟩ choices p.a (Array.repeat 35#usize 0#u32)
  let rows ← leafPrefix sk seed addr ids k
  sign_loop3 ⟨0#usize,k⟩ stride sig rows

def low1 {N : Usize} (p : params.Params) (choices : Slice U32) (sk seed : Array U8 N) (addr tree : address.Adrs)
    (stride : Usize) (sig : Buffer) := do
  let k := choices.len
  let (li,ni) ← sign_loop4 ⟨0#usize,k⟩ choices p.a (Array.repeat 70#usize 0#u32) (Array.repeat 35#usize 0#u32)
  let two ← 2#usize*k
  let rows ← leafPrefix sk seed addr li two
  let roots ← pairPrefix seed tree 1#u32 ni rows k two
  sign_loop5 ⟨0#usize,k⟩ stride sig roots

def low2 {N : Usize} (p : params.Params) (choices : Slice U32) (sk seed : Array U8 N) (addr tree : address.Adrs)
    (stride : Usize) (sig : Buffer) := do
  let k := choices.len
  let (li,l1,l2) ← sign_loop6 ⟨0#usize,k⟩ choices p.a (Array.repeat 140#usize 0#u32)
    (Array.repeat 70#usize 0#u32) (Array.repeat 35#usize 0#u32)
  let four ← 4#usize*k
  let rows ← leafPrefix sk seed addr li four
  let two ← 2#usize*k
  let parents ← pairPrefix seed tree 1#u32 l1 rows two four
  let roots ← pairPrefix seed tree 2#u32 l2 parents k two
  sign_loop7 ⟨0#usize,k⟩ stride sig roots
end slhdsa.ForsDriver
