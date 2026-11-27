import Cachepath.NativeVerify.ActiveHashProgram
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeVerify.ForsFused
open ShakeBatch
variable [machine : Machine] (permute : Active machine)
@[rust_loop_body]
def fused_loop0.body
  (indices : Array Std.U32 machine.width) (iter : core.ops.range.Range Std.Usize)
  (w3 : Array Std.U64 machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    machine.width)) (Array Std.U64 machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done w3)
  | some lane =>
    let i ← Array.index_usize indices lane
    let i1 ← ShakeBatch.core.num.U32.swap_bytes i
    let i2 ← lift (core.convert.num.FromU64U32.from i1)
    let i3 ← i2 <<< 32#i32
    let a ← Array.update w3 lane i3
    ok (cont (iter1, a))

@[rust_loop]
def fused_loop0
  (iter : core.ops.range.Range Std.Usize) (indices : Array Std.U32 machine.width)
  (w3 : Array Std.U64 machine.width) :
  Result (Array Std.U64 machine.width)
  := do
  loop
    (fun (iter1, w31) => fused_loop0.body indices
      iter1 w31)
    (iter, w3)

@[rust_loop_body]
def fused_loop1.body
  (offset : Std.Usize) (sw : Array Std.U64 4#usize)
  (skw : Array Std.U64 4#usize) (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some j =>
    let i ← Array.index_usize sw j
    let a := Array.repeat machine.width i
    let state1 ← Array.update state j a
    let i1 ← Array.index_usize skw j
    let i2 ← offset + j
    let a1 := Array.repeat machine.width i1
    let a2 ← Array.update state1 i2 a1
    ok (cont (iter1, a2))

@[rust_loop]
def fused_loop1
  (iter : core.ops.range.Range Std.Usize) (offset : Std.Usize)
  (sw : Array Std.U64 4#usize) (skw : Array Std.U64 4#usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => fused_loop1.body
      offset sw skw iter1 state1)
    (iter, state)

@[rust_loop_body]
def fused_loop2.body
  (offset : Std.Usize) (sw : Array Std.U64 4#usize)
  (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some j =>
    let a ← Array.index_usize state j
    let i ← offset + j
    let state1 ← Array.update state i a
    let i1 ← Array.index_usize sw j
    let a1 := Array.repeat machine.width i1
    let a2 ← Array.update state1 j a1
    ok (cont (iter1, a2))

@[rust_loop]
def fused_loop2
  (iter : core.ops.range.Range Std.Usize) (offset : Std.Usize)
  (sw : Array Std.U64 4#usize) (state : Array (Array Std.U64 machine.width) 25#usize)
  :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => fused_loop2.body
      offset sw iter1 state1)
    (iter, state)

@[rust_loop_body]
def fused_loop3.body
  (iter : core.slice.iter.IterMut (Array Std.U64 machine.width))
  (back : core.slice.iter.IterMut (Array Std.U64 machine.width) →
  core.slice.iter.IterMut (Array Std.U64 machine.width)) :
  Result (ControlFlow ((core.slice.iter.IterMut (Array Std.U64 machine.width)) ×
    (core.slice.iter.IterMut (Array Std.U64 machine.width) →
    core.slice.iter.IterMut (Array Std.U64 machine.width))) ((core.slice.iter.IterMut
    (Array Std.U64 machine.width)) × (core.slice.iter.IterMut (Array Std.U64
    machine.width) → core.slice.iter.IterMut (Array Std.U64 machine.width))))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some _ =>
    let w := Array.repeat machine.width 0#u64
    ok (cont (iter1, fun im => let im1 := next_back im (some w)
                               back im1))

@[rust_loop]
def fused_loop3
  (iter : core.slice.iter.IterMut (Array Std.U64 machine.width))
  (back : core.slice.iter.IterMut (Array Std.U64 machine.width) →
  core.slice.iter.IterMut (Array Std.U64 machine.width)) :
  Result ((core.slice.iter.IterMut (Array Std.U64 machine.width)) ×
    (core.slice.iter.IterMut (Array Std.U64 machine.width) →
    core.slice.iter.IterMut (Array Std.U64 machine.width)))
  := do
  loop
    (fun (iter1, back1) => fused_loop3.body iter1
      back1)
    (iter, back)

@[rust_loop_body]
def fused_loop4_loop0.body
  {N : Std.Usize} (state : Array (Array Std.U64 machine.width) 25#usize)
  (j : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (out : Array (Array Std.U8 N) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array Std.U8
    N) machine.width)) (Array (Array Std.U8 N) machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some lane =>
    let (a, index_mut_back) ← Array.index_mut_usize out lane
    let i ← 8#usize * j
    let i1 ← i + 8#usize
    let (s, index_mut_back1) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a
        { start := i, «end» := i1 }
    let a1 ← Array.index_usize state j
    let i2 ← Array.index_usize a1 lane
    let a2 ← lift (core.num.U64.to_le_bytes i2)
    let s1 ← lift (Array.to_slice a2)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let a3 := index_mut_back1 s2
    let a4 := index_mut_back a3
    ok (cont (iter1, a4))

@[rust_loop]
def fused_loop4_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (out : Array (Array Std.U8 N) machine.width) (j : Std.Usize) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  loop
    (fun (iter1, out1) => fused_loop4_loop0.body
      state j iter1 out1)
    (iter, out)

@[rust_loop_body]
def fused_loop4.body
  {N : Std.Usize} (active : Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (iter : core.ops.range.Range Std.Usize)
  (out : Array (Array Std.U8 N) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array Std.U8
    N) machine.width)) (Array (Array Std.U8 N) machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some j =>
    let out1 ←
      fused_loop4_loop0
        { start := 0#usize, «end» := active } state out j
    ok (cont (iter1, out1))

@[rust_loop]
def fused_loop4
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (active : Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (out : Array (Array Std.U8 N) machine.width) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  loop
    (fun (iter1, out1) => fused_loop4.body active
      state iter1 out1)
    (iter, out)

def fused
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (addr : address.Adrs) (indices : Array Std.U32 machine.width) (active : Std.Usize)
  :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let n ← N / 8#usize
  let offset ← n + 4#usize
  let pad ← offset + n
  let sw ← NativeVerify.seed_words seed
  let skw ← NativeVerify.seed_words sk
  let a ← address.Adrs.with_type addr address.FORS_PRF
  let a1 ← address.Adrs.with_keypair a addr.keypair
  let aw_prf ← NativeVerify.adrs_words a1
  let a2 ← address.Adrs.with_type addr address.FORS_TREE
  let a3 ← address.Adrs.with_keypair a2 addr.keypair
  let aw_tree ← NativeVerify.adrs_words a3
  let w3 := Array.repeat machine.width 0#u64
  let w31 ←
    fused_loop0
      { start := 0#usize, «end» := active } indices w3
  let a4 := Array.repeat machine.width 0#u64
  let state := Array.repeat 25#usize a4
  let state1 ←
    fused_loop1 { start := 0#usize, «end» := n }
      offset sw skw state
  let i ← Array.index_usize aw_prf 0#usize
  let a5 := Array.repeat machine.width i
  let state2 ← Array.update state1 n a5
  let i1 ← Array.index_usize aw_prf 1#usize
  let i2 ← n + 1#usize
  let a6 := Array.repeat machine.width i1
  let state3 ← Array.update state2 i2 a6
  let i3 ← Array.index_usize aw_prf 2#usize
  let i4 ← n + 2#usize
  let a7 := Array.repeat machine.width i3
  let state4 ← Array.update state3 i4 a7
  let i5 ← n + 3#usize
  let state5 ← Array.update state4 i5 w31
  let a8 := Array.repeat machine.width 31#u64
  let state6 ← Array.update state5 pad a8
  let i6 ← 1#u64 <<< 63#i32
  let a9 := Array.repeat machine.width i6
  let state7 ← Array.update state6 16#usize a9
  let state8 ← permute state7 active
  let state9 ←
    fused_loop2 { start := 0#usize, «end» := n }
      offset sw state8
  let i7 ← Array.index_usize aw_tree 0#usize
  let a10 := Array.repeat machine.width i7
  let state10 ← Array.update state9 n a10
  let i8 ← Array.index_usize aw_tree 1#usize
  let i9 ← n + 1#usize
  let a11 := Array.repeat machine.width i8
  let state11 ← Array.update state10 i9 a11
  let i10 ← Array.index_usize aw_tree 2#usize
  let i11 ← n + 2#usize
  let a12 := Array.repeat machine.width i10
  let state12 ← Array.update state11 i11 a12
  let i12 ← n + 3#usize
  let state13 ← Array.update state12 i12 w31
  let a13 := Array.repeat machine.width 31#u64
  let state14 ← Array.update state13 pad a13
  let i13 ← pad + 1#usize
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
      state14 { start := i13, «end» := 25#usize }
  let (iter, into_iter_back) ←
    core.slice.Slice.iter_mut s
  let (im, back) ←
    fused_loop3 iter (fun im1 => im1)
  let im1 := back im
  let s1 := into_iter_back im1
  let state15 := index_mut_back s1
  let a14 := Array.repeat machine.width i6
  let state16 ← Array.update state15 16#usize a14
  let state17 ← permute state16 active
  let a15 := Array.repeat N 0#u8
  let out := Array.repeat machine.width a15
  fused_loop4 { start := 0#usize, «end» := n }
    active state17 out
end slhdsa.NativeVerify.ForsFused
