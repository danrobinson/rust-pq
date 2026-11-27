import Cachepath.NativeVerify.WotsRound
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeShakeWots
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]
noncomputable section
@[rust_loop_body]
def refill_short_inplace_loop0.body
  (sw : Array Std.U64 4#usize) (offset : Std.Usize)
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
def refill_short_inplace_loop0
  (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) (sw : Array Std.U64 4#usize)
  (offset : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => refill_short_inplace_loop0.body sw
      offset iter1 state1)
    (iter, state)

@[rust_loop_body]
def refill_short_inplace_loop1.body
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
def refill_short_inplace_loop1
  (iter : core.slice.iter.IterMut (Array Std.U64 machine.width))
  (back : core.slice.iter.IterMut (Array Std.U64 machine.width) →
  core.slice.iter.IterMut (Array Std.U64 machine.width)) :
  Result ((core.slice.iter.IterMut (Array Std.U64 machine.width)) ×
    (core.slice.iter.IterMut (Array Std.U64 machine.width) →
    core.slice.iter.IterMut (Array Std.U64 machine.width)))
  := do
  loop
    (fun (iter1, back1) => refill_short_inplace_loop1.body iter1
      back1)
    (iter, back)

def refill_short_inplace
  (N : Std.Usize) (state : Array (Array Std.U64 machine.width) 25#usize)
  (sw : Array Std.U64 4#usize) (w0 : Std.U64) (w1 : Std.U64)
  (w2 : Array Std.U64 machine.width) (w3 : Array Std.U64 machine.width) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  let n ← N / 8#usize
  let offset ← n + 4#usize
  let state1 ←
    refill_short_inplace_loop0 { start := 0#usize, «end» := n }
      state sw offset
  let a := Array.repeat machine.width w0
  let state2 ← Array.update state1 n a
  let i ← n + 1#usize
  let a1 := Array.repeat machine.width w1
  let state3 ← Array.update state2 i a1
  let i1 ← n + 2#usize
  let state4 ← Array.update state3 i1 w2
  let i2 ← n + 3#usize
  let state5 ← Array.update state4 i2 w3
  let pad ← offset + n
  let a2 := Array.repeat machine.width 31#u64
  let state6 ← Array.update state5 pad a2
  let i3 ← pad + 1#usize
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
      state6 { start := i3, «end» := 25#usize }
  let (iter, into_iter_back) ←
    core.slice.Slice.iter_mut s
  let (im, back) ←
    refill_short_inplace_loop1 iter (fun im1 => im1)
  let i4 ← 1#u64 <<< 63#i32
  let im1 := back im
  let s1 := into_iter_back im1
  let state7 := index_mut_back s1
  let a3 := Array.repeat machine.width i4
  Array.update state7 16#usize a3

@[rust_loop_body]
def fill_prf_loop0.body
  (sw : Array Std.U64 4#usize) (skw : Array Std.U64 4#usize)
  (offset : Std.Usize) (iter : core.ops.range.Range Std.Usize)
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
def fill_prf_loop0
  (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) (sw : Array Std.U64 4#usize)
  (skw : Array Std.U64 4#usize) (offset : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => fill_prf_loop0.body sw skw offset iter1
      state1)
    (iter, state)

@[rust_loop_body]
def fill_prf_loop1.body
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
def fill_prf_loop1
  (iter : core.slice.iter.IterMut (Array Std.U64 machine.width))
  (back : core.slice.iter.IterMut (Array Std.U64 machine.width) →
  core.slice.iter.IterMut (Array Std.U64 machine.width)) :
  Result ((core.slice.iter.IterMut (Array Std.U64 machine.width)) ×
    (core.slice.iter.IterMut (Array Std.U64 machine.width) →
    core.slice.iter.IterMut (Array Std.U64 machine.width)))
  := do
  loop
    (fun (iter1, back1) => fill_prf_loop1.body iter1 back1)
    (iter, back)

def fill_prf
  (N : Std.Usize) (state : Array (Array Std.U64 machine.width) 25#usize)
  (sw : Array Std.U64 4#usize) (skw : Array Std.U64 4#usize) (w0 : Std.U64)
  (w1 : Std.U64) (w2 : Array Std.U64 machine.width) (w3 : Array Std.U64 machine.width) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  let n ← N / 8#usize
  let offset ← n + 4#usize
  let state1 ←
    fill_prf_loop0 { start := 0#usize, «end» := n } state sw skw
      offset
  let a := Array.repeat machine.width w0
  let state2 ← Array.update state1 n a
  let i ← n + 1#usize
  let a1 := Array.repeat machine.width w1
  let state3 ← Array.update state2 i a1
  let i1 ← n + 2#usize
  let state4 ← Array.update state3 i1 w2
  let i2 ← n + 3#usize
  let state5 ← Array.update state4 i2 w3
  let pad ← offset + n
  let a2 := Array.repeat machine.width 31#u64
  let state6 ← Array.update state5 pad a2
  let i3 ← pad + 1#usize
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
      state6 { start := i3, «end» := 25#usize }
  let (iter, into_iter_back) ←
    core.slice.Slice.iter_mut s
  let (im, back) ← fill_prf_loop1 iter (fun im1 => im1)
  let i4 ← 1#u64 <<< 63#i32
  let im1 := back im
  let s1 := into_iter_back im1
  let state7 := index_mut_back s1
  let a3 := Array.repeat machine.width i4
  Array.update state7 16#usize a3
end
end slhdsa.NativeShakeWots
