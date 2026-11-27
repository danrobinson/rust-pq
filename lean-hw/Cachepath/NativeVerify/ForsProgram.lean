import Cachepath.NativeVerify.Active
import Cachepath.NativeVerify.Words
import Shakebatch.RecoverStream
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace slhdsa.NativeVerify.Fors
open ShakeBatch
class ActiveKernel (m : Machine) where
  run : Active m
set_option linter.concreteInstances false
variable [machine : Machine] [stream : Stream] [accelerator : ActiveKernel machine]

/-- [slhdsa::shake::fors_batch::recover]: loop body 1:
    Source: 'src/shake/fors_batch.rs', lines 394:8-397:9 -/
@[rust_loop_body]
def recover_loop0_loop0.body
  (i : Std.U32) (selections : Slice Std.U32) (first : Std.Usize)
  (iter : core.ops.range.Range Std.Usize) (indices : Array Std.U32 machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U32
    machine.width)) (Array Std.U32 machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done indices)
  | some lane =>
    let tree ← first + lane
    let i1 ← lift (UScalar.cast .U32 tree)
    let i2 ← i1 <<< i
    let i3 ← Slice.index_usize selections tree
    let i4 ← i2 + i3
    let a ← Array.update indices lane i4
    ok (cont (iter1, a))

/-- [slhdsa::shake::fors_batch::recover]: loop 1:
    Source: 'src/shake/fors_batch.rs', lines 394:8-397:9 -/
@[rust_loop]
def recover_loop0_loop0
  (iter : core.ops.range.Range Std.Usize) (i : Std.U32)
  (selections : Slice Std.U32) (first : Std.Usize)
  (indices : Array Std.U32 machine.width) :
  Result (Array Std.U32 machine.width)
  := do
  loop
    (fun (iter1, indices1) => recover_loop0_loop0.body i
      selections first iter1 indices1)
    (iter, indices)

/-- [slhdsa::shake::fors_batch::recover]: loop body 2:
    Source: 'src/shake/fors_batch.rs', lines 400:8-402:9 -/
@[rust_loop_body]
def recover_loop0_loop1.body
  (sw : Array Std.U64 4#usize) (iter : core.ops.range.Range Std.Usize)
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
    let a1 ← Array.update state j a
    ok (cont (iter1, a1))

/-- [slhdsa::shake::fors_batch::recover]: loop 2:
    Source: 'src/shake/fors_batch.rs', lines 400:8-402:9 -/
@[rust_loop]
def recover_loop0_loop1
  (iter : core.ops.range.Range Std.Usize) (sw : Array Std.U64 4#usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => recover_loop0_loop1.body sw iter1
      state1)
    (iter, state)

/-- [slhdsa::shake::fors_batch::recover]: loop body 4:
    Source: 'src/shake/fors_batch.rs', lines 409:12-411:13 -/
@[rust_loop_body]
def recover_loop0_loop2_loop0.body
  (offset : Std.Usize) (lane : Std.Usize) (blk : Slice Std.U8)
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
    let i ← ShakeBatch.shake.batch.word blk j
    let i1 ← offset + j
    let (a, index_mut_back) ← Array.index_mut_usize state i1
    let a1 ← Array.update a lane i
    let a2 := index_mut_back a1
    ok (cont (iter1, a2))

/-- [slhdsa::shake::fors_batch::recover]: loop 4:
    Source: 'src/shake/fors_batch.rs', lines 409:12-411:13 -/
@[rust_loop]
def recover_loop0_loop2_loop0
  (iter : core.ops.range.Range Std.Usize) (offset : Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize)
  (blk : Slice Std.U8) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => recover_loop0_loop2_loop0.body
      offset lane blk iter1 state1)
    (iter, state)

/-- [slhdsa::shake::fors_batch::recover]: loop body 3:
    Source: 'src/shake/fors_batch.rs', lines 406:8-412:9 -/
@[rust_loop_body]
def recover_loop0_loop2.body
  (N : Std.Usize) (sig : Slice Std.U8) (n : Std.Usize) (offset : Std.Usize)
  (stride : Std.Usize) (first : Std.Usize) (indices : Array Std.U32 machine.width)
  (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some lane =>
    let i ← Array.index_usize indices lane
    let i1 ← ShakeBatch.core.num.U32.swap_bytes i
    let i2 ← lift (core.convert.num.FromU64U32.from i1)
    let i3 ← i2 <<< 32#i32
    let i4 ← n + 3#usize
    let (a, index_mut_back) ← Array.index_mut_usize state i4
    let a1 ← Array.update a lane i3
    let i5 ← first + lane
    let i6 ← i5 * stride
    let i7 ← i6 * N
    let i8 ← i5 * stride
    let i9 ← i8 + 1#usize
    let i10 ← i9 * N
    let blk ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := i7, «end» := i10 }
    let a2 := index_mut_back a1
    let state1 ←
      recover_loop0_loop2_loop0
        { start := 0#usize, «end» := n } offset a2 lane blk
    ok (cont (iter1, state1))

/-- [slhdsa::shake::fors_batch::recover]: loop 3:
    Source: 'src/shake/fors_batch.rs', lines 406:8-412:9 -/
@[rust_loop]
def recover_loop0_loop2
  (N : Std.Usize) (iter : core.ops.range.Range Std.Usize) (sig : Slice Std.U8)
  (n : Std.Usize) (offset : Std.Usize) (stride : Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) (first : Std.Usize)
  (indices : Array Std.U32 machine.width) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => recover_loop0_loop2.body N sig n
      offset stride first indices iter1 state1)
    (iter, state)

/-- [slhdsa::shake::fors_batch::recover]: loop body 5:
    Source: 'src/shake/fors_batch.rs', lines 414:8-416:9 -/
@[rust_loop_body]
def recover_loop0_loop3.body
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

/-- [slhdsa::shake::fors_batch::recover]: loop 5:
    Source: 'src/shake/fors_batch.rs', lines 414:8-416:9 -/
@[rust_loop]
def recover_loop0_loop3
  (iter : core.slice.iter.IterMut (Array Std.U64 machine.width))
  (back : core.slice.iter.IterMut (Array Std.U64 machine.width) →
  core.slice.iter.IterMut (Array Std.U64 machine.width)) :
  Result ((core.slice.iter.IterMut (Array Std.U64 machine.width)) ×
    (core.slice.iter.IterMut (Array Std.U64 machine.width) →
    core.slice.iter.IterMut (Array Std.U64 machine.width)))
  := do
  loop
    (fun (iter1, back1) => recover_loop0_loop3.body iter1
      back1)
    (iter, back)

/-- [slhdsa::shake::fors_batch::recover]: loop body 7:
    Source: 'src/shake/fors_batch.rs', lines 423:12-426:13 -/
@[rust_loop_body]
def recover_loop0_loop4_loop0.body
  (sw : Array Std.U64 4#usize) (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (cur : Array (Array Std.U64 machine.width) 4#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize) × (Array (Array Std.U64 machine.width) 4#usize))
    ((Array (Array Std.U64 machine.width) 25#usize) × (Array (Array Std.U64 machine.width)
    4#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (state, cur))
  | some j =>
    let a ← Array.index_usize state j
    let a1 ← Array.update cur j a
    let i ← Array.index_usize sw j
    let a2 := Array.repeat machine.width i
    let a3 ← Array.update state j a2
    ok (cont (iter1, a3, a1))

/-- [slhdsa::shake::fors_batch::recover]: loop 7:
    Source: 'src/shake/fors_batch.rs', lines 423:12-426:13 -/
@[rust_loop]
def recover_loop0_loop4_loop0
  (iter : core.ops.range.Range Std.Usize) (sw : Array Std.U64 4#usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (cur : Array (Array Std.U64 machine.width) 4#usize) :
  Result ((Array (Array Std.U64 machine.width) 25#usize) × (Array (Array Std.U64
    machine.width) 4#usize))
  := do
  loop
    (fun (iter1, state1, cur1) =>
      recover_loop0_loop4_loop0.body sw iter1 state1 cur1)
    (iter, state, cur)

/-- [slhdsa::shake::fors_batch::recover]: loop body 9:
    Source: 'src/shake/fors_batch.rs', lines 439:20-442:21 -/
@[rust_loop_body]
def recover_loop0_loop4_loop1_loop0.body
  (n : Std.Usize) (offset : Std.Usize)
  (cur : Array (Array Std.U64 machine.width) 4#usize) (lane : Std.Usize)
  (sib : Slice Std.U8) (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some j =>
    let a ← Array.index_usize cur j
    let i ← Array.index_usize a lane
    let i1 ← offset + j
    let (a1, index_mut_back) ← Array.index_mut_usize state i1
    let a2 ← Array.update a1 lane i
    let i2 ← ShakeBatch.shake.batch.word sib j
    let i3 ← offset + n
    let i4 ← i3 + j
    let state1 := index_mut_back a2
    let (a3, index_mut_back1) ← Array.index_mut_usize state1 i4
    let a4 ← Array.update a3 lane i2
    let a5 := index_mut_back1 a4
    ok (cont (iter1, a5))

/-- [slhdsa::shake::fors_batch::recover]: loop 9:
    Source: 'src/shake/fors_batch.rs', lines 439:20-442:21 -/
@[rust_loop]
def recover_loop0_loop4_loop1_loop0
  (iter : core.ops.range.Range Std.Usize) (n : Std.Usize) (offset : Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (cur : Array (Array Std.U64 machine.width) 4#usize) (lane : Std.Usize)
  (sib : Slice Std.U8) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) =>
      recover_loop0_loop4_loop1_loop0.body n offset cur lane
      sib iter1 state1)
    (iter, state)

/-- [slhdsa::shake::fors_batch::recover]: loop body 10:
    Source: 'src/shake/fors_batch.rs', lines 444:20-447:21 -/
@[rust_loop_body]
def recover_loop0_loop4_loop1_loop1.body
  (n : Std.Usize) (offset : Std.Usize)
  (cur : Array (Array Std.U64 machine.width) 4#usize) (lane : Std.Usize)
  (sib : Slice Std.U8) (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some j =>
    let i ← ShakeBatch.shake.batch.word sib j
    let i1 ← offset + j
    let (a, index_mut_back) ← Array.index_mut_usize state i1
    let a1 ← Array.update a lane i
    let a2 ← Array.index_usize cur j
    let i2 ← Array.index_usize a2 lane
    let i3 ← offset + n
    let i4 ← i3 + j
    let state1 := index_mut_back a1
    let (a3, index_mut_back1) ← Array.index_mut_usize state1 i4
    let a4 ← Array.update a3 lane i2
    let a5 := index_mut_back1 a4
    ok (cont (iter1, a5))

/-- [slhdsa::shake::fors_batch::recover]: loop 10:
    Source: 'src/shake/fors_batch.rs', lines 444:20-447:21 -/
@[rust_loop]
def recover_loop0_loop4_loop1_loop1
  (iter : core.ops.range.Range Std.Usize) (n : Std.Usize) (offset : Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (cur : Array (Array Std.U64 machine.width) 4#usize) (lane : Std.Usize)
  (sib : Slice Std.U8) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) =>
      recover_loop0_loop4_loop1_loop1.body n offset cur lane
      sib iter1 state1)
    (iter, state)

/-- [slhdsa::shake::fors_batch::recover]: loop body 8:
    Source: 'src/shake/fors_batch.rs', lines 431:12-449:13 -/
@[rust_loop_body]
def recover_loop0_loop4_loop1.body
  (N : Std.Usize) (sig : Slice Std.U8) (n : Std.Usize) (offset : Std.Usize)
  (stride : Std.Usize) (first : Std.Usize) (lvl : Std.U32)
  (cur : Array (Array Std.U64 machine.width) 4#usize) (lvl_lo : Std.U64)
  (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (indices : Array Std.U32 machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize) × (Array Std.U32 machine.width)) ((Array (Array
    Std.U64 machine.width) 25#usize) × (Array Std.U32 machine.width)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (state, indices))
  | some lane =>
    let idx ← Array.index_usize indices lane
    let parent ← idx >>> 1#i32
    let (_, index_mut_back) ← Array.index_mut_usize indices lane
    let i ← ShakeBatch.core.num.U32.swap_bytes parent
    let i1 ← lift (core.convert.num.FromU64U32.from i)
    let i2 ← i1 <<< 32#i32
    let i3 ← n + 3#usize
    let (a, index_mut_back1) ← Array.index_mut_usize state i3
    let (_, index_mut_back2) ← Array.index_mut_usize a lane
    let i4 ← lift (lvl_lo ||| i2)
    let i5 ← first + lane
    let i6 ← i5 * stride
    let i7 ← lift (UScalar.cast .Usize lvl)
    let i8 ← i6 + i7
    let sib_blk_idx ← i8 + 1#usize
    let i9 ← sib_blk_idx * N
    let i10 ← sib_blk_idx + 1#usize
    let i11 ← i10 * N
    let sib ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := i9, «end» := i11 }
    let i12 ← lift (idx &&& 1#u32)
    if i12 = 0#u32
    then
      let a1 := index_mut_back2 i4
      let a2 := index_mut_back1 a1
      let state1 ←
        recover_loop0_loop4_loop1_loop0
          { start := 0#usize, «end» := n } n offset a2 cur lane sib
      let a3 := index_mut_back parent
      ok (cont (iter1, state1, a3))
    else
      let a1 := index_mut_back2 i4
      let a2 := index_mut_back1 a1
      let state1 ←
        recover_loop0_loop4_loop1_loop1
          { start := 0#usize, «end» := n } n offset a2 cur lane sib
      let a3 := index_mut_back parent
      ok (cont (iter1, state1, a3))

/-- [slhdsa::shake::fors_batch::recover]: loop 8:
    Source: 'src/shake/fors_batch.rs', lines 431:12-449:13 -/
@[rust_loop]
def recover_loop0_loop4_loop1
  (N : Std.Usize) (iter : core.ops.range.Range Std.Usize) (sig : Slice Std.U8)
  (n : Std.Usize) (offset : Std.Usize) (stride : Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) (first : Std.Usize)
  (indices : Array Std.U32 machine.width) (lvl : Std.U32)
  (cur : Array (Array Std.U64 machine.width) 4#usize) (lvl_lo : Std.U64) :
  Result ((Array (Array Std.U64 machine.width) 25#usize) × (Array Std.U32 machine.width))
  := do
  loop
    (fun (iter1, state1, indices1) =>
      recover_loop0_loop4_loop1.body N sig n offset stride
      first lvl cur lvl_lo iter1 state1 indices1)
    (iter, state, indices)

/-- [slhdsa::shake::fors_batch::recover]: loop body 11:
    Source: 'src/shake/fors_batch.rs', lines 450:12-452:13 -/
@[rust_loop_body]
def recover_loop0_loop4_loop2.body
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

/-- [slhdsa::shake::fors_batch::recover]: loop 11:
    Source: 'src/shake/fors_batch.rs', lines 450:12-452:13 -/
@[rust_loop]
def recover_loop0_loop4_loop2
  (iter : core.slice.iter.IterMut (Array Std.U64 machine.width))
  (back : core.slice.iter.IterMut (Array Std.U64 machine.width) →
  core.slice.iter.IterMut (Array Std.U64 machine.width)) :
  Result ((core.slice.iter.IterMut (Array Std.U64 machine.width)) ×
    (core.slice.iter.IterMut (Array Std.U64 machine.width) →
    core.slice.iter.IterMut (Array Std.U64 machine.width)))
  := do
  loop
    (fun (iter1, back1) => recover_loop0_loop4_loop2.body
      iter1 back1)
    (iter, back)

/-- [slhdsa::shake::fors_batch::recover]: loop body 12:
    Source: 'src/shake/fors_batch.rs', lines 454:12-456:13 -/
@[rust_loop_body]
def recover_loop0_loop4_loop3.body
  (i : Std.U64) (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64))
    ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64 →
    core.slice.iter.IterMut Std.U64)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some v =>
    let v1 ← lift (v ||| i)
    ok (cont (iter1, fun im => let im1 := next_back im (some v1)
                               back im1))

/-- [slhdsa::shake::fors_batch::recover]: loop 12:
    Source: 'src/shake/fors_batch.rs', lines 454:12-456:13 -/
@[rust_loop]
def recover_loop0_loop4_loop3
  (i : Std.U64) (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1) => recover_loop0_loop4_loop3.body i
      iter1 back1)
    (iter, back)

/-- [slhdsa::shake::fors_batch::recover]: loop body 6:
    Source: 'src/shake/fors_batch.rs', lines 421:8-458:9 -/
@[rust_loop_body]
def recover_loop0_loop4.body
  (N : Std.Usize) (i : Std.U64) (sig : Slice Std.U8) (n : Std.Usize)
  (offset : Std.Usize) (pad_pair : Std.Usize) (stride : Std.Usize)
  (sw : Array Std.U64 4#usize) (aw : Array Std.U64 4#usize) (first : Std.Usize)
  (active : Std.Usize) (iter : core.ops.range.Range Std.U32)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (indices : Array Std.U32 machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (Array (Array Std.U64
    machine.width) 25#usize) × (Array Std.U32 machine.width)) (Array (Array Std.U64
    machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done state)
  | some lvl =>
    let a := Array.repeat machine.width 0#u64
    let cur := Array.repeat 4#usize a
    let (state1, cur1) ←
      recover_loop0_loop4_loop0
        { start := 0#usize, «end» := n } sw state cur
    let i1 ← Array.index_usize aw 0#usize
    let a1 := Array.repeat machine.width i1
    let state2 ← Array.update state1 n a1
    let i2 ← Array.index_usize aw 1#usize
    let i3 ← n + 1#usize
    let a2 := Array.repeat machine.width i2
    let state3 ← Array.update state2 i3 a2
    let i4 ← Array.index_usize aw 2#usize
    let i5 ← n + 2#usize
    let a3 := Array.repeat machine.width i4
    let a4 ← Array.update state3 i5 a3
    let i6 ← lvl + 1#u32
    let i7 ← ShakeBatch.core.num.U32.swap_bytes i6
    let lvl_lo ← lift (core.convert.num.FromU64U32.from i7)
    let (state4, indices1) ←
      recover_loop0_loop4_loop1 N
        { start := 0#usize, «end» := active } sig n offset stride a4 first
        indices lvl cur1 lvl_lo
    let i8 ← pad_pair + 1#usize
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
        state4 { start := i8, «end» := 25#usize }
    let (iter2, into_iter_back) ←
      core.slice.Slice.iter_mut s
    let (im, back) ←
      recover_loop0_loop4_loop2 iter2 (fun im1 => im1)
    let im1 := back im
    let s1 := into_iter_back im1
    let state5 := index_mut_back s1
    let a5 := Array.repeat machine.width 31#u64
    let state6 ← Array.update state5 pad_pair a5
    let (a6, index_mut_back1) ← Array.index_mut_usize state6 16#usize
    let (iter3, into_iter_back1) ←
      MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
        a6
    let (im2, back1) ←
      recover_loop0_loop4_loop3 i iter3 (fun im3 => im3)
    let im3 := back1 im2
    let a7 := into_iter_back1 im3
    let state7 := index_mut_back1 a7
    let state8 ← accelerator.run state7 active
    ok (cont (iter1, state8, indices1))

/-- [slhdsa::shake::fors_batch::recover]: loop 6:
    Source: 'src/shake/fors_batch.rs', lines 421:8-458:9 -/
@[rust_loop]
def recover_loop0_loop4
  (N : Std.Usize) (i : Std.U64) (iter : core.ops.range.Range Std.U32)
  (sig : Slice Std.U8) (n : Std.Usize) (offset : Std.Usize)
  (pad_pair : Std.Usize) (stride : Std.Usize) (sw : Array Std.U64 4#usize)
  (aw : Array Std.U64 4#usize) (state : Array (Array Std.U64 machine.width) 25#usize)
  (first : Std.Usize) (active : Std.Usize) (indices : Array Std.U32 machine.width) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1, indices1) => recover_loop0_loop4.body
      N i sig n offset pad_pair stride sw aw first active iter1 state1
      indices1)
    (iter, state, indices)

/-- [slhdsa::shake::fors_batch::recover]: loop body 14:
    Source: 'src/shake/fors_batch.rs', lines 462:12-464:13 -/
@[rust_loop_body]
def recover_loop0_loop5_loop0.body
  {N : Std.Usize} (state : Array (Array Std.U64 machine.width) 25#usize)
  (lane : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (root : Array Std.U8 N) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U8 N))
    (Array Std.U8 N))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done root)
  | some j =>
    let i ← 8#usize * j
    let i1 ← i + 8#usize
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) root
        { start := i, «end» := i1 }
    let a ← Array.index_usize state j
    let i2 ← Array.index_usize a lane
    let a1 ← lift (core.num.U64.to_le_bytes i2)
    let s1 ← lift (Array.to_slice a1)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let root1 := index_mut_back s2
    ok (cont (iter1, root1))

/-- [slhdsa::shake::fors_batch::recover]: loop 14:
    Source: 'src/shake/fors_batch.rs', lines 462:12-464:13 -/
@[rust_loop]
def recover_loop0_loop5_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize)
  (root : Array Std.U8 N) :
  Result (Array Std.U8 N)
  := do
  loop
    (fun (iter1, root1) => recover_loop0_loop5_loop0.body
      state lane iter1 root1)
    (iter, root)

/-- [slhdsa::shake::fors_batch::recover]: loop body 13:
    Source: 'src/shake/fors_batch.rs', lines 460:8-466:9 -/
@[rust_loop_body]
def recover_loop0_loop5.body
  (N : Std.Usize) (n : Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize)
  (iter : core.ops.range.Range Std.Usize) (pk : stream.State) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × stream.State)
    stream.State)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done pk)
  | some lane =>
    let root := Array.repeat N 0#u8
    let root1 ←
      recover_loop0_loop5_loop0
        { start := 0#usize, «end» := n } state lane root
    let s ← lift (Array.to_slice root1)
    let pk1 ← stream.absorb pk s
    ok (cont (iter1, pk1))

/-- [slhdsa::shake::fors_batch::recover]: loop 13:
    Source: 'src/shake/fors_batch.rs', lines 460:8-466:9 -/
@[rust_loop]
def recover_loop0_loop5
  (N : Std.Usize) (iter : core.ops.range.Range Std.Usize) (n : Std.Usize)
  (pk : stream.State) (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result stream.State
  := do
  loop
    (fun (iter1, pk1) => recover_loop0_loop5.body N n state
      iter1 pk1)
    (iter, pk)

/-- [slhdsa::shake::fors_batch::recover]: loop body 0:
    Source: 'src/shake/fors_batch.rs', lines 391:4-467:5 -/
@[rust_loop_body]
def recover_loop0.body
  (N : Std.Usize) (i : Std.U32) (selections : Slice Std.U32)
  (sig : Slice Std.U8) (n : Std.Usize) (offset : Std.Usize)
  (pad_short : Std.Usize) (pad_pair : Std.Usize) (stride : Std.Usize)
  (sw : Array Std.U64 4#usize) (aw : Array Std.U64 4#usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (pk : stream.State) (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Std.Usize)) × stream.State × (Array (Array Std.U64 machine.width) 25#usize))
    stream.State)
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done pk)
  | some first =>
    let i1 := Slice.len selections
    let i2 ← i1 - first
    let active ←
      lift (core.cmp.impls.OrdUsize.min i2 machine.width)
    let indices := Array.repeat machine.width 0#u32
    let indices1 ←
      recover_loop0_loop0
        { start := 0#usize, «end» := active } i selections first indices
    let state1 ←
      recover_loop0_loop1 { start := 0#usize, «end» := n }
        sw state
    let i3 ← Array.index_usize aw 0#usize
    let a := Array.repeat machine.width i3
    let state2 ← Array.update state1 n a
    let i4 ← Array.index_usize aw 1#usize
    let i5 ← n + 1#usize
    let a1 := Array.repeat machine.width i4
    let state3 ← Array.update state2 i5 a1
    let i6 ← Array.index_usize aw 2#usize
    let i7 ← n + 2#usize
    let a2 := Array.repeat machine.width i6
    let a3 ← Array.update state3 i7 a2
    let state4 ←
      recover_loop0_loop2 N
        { start := 0#usize, «end» := active } sig n offset stride a3 first
        indices1
    let a4 := Array.repeat machine.width 31#u64
    let state5 ← Array.update state4 pad_short a4
    let i8 ← pad_short + 1#usize
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
        state5 { start := i8, «end» := 25#usize }
    let (iter2, into_iter_back) ←
      core.slice.Slice.iter_mut s
    let (im, back) ←
      recover_loop0_loop3 iter2 (fun im1 => im1)
    let i9 ← 1#u64 <<< 63#i32
    let im1 := back im
    let s1 := into_iter_back im1
    let state6 := index_mut_back s1
    let a5 := Array.repeat machine.width i9
    let state7 ← Array.update state6 16#usize a5
    let state8 ← accelerator.run state7 active
    let state9 ←
      recover_loop0_loop4 N i9
        { start := 0#u32, «end» := i } sig n offset pad_pair stride sw aw
        state8 first active indices1
    let pk1 ←
      recover_loop0_loop5 N
        { start := 0#usize, «end» := active } n pk state9
    ok (cont (iter1, pk1, state9))

/-- [slhdsa::shake::fors_batch::recover]: loop 0:
    Source: 'src/shake/fors_batch.rs', lines 391:4-467:5 -/
@[rust_loop]
def recover_loop0
  (N : Std.Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (i : Std.U32) (selections : Slice Std.U32) (sig : Slice Std.U8)
  (n : Std.Usize) (offset : Std.Usize) (pad_short : Std.Usize)
  (pad_pair : Std.Usize) (stride : Std.Usize) (sw : Array Std.U64 4#usize)
  (aw : Array Std.U64 4#usize) (pk : stream.State)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result stream.State
  := do
  loop
    (fun (iter1, pk1, state1) => recover_loop0.body N i
      selections sig n offset pad_short pad_pair stride sw aw iter1 pk1 state1)
    (iter, pk, state)

/-- [slhdsa::shake::fors_batch::recover]:
    Source: 'src/shake/fors_batch.rs', lines 373:0-469:1 -/
def recover
  {N : Std.Usize} (p : params.Params) (selections : Slice Std.U32)
  (sig : Slice Std.U8) (seed : Array Std.U8 N) (addr : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let n ← N / 8#usize
  let offset ← n + 4#usize
  let pad_short ← offset + n
  let i ← 2#usize * n
  let pad_pair ← offset + i
  let i1 ← lift (UScalar.cast .Usize p.a)
  let stride ← i1 + 1#usize
  let sw ← seed_words seed
  let a ← address.Adrs.with_type addr address.FORS_TREE
  let a1 ← address.Adrs.with_keypair a addr.keypair
  let aw ← adrs_words a1
  let a2 ← address.Adrs.with_type addr address.FORS_ROOTS
  let a3 ← address.Adrs.with_keypair a2 addr.keypair
  let pk ← stream.start seed a3
  let a4 := Array.repeat machine.width 0#u64
  let state := Array.repeat 25#usize a4
  let i2 := Slice.len selections
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := i2 } machine.width
  let pk1 ←
    recover_loop0 N iter p.a selections sig n offset pad_short
      pad_pair stride sw aw pk state
  stream.digest N pk1

end slhdsa.NativeVerify.Fors
