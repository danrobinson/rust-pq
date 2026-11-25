import Cachepath.NativeVerify.Active
import Cachepath.NativeVerify.Words
import Shakeopt.WotsRefill
import Shakebatch.WotsBatches
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeVerify.Wots
open ShakeBatch
set_option linter.concreteInstances false
noncomputable section
class Dispatch (machine : Machine) where
  permute : Active machine
variable [machine : Machine] [Dispatch machine] [stream : Stream]

@[rust_loop_body]
def extract_lane_loop.body
  {N : Std.Usize} (s : Array (Array Std.U64 machine.width) 25#usize)
  (word_offset : Std.Usize) (lane : Std.Usize)
  (iter : core.ops.range.Range Std.Usize) (out : Array Std.U8 N) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U8 N))
    (Array Std.U8 N))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some j =>
    let i ← 8#usize * j
    let i1 ← i + 8#usize
    let (s1, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) out
        { start := i, «end» := i1 }
    let i2 ← word_offset + j
    let a ← Array.index_usize s i2
    let i3 ← Array.index_usize a lane
    let a1 ← lift (core.num.U64.to_le_bytes i3)
    let s2 ← lift (Array.to_slice a1)
    let s3 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s1 s2
    let out1 := index_mut_back s3
    ok (cont (iter1, out1))

@[rust_loop]
def extract_lane_loop
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) (word_offset : Std.Usize)
  (lane : Std.Usize) (out : Array Std.U8 N) :
  Result (Array Std.U8 N)
  := do
  loop
    (fun (iter1, out1) => extract_lane_loop.body s word_offset lane
      iter1 out1)
    (iter, out)

def extract_lane
  (N : Std.Usize) (s : Array (Array Std.U64 machine.width) 25#usize)
  (word_offset : Std.Usize) (lane : Std.Usize) :
  Result (Array Std.U8 N)
  := do
  let out := Array.repeat N 0#u8
  let i ← N / 8#usize
  extract_lane_loop { start := 0#usize, «end» := i } s
    word_offset lane out

@[rust_loop_body]
def recover_loop0.body
  {N : Std.Usize} (sig : Slice Std.U8) (digits : Slice Std.U32)
  (iter : core.ops.range.Range Std.Usize)
  (endpoints : Array (Array Std.U8 N) 67#usize)
  (rem_steps : Array Std.U32 67#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array Std.U8
    N) 67#usize) × (Array Std.U32 67#usize)) ((Array (Array Std.U8 N)
    67#usize) × (Array Std.U32 67#usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (endpoints, rem_steps))
  | some i =>
    let i1 ← params.W - 1#u32
    let i2 ← Slice.index_usize digits i
    let rem ← i1 - i2
    let (_, index_mut_back) ← Array.index_mut_usize rem_steps i
    if rem = 0#u32
    then
      let a ← util.block N sig i
      let a1 ← Array.update endpoints i a
      let a2 := index_mut_back rem
      ok (cont (iter1, a1, a2))
    else let a := index_mut_back rem
         ok (cont (iter1, endpoints, a))

@[rust_loop]
def recover_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (sig : Slice Std.U8)
  (digits : Slice Std.U32) (endpoints : Array (Array Std.U8 N) 67#usize)
  (rem_steps : Array Std.U32 67#usize) :
  Result ((Array (Array Std.U8 N) 67#usize) × (Array Std.U32 67#usize))
  := do
  loop
    (fun (iter1, endpoints1, rem_steps1) => recover_loop0.body sig
      digits iter1 endpoints1 rem_steps1)
    (iter, endpoints, rem_steps)

@[rust_loop_body]
def recover_loop1_loop0.body
  (lane : Std.Usize) (blk : Slice Std.U8)
  (iter : core.ops.range.Range Std.Usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 4#usize) machine.width)) (Array (Array Std.U64 4#usize) machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done lane_val)
  | some j =>
    let i ← ShakeBatch.shake.batch.word blk j
    let (a, index_mut_back) ← Array.index_mut_usize lane_val lane
    let a1 ← Array.update a j i
    let a2 := index_mut_back a1
    ok (cont (iter1, a2))

@[rust_loop]
def recover_loop1_loop0
  (iter : core.ops.range.Range Std.Usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) (lane : Std.Usize)
  (blk : Slice Std.U8) :
  Result (Array (Array Std.U64 4#usize) machine.width)
  := do
  loop
    (fun (iter1, lane_val1) => recover_loop1_loop0.body lane blk
      iter1 lane_val1)
    (iter, lane_val)

@[rust_loop_body]
def recover_loop1.body
  (N : Std.Usize) (sig : Slice Std.U8) (digits : Slice Std.U32) (n : Std.Usize)
  (order : Array Std.Usize 67#usize) (iter : core.ops.range.Range Std.Usize)
  (next : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × Std.Usize × (Array
    Std.Usize machine.width) × (Array Std.U32 machine.width) × (Array (Array Std.U64
    4#usize) machine.width)) (Std.Usize × (Array Std.Usize machine.width) × (Array
    Std.U32 machine.width) × (Array (Array Std.U64 4#usize) machine.width)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (next, lane_id, lane_step, lane_val))
  | some lane =>
    let id ← Array.index_usize order next
    let next1 ← next + 1#usize
    let a ← Array.update lane_id lane id
    let i ← Slice.index_usize digits id
    let a1 ← Array.update lane_step lane i
    let i1 ← id * N
    let i2 ← id + 1#usize
    let i3 ← i2 * N
    let blk ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := i1, «end» := i3 }
    let lane_val1 ←
      recover_loop1_loop0 { start := 0#usize, «end» := n }
        lane_val lane blk
    ok (cont (iter1, next1, a, a1, lane_val1))

@[rust_loop]
def recover_loop1
  (N : Std.Usize) (iter : core.ops.range.Range Std.Usize) (sig : Slice Std.U8)
  (digits : Slice Std.U32) (n : Std.Usize) (order : Array Std.Usize 67#usize)
  (next : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) :
  Result (Std.Usize × (Array Std.Usize machine.width) × (Array Std.U32 machine.width) ×
    (Array (Array Std.U64 4#usize) machine.width))
  := do
  loop
    (fun (iter1, next1, lane_id1, lane_step1, lane_val1) =>
      recover_loop1.body N sig digits n order iter1 next1 lane_id1
      lane_step1 lane_val1)
    (iter, next, lane_id, lane_step, lane_val)

@[rust_loop_body]
def recover_loop2_loop0_loop0.body
  (offset : Std.Usize) (lane_val : Array (Array Std.U64 4#usize) machine.width)
  (j : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some lane =>
    let a ← Array.index_usize lane_val lane
    let i ← Array.index_usize a j
    let i1 ← offset + j
    let (a1, index_mut_back) ← Array.index_mut_usize state i1
    let a2 ← Array.update a1 lane i
    let a3 := index_mut_back a2
    ok (cont (iter1, a3))

@[rust_loop]
def recover_loop2_loop0_loop0
  (iter : core.ops.range.Range Std.Usize) (offset : Std.Usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width)
  (state : Array (Array Std.U64 machine.width) 25#usize) (j : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => recover_loop2_loop0_loop0.body offset
      lane_val j iter1 state1)
    (iter, state)

@[rust_loop_body]
def recover_loop2_loop0.body
  (offset : Std.Usize) (sw : Array Std.U64 4#usize) (active : Std.Usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width)
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
    let i ← Array.index_usize sw j
    let a := Array.repeat machine.width i
    let a1 ← Array.update state j a
    let state1 ←
      recover_loop2_loop0_loop0
        { start := 0#usize, «end» := active } offset lane_val a1 j
    ok (cont (iter1, state1))

@[rust_loop]
def recover_loop2_loop0
  (iter : core.ops.range.Range Std.Usize) (offset : Std.Usize)
  (sw : Array Std.U64 4#usize) (active : Std.Usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => recover_loop2_loop0.body offset sw
      active lane_val iter1 state1)
    (iter, state)

@[rust_loop_body]
def recover_loop2_loop1.body
  (n : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width) (iter : core.ops.range.Range Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some lane =>
    let i ← Array.index_usize lane_id lane
    let i1 ← lift (UScalar.cast .U32 i)
    let i2 ← core.num.U32.swap_bytes i1
    let i3 ← lift (core.convert.num.FromU64U32.from i2)
    let i4 ← Array.index_usize lane_step lane
    let i5 ← core.num.U32.swap_bytes i4
    let i6 ← lift (core.convert.num.FromU64U32.from i5)
    let i7 ← i6 <<< 32#i32
    let i8 ← n + 3#usize
    let (a, index_mut_back) ← Array.index_mut_usize state i8
    let i9 ← lift (i3 ||| i7)
    let a1 ← Array.update a lane i9
    let a2 := index_mut_back a1
    ok (cont (iter1, a2))

@[rust_loop]
def recover_loop2_loop1
  (iter : core.ops.range.Range Std.Usize) (n : Std.Usize)
  (lane_id : Array Std.Usize machine.width) (lane_step : Array Std.U32 machine.width)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => recover_loop2_loop1.body n lane_id
      lane_step iter1 state1)
    (iter, state)

@[rust_loop_body]
def recover_loop2_loop2.body
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
def recover_loop2_loop2
  (iter : core.slice.iter.IterMut (Array Std.U64 machine.width))
  (back : core.slice.iter.IterMut (Array Std.U64 machine.width) →
  core.slice.iter.IterMut (Array Std.U64 machine.width)) :
  Result ((core.slice.iter.IterMut (Array Std.U64 machine.width)) ×
    (core.slice.iter.IterMut (Array Std.U64 machine.width) →
    core.slice.iter.IterMut (Array Std.U64 machine.width)))
  := do
  loop
    (fun (iter1, back1) => recover_loop2_loop2.body iter1 back1)
    (iter, back)

@[rust_loop_body]
def recover_loop2_loop3_loop0.body
  (lane : Std.Usize) (blk : Slice Std.U8)
  (iter : core.ops.range.Range Std.Usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 4#usize) machine.width)) (Array (Array Std.U64 4#usize) machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done lane_val)
  | some j =>
    let i ← ShakeBatch.shake.batch.word blk j
    let (a, index_mut_back) ← Array.index_mut_usize lane_val lane
    let a1 ← Array.update a j i
    let a2 := index_mut_back a1
    ok (cont (iter1, a2))

@[rust_loop]
def recover_loop2_loop3_loop0
  (iter : core.ops.range.Range Std.Usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) (lane : Std.Usize)
  (blk : Slice Std.U8) :
  Result (Array (Array Std.U64 4#usize) machine.width)
  := do
  loop
    (fun (iter1, lane_val1) => recover_loop2_loop3_loop0.body lane
      blk iter1 lane_val1)
    (iter, lane_val)

@[rust_loop_body]
def recover_loop2_loop3_loop1.body
  (active : Std.Usize) (lane : Std.Usize)
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
    let i ← Array.index_usize a active
    let (a1, index_mut_back) ← Array.index_mut_usize state j
    let a2 ← Array.update a1 lane i
    let a3 := index_mut_back a2
    ok (cont (iter1, a3))

@[rust_loop]
def recover_loop2_loop3_loop1
  (iter : core.ops.range.Range Std.Usize) (active : Std.Usize)
  (state : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, state1) => recover_loop2_loop3_loop1.body active
      lane iter1 state1)
    (iter, state)

@[rust_loop_body]
def recover_loop2_loop3_loop2.body
  (state : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize)
  (iter : core.ops.range.Range Std.Usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 4#usize) machine.width)) (Array (Array Std.U64 4#usize) machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done lane_val)
  | some j =>
    let a ← Array.index_usize state j
    let i ← Array.index_usize a lane
    let (a1, index_mut_back) ← Array.index_mut_usize lane_val lane
    let a2 ← Array.update a1 j i
    let a3 := index_mut_back a2
    ok (cont (iter1, a3))

@[rust_loop]
def recover_loop2_loop3_loop2
  (iter : core.ops.range.Range Std.Usize)
  (lane_val : Array (Array Std.U64 4#usize) machine.width)
  (state : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize) :
  Result (Array (Array Std.U64 4#usize) machine.width)
  := do
  loop
    (fun (iter1, lane_val1) => recover_loop2_loop3_loop2.body state
      lane iter1 lane_val1)
    (iter, lane_val)

@[rust_loop_body]
def recover_loop2_loop3.body
  {N : Std.Usize} (sig : Slice Std.U8) (digits : Slice Std.U32) (n : Std.Usize)
  (order : Array Std.Usize 67#usize) (total : Std.Usize)
  (endpoints : Array (Array Std.U8 N) 67#usize) (next : Std.Usize)
  (active : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width)
  (lane_val : Array (Array Std.U64 4#usize) machine.width)
  (state : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize) :
  Result (ControlFlow ((Array (Array Std.U8 N) 67#usize) × Std.Usize ×
    Std.Usize × (Array Std.Usize machine.width) × (Array Std.U32 machine.width) × (Array
    (Array Std.U64 4#usize) machine.width) × (Array (Array Std.U64 machine.width)
    25#usize) × Std.Usize) ((Array (Array Std.U8 N) 67#usize) × Std.Usize ×
    Std.Usize × (Array Std.Usize machine.width) × (Array Std.U32 machine.width) × (Array
    (Array Std.U64 4#usize) machine.width) × (Array (Array Std.U64 machine.width)
    25#usize)))
  := do
  if lane < active
  then
    let i ← Array.index_usize lane_step lane
    let i1 ← i + 1#u32
    let lane_step1 ← Array.update lane_step lane i1
    let i2 ← Array.index_usize lane_step1 lane
    let i3 ← params.W - 1#u32
    if i2 = i3
    then
      let id ← Array.index_usize lane_id lane
      let a ← extract_lane N state 0#usize lane
      let (_, index_mut_back) ← Array.index_mut_usize endpoints id
      if next < total
      then
        let nid ← Array.index_usize order next
        let next1 ← next + 1#usize
        let a1 ← Array.update lane_id lane nid
        let i4 ← Slice.index_usize digits nid
        let a2 ← Array.update lane_step1 lane i4
        let i5 ← nid * N
        let i6 ← nid + 1#usize
        let i7 ← i6 * N
        let blk ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sig
            { start := i5, «end» := i7 }
        let lane_val1 ←
          recover_loop2_loop3_loop0
            { start := 0#usize, «end» := n } lane_val lane blk
        let lane1 ← lane + 1#usize
        let a3 := index_mut_back a
        ok (cont (a3, next1, active, a1, a2, lane_val1, state, lane1))
      else
        let active1 ← active - 1#usize
        if lane < active1
        then
          let i4 ← Array.index_usize lane_id active1
          let a1 ← Array.update lane_id lane i4
          let i5 ← Array.index_usize lane_step1 active1
          let a2 ← Array.update lane_step1 lane i5
          let state1 ←
            recover_loop2_loop3_loop1
              { start := 0#usize, «end» := n } active1 state lane
          let a3 := index_mut_back a
          ok (cont (a3, next, active1, a1, a2, lane_val, state1, lane))
        else
          let a1 := index_mut_back a
          ok (cont (a1, next, active1, lane_id, lane_step1, lane_val, state,
            lane))
    else
      let lane_val1 ←
        recover_loop2_loop3_loop2
          { start := 0#usize, «end» := n } lane_val state lane
      let lane1 ← lane + 1#usize
      ok (cont (endpoints, next, active, lane_id, lane_step1, lane_val1, state,
        lane1))
  else ok (done (endpoints, next, active, lane_id, lane_step, lane_val, state))

@[rust_loop]
def recover_loop2_loop3
  {N : Std.Usize} (sig : Slice Std.U8) (digits : Slice Std.U32) (n : Std.Usize)
  (endpoints : Array (Array Std.U8 N) 67#usize)
  (order : Array Std.Usize 67#usize) (total : Std.Usize) (next : Std.Usize)
  (active : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width)
  (lane_val : Array (Array Std.U64 4#usize) machine.width)
  (state : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize) :
  Result ((Array (Array Std.U8 N) 67#usize) × Std.Usize × Std.Usize × (Array
    Std.Usize machine.width) × (Array Std.U32 machine.width) × (Array (Array Std.U64
    4#usize) machine.width) × (Array (Array Std.U64 machine.width) 25#usize))
  := do
  loop
    (fun (endpoints1, next1, active1, lane_id1, lane_step1, lane_val1, state1,
      lane1) => recover_loop2_loop3.body sig digits n order total
      endpoints1 next1 active1 lane_id1 lane_step1 lane_val1 state1 lane1)
    (endpoints, next, active, lane_id, lane_step, lane_val, state, lane)

@[rust_loop_body]
def recover_loop2.body
  {N : Std.Usize} (sig : Slice Std.U8) (digits : Slice Std.U32) (n : Std.Usize)
  (offset : Std.Usize) (sw : Array Std.U64 4#usize)
  (aw_hash : Array Std.U64 4#usize) (order : Array Std.Usize 67#usize)
  (total : Std.Usize) (pad : Std.Usize)
  (endpoints : Array (Array Std.U8 N) 67#usize) (next : Std.Usize)
  (active : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width)
  (lane_val : Array (Array Std.U64 4#usize) machine.width)
  (state : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((Array (Array Std.U8 N) 67#usize) × Std.Usize ×
    Std.Usize × (Array Std.Usize machine.width) × (Array Std.U32 machine.width) × (Array
    (Array Std.U64 4#usize) machine.width) × (Array (Array Std.U64 machine.width)
    25#usize)) (Array (Array Std.U8 N) 67#usize))
  := do
  if active > 0#usize
  then
    let state1 ←
      recover_loop2_loop0 { start := 0#usize, «end» := n } offset
        sw active lane_val state
    let i ← Array.index_usize aw_hash 0#usize
    let a := Array.repeat machine.width i
    let state2 ← Array.update state1 n a
    let i1 ← Array.index_usize aw_hash 1#usize
    let i2 ← n + 1#usize
    let a1 := Array.repeat machine.width i1
    let state3 ← Array.update state2 i2 a1
    let i3 ← Array.index_usize aw_hash 2#usize
    let i4 ← n + 2#usize
    let a2 := Array.repeat machine.width i3
    let a3 ← Array.update state3 i4 a2
    let state4 ←
      recover_loop2_loop1 { start := 0#usize, «end» := active } n
        lane_id lane_step a3
    let a4 := Array.repeat machine.width 31#u64
    let state5 ← Array.update state4 pad a4
    let i5 ← pad + 1#usize
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
        state5 { start := i5, «end» := 25#usize }
    let (iter, into_iter_back) ←
      core.slice.Slice.iter_mut s
    let (im, back) ← recover_loop2_loop2 iter (fun im1 => im1)
    let i6 ← 1#u64 <<< 63#i32
    let im1 := back im
    let s1 := into_iter_back im1
    let state6 := index_mut_back s1
    let a5 := Array.repeat machine.width i6
    let state7 ← Array.update state6 16#usize a5
    let state8 ← Dispatch.permute state7 active
    let (endpoints1, next1, active1, lane_id1, lane_step1, lane_val1, state9)
      ←
      recover_loop2_loop3 sig digits n endpoints order total next
        active lane_id lane_step lane_val state8 0#usize
    ok (cont (endpoints1, next1, active1, lane_id1, lane_step1, lane_val1,
      state9))
  else ok (done endpoints)

@[rust_loop]
def recover_loop2
  {N : Std.Usize} (sig : Slice Std.U8) (digits : Slice Std.U32) (n : Std.Usize)
  (offset : Std.Usize) (sw : Array Std.U64 4#usize)
  (aw_hash : Array Std.U64 4#usize)
  (endpoints : Array (Array Std.U8 N) 67#usize)
  (order : Array Std.Usize 67#usize) (total : Std.Usize) (next : Std.Usize)
  (active : Std.Usize) (lane_id : Array Std.Usize machine.width)
  (lane_step : Array Std.U32 machine.width)
  (lane_val : Array (Array Std.U64 4#usize) machine.width)
  (state : Array (Array Std.U64 machine.width) 25#usize) (pad : Std.Usize) :
  Result (Array (Array Std.U8 N) 67#usize)
  := do
  loop
    (fun (endpoints1, next1, active1, lane_id1, lane_step1, lane_val1, state1)
      => recover_loop2.body sig digits n offset sw aw_hash order
      total pad endpoints1 next1 active1 lane_id1 lane_step1 lane_val1 state1)
    (endpoints, next, active, lane_id, lane_step, lane_val, state)

@[rust_loop_body]
def recover_loop3.body
  {N : Std.Usize} (iter : core.slice.iter.Iter (Array Std.U8 N))
  (pk : stream.State) :
  Result (ControlFlow ((core.slice.iter.Iter (Array Std.U8 N)) ×
    stream.State) stream.State)
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done pk)
  | some key =>
    let s ← lift (Array.to_slice key)
    let pk1 ← stream.absorb pk s
    ok (cont (iter1, pk1))

@[rust_loop]
def recover_loop3
  {N : Std.Usize} (iter : core.slice.iter.Iter (Array Std.U8 N))
  (pk : stream.State) :
  Result stream.State
  := do
  loop
    (fun (iter1, pk1) => recover_loop3.body iter1 pk1)
    (iter, pk)

def recover
  {N : Std.Usize} (sig : Slice Std.U8) (seed : Array Std.U8 N)
  (addr : address.Adrs) (digits : Slice Std.U32) :
  Result (Array Std.U8 N)
  := do
  let len := Slice.len digits
  let n ← N / 8#usize
  let offset ← n + 4#usize
  let sw ← NativeVerify.seed_words seed
  let a ← address.Adrs.with_type addr address.WOTS_HASH
  let a1 ← address.Adrs.with_keypair a addr.keypair
  let aw_hash ← NativeVerify.adrs_words a1
  let a2 := Array.repeat N 0#u8
  let endpoints := Array.repeat 67#usize a2
  let rem_steps := Array.repeat 67#usize 0#u32
  let (endpoints1, rem_steps1) ←
    recover_loop0 { start := 0#usize, «end» := len } sig digits
      endpoints rem_steps
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) rem_steps1
      { «end» := len }
  let (order, total) ← ShakeoptSort.shake.batch.sort_descending s
  let i ← ok machine.width
  let active ← lift (core.cmp.impls.OrdUsize.min total i)
  let lane_id := Array.repeat machine.width 0#usize
  let lane_step := Array.repeat machine.width 0#u32
  let a3 := Array.repeat 4#usize 0#u64
  let lane_val := Array.repeat machine.width a3
  let (next, lane_id1, lane_step1, lane_val1) ←
    recover_loop1 N { start := 0#usize, «end» := active } sig
      digits n order 0#usize lane_id lane_step lane_val
  let a4 := Array.repeat machine.width 0#u64
  let state := Array.repeat 25#usize a4
  let pad ← offset + n
  let endpoints2 ←
    recover_loop2 sig digits n offset sw aw_hash endpoints1 order
      total next active lane_id1 lane_step1 lane_val1 state pad
  let a5 ← address.Adrs.with_type addr address.WOTS_PK
  let a6 ← address.Adrs.with_keypair a5 addr.keypair
  let pk ← stream.start seed a6
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N)))
      endpoints2 { «end» := len }
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s1
  let pk1 ← recover_loop3 iter pk
  stream.digest N pk1

end
end slhdsa.NativeVerify.Wots
