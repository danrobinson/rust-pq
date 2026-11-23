import Slhdsa.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
open slhdsa
namespace slhdsa.ShakeBatch
abbrev Matrix (width : Usize) := Array (Array U64 width) 25#usize
class Machine where
  width : Usize
  permute : Matrix width → Result (Matrix width)
set_option linter.concreteInstances false
variable [machine : Machine]

def shake.batch.word
  (input : Slice Std.U8) (i : Std.Usize) : Result Std.U64 := do
  let i1 ← i * 8#usize
  let i2 ← i1 + 8#usize
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) input { start := i1, «end» := i2 }
  let r ←
    core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s
  let a ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  ok (core.num.U64.from_le_bytes a)

@[rust_loop_body]
def shake.batch.header_loop0.body
  {N : Std.Usize} (seed : Array Std.U8 N)
  (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done s)
  | some i =>
    let s1 ← lift (Array.to_slice seed)
    let i1 ← shake.batch.word s1 i
    let a := Array.repeat machine.width i1
    let a1 ← Array.update s i a
    ok (cont (iter1, a1))

@[rust_loop]
def shake.batch.header_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (seed : Array Std.U8 N) (s : Array (Array Std.U64 machine.width) 25#usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, s1) => shake.batch.header_loop0.body seed iter1 s1)
    (iter, s)

@[rust_loop_body]
def shake.batch.header_loop1_loop0.body
  (i : Std.Usize) (lane : Std.Usize) (addr : Array Std.U8 32#usize)
  (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done s)
  | some j =>
    let s1 ← lift (Array.to_slice addr)
    let i1 ← shake.batch.word s1 j
    let i2 ← i + j
    let (a, index_mut_back) ← Array.index_mut_usize s i2
    let a1 ← Array.update a lane i1
    let a2 := index_mut_back a1
    ok (cont (iter1, a2))

@[rust_loop]
def shake.batch.header_loop1_loop0
  (i : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize)
  (addr : Array Std.U8 32#usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, s1) => shake.batch.header_loop1_loop0.body i lane addr iter1
      s1)
    (iter, s)

@[rust_loop_body]
def shake.batch.header_loop1.body
  (i : Std.Usize) (addresses : Array address.Adrs machine.width)
  (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done s)
  | some lane =>
    let a ← Array.index_usize addresses lane
    let addr ← address.Adrs.full a
    let s1 ←
      shake.batch.header_loop1_loop0 i { start := 0#usize, «end» := 4#usize }
        s lane addr
    ok (cont (iter1, s1))

@[rust_loop]
def shake.batch.header_loop1
  (i : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (addresses : Array address.Adrs machine.width)
  (s : Array (Array Std.U64 machine.width) 25#usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, s1) => shake.batch.header_loop1.body i addresses iter1 s1)
    (iter, s)

@[rust_loop_body]
def shake.batch.header_loop2.body
  (iter : core.slice.iter.IterMut Std.U64)
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
    let i ← 1#u64 <<< 63#i32
    let v1 ← lift (v ||| i)
    ok (cont (iter1, fun im => let im1 := next_back im (some v1)
                               back im1))

@[rust_loop]
def shake.batch.header_loop2
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1) => shake.batch.header_loop2.body iter1 back1)
    (iter, back)

def shake.batch.header
  {N : Std.Usize} (seed : Array Std.U8 N)
  (addresses : Array address.Adrs machine.width) (size : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  let a := Array.repeat machine.width 0#u64
  let s := Array.repeat 25#usize a
  let i ← N / 8#usize
  let s1 ← shake.batch.header_loop0 { start := 0#usize, «end» := i } seed s
  let s2 ←
    shake.batch.header_loop1 i
      { start := 0#usize, «end» := machine.width } addresses s1
  let i1 ← size / 8#usize
  let a1 := Array.repeat machine.width 31#u64
  let s3 ← Array.update s2 i1 a1
  let (a2, index_mut_back) ← Array.index_mut_usize s3 16#usize
  let (iter, into_iter_back) ←
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter a2
  let (im, back) ← shake.batch.header_loop2 iter (fun im1 => im1)
  let im1 := back im
  let a3 := into_iter_back im1
  ok (index_mut_back a3)

@[rust_loop_body]
def shake.batch.put_loop0_loop0.body
  {N : Std.Usize} (offset : Std.Usize)
  (values : Array (Array Std.U8 N) machine.width) (i : Std.Usize)
  (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done s)
  | some lane =>
    let a ← Array.index_usize values lane
    let s1 ← lift (Array.to_slice a)
    let i1 ← shake.batch.word s1 i
    let i2 ← offset + i
    let (a1, index_mut_back) ← Array.index_mut_usize s i2
    let a2 ← Array.update a1 lane i1
    let a3 := index_mut_back a2
    ok (cont (iter1, a3))

@[rust_loop]
def shake.batch.put_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) (offset : Std.Usize)
  (values : Array (Array Std.U8 N) machine.width) (i : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, s1) => shake.batch.put_loop0_loop0.body offset values i iter1
      s1)
    (iter, s)

@[rust_loop_body]
def shake.batch.put_loop0.body
  {N : Std.Usize} (offset : Std.Usize)
  (values : Array (Array Std.U8 N) machine.width)
  (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done s)
  | some i =>
    let s1 ←
      shake.batch.put_loop0_loop0
        { start := 0#usize, «end» := machine.width } s offset
        values i
    ok (cont (iter1, s1))

@[rust_loop]
def shake.batch.put_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) (offset : Std.Usize)
  (values : Array (Array Std.U8 N) machine.width) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, s1) => shake.batch.put_loop0.body offset values iter1 s1)
    (iter, s)

def shake.batch.put
  {N : Std.Usize} (s : Array (Array Std.U64 machine.width) 25#usize)
  (offset : Std.Usize) (values : Array (Array Std.U8 N) machine.width) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  let i ← N / 8#usize
  shake.batch.put_loop0 { start := 0#usize, «end» := i } s offset values

@[rust_loop_body]
def shake.batch.read_loop0_loop0.body
  {N : Std.Usize} (s : Array (Array Std.U64 machine.width) 25#usize) (i : Std.Usize)
  (iter : core.ops.range.Range Std.Usize)
  (values : Array (Array Std.U8 N) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array Std.U8
    N) machine.width)) (Array (Array Std.U8 N) machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done values)
  | some lane =>
    let (a, index_mut_back) ← Array.index_mut_usize values lane
    let i1 ← 8#usize * i
    let i2 ← i1 + 8#usize
    let (s1, index_mut_back1) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a
        { start := i1, «end» := i2 }
    let a1 ← Array.index_usize s i
    let i3 ← Array.index_usize a1 lane
    let a2 ← lift (core.num.U64.to_le_bytes i3)
    let s2 ← lift (Array.to_slice a2)
    let s3 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s1 s2
    let a3 := index_mut_back1 s3
    let a4 := index_mut_back a3
    ok (cont (iter1, a4))

@[rust_loop]
def shake.batch.read_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize)
  (values : Array (Array Std.U8 N) machine.width) (i : Std.Usize) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  loop
    (fun (iter1, values1) => shake.batch.read_loop0_loop0.body s i iter1
      values1)
    (iter, values)

@[rust_loop_body]
def shake.batch.read_loop0.body
  {N : Std.Usize} (s : Array (Array Std.U64 machine.width) 25#usize)
  (iter : core.ops.range.Range Std.Usize)
  (values : Array (Array Std.U8 N) machine.width) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array Std.U8
    N) machine.width)) (Array (Array Std.U8 N) machine.width))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done values)
  | some i =>
    let values1 ←
      shake.batch.read_loop0_loop0
        { start := 0#usize, «end» := machine.width } s values i
    ok (cont (iter1, values1))

@[rust_loop]
def shake.batch.read_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize)
  (values : Array (Array Std.U8 N) machine.width) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  loop
    (fun (iter1, values1) => shake.batch.read_loop0.body s iter1 values1)
    (iter, values)

def shake.batch.read
  (N : Std.Usize) (s : Array (Array Std.U64 machine.width) 25#usize) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let a := Array.repeat N 0#u8
  let values := Array.repeat machine.width a
  let i ← N / 8#usize
  shake.batch.read_loop0 { start := 0#usize, «end» := i } s values

def shake.batch.short
  {N : Std.Usize} (seed : Array Std.U8 N)
  (addresses : Array address.Adrs machine.width)
  (values : Array (Array Std.U8 N) machine.width) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let i ← 2#usize * N
  let i1 ← i + 32#usize
  let s ← shake.batch.header seed addresses i1
  let i2 ← N / 8#usize
  let i3 ← i2 + 4#usize
  let s1 ← shake.batch.put s i3 values
  let s2 ← machine.permute s1
  shake.batch.read N s2

def shake.batch.pair
  {N : Std.Usize} (seed : Array Std.U8 N)
  (addresses : Array address.Adrs machine.width)
  (left : Array (Array Std.U8 N) machine.width)
  (right : Array (Array Std.U8 N) machine.width) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let i ← 3#usize * N
  let i1 ← i + 32#usize
  let s ← shake.batch.header seed addresses i1
  let i2 ← N / 8#usize
  let i3 ← i2 + 4#usize
  let s1 ← shake.batch.put s i3 left
  let i4 ← 2#usize * N
  let i5 ← i4 / 8#usize
  let i6 ← i5 + 4#usize
  let s2 ← shake.batch.put s1 i6 right
  let s3 ← machine.permute s2
  shake.batch.read N s3
end slhdsa.ShakeBatch
