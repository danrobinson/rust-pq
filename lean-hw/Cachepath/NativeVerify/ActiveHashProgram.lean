import Cachepath.NativeVerify.Words
import Cachepath.NativeVerify.Active
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeVerify.ActiveHash
open ShakeBatch
variable [machine : Machine] (permute : Active machine)
@[rust_loop_body]
def header_active_loop0.body
  (sw : Array Std.U64 4#usize) (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array (Array
    Std.U64 machine.width) 25#usize)) (Array (Array Std.U64 machine.width) 25#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done s)
  | some i =>
    let i1 ← Array.index_usize sw i
    let a := Array.repeat machine.width i1
    let a1 ← Array.update s i a
    ok (cont (iter1, a1))

@[rust_loop]
def header_active_loop0
  (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) (sw : Array Std.U64 4#usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, s1) => header_active_loop0.body sw iter1 s1)
    (iter, s)

@[rust_loop_body]
def header_active_loop1_loop0.body
  (i : Std.Usize) (lane : Std.Usize) (aw : Array Std.U64 4#usize)
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
    let i1 ← Array.index_usize aw j
    let i2 ← i + j
    let (a, index_mut_back) ← Array.index_mut_usize s i2
    let a1 ← Array.update a lane i1
    let a2 := index_mut_back a1
    ok (cont (iter1, a2))

@[rust_loop]
def header_active_loop1_loop0
  (i : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) (lane : Std.Usize)
  (aw : Array Std.U64 4#usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, s1) => header_active_loop1_loop0.body i lane aw
      iter1 s1)
    (iter, s)

@[rust_loop_body]
def header_active_loop1.body
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
    let aw ← NativeVerify.adrs_words a
    let s1 ←
      header_active_loop1_loop0 i
        { start := 0#usize, «end» := 4#usize } s lane aw
    ok (cont (iter1, s1))

@[rust_loop]
def header_active_loop1
  (i : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (addresses : Array address.Adrs machine.width)
  (s : Array (Array Std.U64 machine.width) 25#usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, s1) => header_active_loop1.body i addresses iter1
      s1)
    (iter, s)

@[rust_loop_body]
def header_active_loop2.body
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
def header_active_loop2
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1) => header_active_loop2.body iter1 back1)
    (iter, back)

def header_active
  {N : Std.Usize} (seed : Array Std.U8 N)
  (addresses : Array address.Adrs machine.width) (size : Std.Usize)
  (active : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  let a := Array.repeat machine.width 0#u64
  let s := Array.repeat 25#usize a
  let sw ← NativeVerify.seed_words seed
  let i ← N / 8#usize
  let s1 ←
    header_active_loop0 { start := 0#usize, «end» := i } s sw
  let s2 ←
    header_active_loop1 i { start := 0#usize, «end» := active }
      addresses s1
  let i1 ← size / 8#usize
  let a1 := Array.repeat machine.width 31#u64
  let s3 ← Array.update s2 i1 a1
  let (a2, index_mut_back) ← Array.index_mut_usize s3 16#usize
  let (iter, into_iter_back) ←
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter a2
  let (im, back) ← header_active_loop2 iter (fun im1 => im1)
  let im1 := back im
  let a3 := into_iter_back im1
  ok (index_mut_back a3)

@[rust_loop_body]
def put_active_loop0_loop0.body
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
    let i1 ← ShakeBatch.shake.batch.word s1 i
    let i2 ← offset + i
    let (a1, index_mut_back) ← Array.index_mut_usize s i2
    let a2 ← Array.update a1 lane i1
    let a3 := index_mut_back a2
    ok (cont (iter1, a3))

@[rust_loop]
def put_active_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) (offset : Std.Usize)
  (values : Array (Array Std.U8 N) machine.width) (i : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, s1) => put_active_loop0_loop0.body offset values i
      iter1 s1)
    (iter, s)

@[rust_loop_body]
def put_active_loop0.body
  {N : Std.Usize} (offset : Std.Usize)
  (values : Array (Array Std.U8 N) machine.width) (active : Std.Usize)
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
      put_active_loop0_loop0
        { start := 0#usize, «end» := active } s offset values i
    ok (cont (iter1, s1))

@[rust_loop]
def put_active_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) (offset : Std.Usize)
  (values : Array (Array Std.U8 N) machine.width) (active : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  loop
    (fun (iter1, s1) => put_active_loop0.body offset values active
      iter1 s1)
    (iter, s)

def put_active
  {N : Std.Usize} (s : Array (Array Std.U64 machine.width) 25#usize)
  (offset : Std.Usize) (values : Array (Array Std.U8 N) machine.width)
  (active : Std.Usize) :
  Result (Array (Array Std.U64 machine.width) 25#usize)
  := do
  let i ← N / 8#usize
  put_active_loop0 { start := 0#usize, «end» := i } s offset
    values active

@[rust_loop_body]
def read_active_loop0_loop0.body
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
def read_active_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize)
  (values : Array (Array Std.U8 N) machine.width) (i : Std.Usize) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  loop
    (fun (iter1, values1) => read_active_loop0_loop0.body s i iter1
      values1)
    (iter, values)

@[rust_loop_body]
def read_active_loop0.body
  {N : Std.Usize} (s : Array (Array Std.U64 machine.width) 25#usize)
  (active : Std.Usize) (iter : core.ops.range.Range Std.Usize)
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
      read_active_loop0_loop0
        { start := 0#usize, «end» := active } s values i
    ok (cont (iter1, values1))

@[rust_loop]
def read_active_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (s : Array (Array Std.U64 machine.width) 25#usize) (active : Std.Usize)
  (values : Array (Array Std.U8 N) machine.width) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  loop
    (fun (iter1, values1) => read_active_loop0.body s active iter1
      values1)
    (iter, values)

def read_active
  (N : Std.Usize) (s : Array (Array Std.U64 machine.width) 25#usize)
  (active : Std.Usize) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let a := Array.repeat N 0#u8
  let values := Array.repeat machine.width a
  let i ← N / 8#usize
  read_active_loop0 { start := 0#usize, «end» := i } s active
    values

def short_active
  {N : Std.Usize} (seed : Array Std.U8 N)
  (addresses : Array address.Adrs machine.width)
  (values : Array (Array Std.U8 N) machine.width) (active : Std.Usize) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let i ← 2#usize * N
  let i1 ← i + 32#usize
  let s ← header_active seed addresses i1 active
  let i2 ← N / 8#usize
  let i3 ← i2 + 4#usize
  let s1 ← put_active s i3 values active
  let s2 ← permute s1 active
  read_active N s2 active

def pair_active
  {N : Std.Usize} (seed : Array Std.U8 N)
  (addresses : Array address.Adrs machine.width)
  (left : Array (Array Std.U8 N) machine.width)
  (right : Array (Array Std.U8 N) machine.width) (active : Std.Usize) :
  Result (Array (Array Std.U8 N) machine.width)
  := do
  let i ← 3#usize * N
  let i1 ← i + 32#usize
  let s ← header_active seed addresses i1 active
  let i2 ← N / 8#usize
  let i3 ← i2 + 4#usize
  let s1 ← put_active s i3 left active
  let i4 ← 2#usize * N
  let i5 ← i4 / 8#usize
  let i6 ← i5 + 4#usize
  let s2 ← put_active s1 i6 right active
  let s3 ← permute s2 active
  read_active N s3 active
end slhdsa.NativeVerify.ActiveHash
