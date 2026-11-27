import Armwide.NativeWots
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.Armwide.Public.Dispatcher

class Cpu where
  wide : Bool

def sha256.arm_wide.available [cpu : Cpu] : Result Bool := ok cpu.wide

section
variable [Cpu]
@[rust_loop_body]
def wots.wots_sign_loop0.body
  (N : Std.Usize) (len : Std.Usize)
  (blocks : Array (Array Std.U8 64#usize) 67#usize)
  (sig : alloc.vec.Vec Std.U8) (i : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec Std.U8) × Std.Usize) (alloc.vec.Vec
    Std.U8))
  := do
  if i < len
  then
    let a ← Array.index_usize blocks i
    let i1 ← 22#usize + N
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a
        { start := 22#usize, «end» := i1 }
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
    let i2 ← i + 1#usize
    ok (cont (sig1, i2))
  else ok (done sig)

@[rust_loop]
def wots.wots_sign_loop0
  (N : Std.Usize) (len : Std.Usize)
  (blocks : Array (Array Std.U8 64#usize) 67#usize)
  (sig : alloc.vec.Vec Std.U8) (i : Std.Usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (sig1, i1) => wots.wots_sign_loop0.body N len blocks sig1 i1)
    (sig, i)

@[rust_loop_body]
def wots.wots_sign_loop1.body
  (N : Std.Usize) (len : Std.Usize)
  (blocks : Array (Array Std.U8 64#usize) 67#usize)
  (sig : alloc.vec.Vec Std.U8) (i : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec Std.U8) × Std.Usize) (alloc.vec.Vec
    Std.U8))
  := do
  if i < len
  then
    let a ← Array.index_usize blocks i
    let i1 ← 22#usize + N
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a
        { start := 22#usize, «end» := i1 }
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
    let i2 ← i + 1#usize
    ok (cont (sig1, i2))
  else ok (done sig)

@[rust_loop]
def wots.wots_sign_loop1
  (N : Std.Usize) (len : Std.Usize)
  (blocks : Array (Array Std.U8 64#usize) 67#usize)
  (sig : alloc.vec.Vec Std.U8) (i : Std.Usize) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (sig1, i1) => wots.wots_sign_loop1.body N len blocks sig1 i1)
    (sig, i)

def wots.wots_sign
  {N : Std.Usize} (m : Array Std.U8 N) (sk_seed : Array Std.U8 N)
  (seed : hash.Seed N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let b ←
    match N.val with
    | 16 => ok true
    | 24 => ok true
    | 32 => ok true
    | _ => ok false
  if b
  then
    let b1 ← sha256.arm_wide.available
    if b1
    then wots.arm.sign m sk_seed seed adrs
    else
      let i ← 2#usize * N
      let len ← i + params.LEN2
      let msg ← wots.wots_digits m
      let blocks ← wots.sk_blocks sk_seed seed adrs
      let (s, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
          blocks { start := 0#usize, «end» := len }
      let a := Array.repeat 67#usize 0#u32
      let s1 ← lift (Array.to_slice a)
      let s2 := alloc.vec.Vec.deref msg
      let s3 ← hash.chain_blocks N seed.state s s1 s2
      let blocks1 := index_mut_back s3
      wots.wots_sign_loop0 N len blocks1 (alloc.vec.Vec.new Std.U8) 0#usize
  else
    let i ← 2#usize * N
    let len ← i + params.LEN2
    let msg ← wots.wots_digits m
    let blocks ← wots.sk_blocks sk_seed seed adrs
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
        blocks { start := 0#usize, «end» := len }
    let a := Array.repeat 67#usize 0#u32
    let s1 ← lift (Array.to_slice a)
    let s2 := alloc.vec.Vec.deref msg
    let s3 ← hash.chain_blocks N seed.state s s1 s2
    let blocks1 := index_mut_back s3
    wots.wots_sign_loop1 N len blocks1 (alloc.vec.Vec.new Std.U8) 0#usize
end
end slhdsa.Armwide.Public.Dispatcher
