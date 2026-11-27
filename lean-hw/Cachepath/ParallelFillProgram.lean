import Cachepath.BuilderParallelProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.cache.builder.workers.fill
set_option linter.concreteInstances false

@[rust_loop_body]
def sha2Batch_loop.body
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (seed : hash.Seed N)
  (adrs : address.Adrs) (iter : core.ops.range.Range Std.Usize)
  (out : alloc.vec.Vec (Array Std.U8 N)) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    (Array Std.U8 N))) (alloc.vec.Vec (Array Std.U8 N)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some i =>
    let a ← address.Adrs.with_type adrs address.WOTS_HASH
    let i1 ← lift (UScalar.cast .U32 i)
    let a1 ← address.Adrs.with_keypair a i1
    let a2 ← wots.wots_pk_gen sk_seed seed a1
    let out1 ← alloc.vec.Vec.push out a2
    ok (cont (iter1, out1))

@[rust_loop]
def sha2Batch_loop
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (sk_seed : Array Std.U8 N) (seed : hash.Seed N) (adrs : address.Adrs)
  (out : alloc.vec.Vec (Array Std.U8 N)) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, out1) => sha2Batch_loop.body sk_seed
      seed adrs iter1 out1)
    (iter, out)

def sha2Batch
  {N : Std.Usize} (start : Std.Usize) («end» : Std.Usize)
  (sk_seed : Array Std.U8 N) (seed : hash.Seed N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  let i ← «end» - start
  let out := alloc.vec.Vec.with_capacity (Array Std.U8 N) i
  sha2Batch_loop { start, «end» } sk_seed seed adrs out

def shakeBatch [nativeShake.Backend]
  {N : Std.Usize} (start : Std.Usize) («end» : Std.Usize)
  (sk_seed : Array Std.U8 N) (pk_seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  let a := Array.repeat N 0#u8
  let i ← «end» - start
  let out ←
    alloc.vec.from_elem (core.clone.CloneArray N core.clone.CloneU8) a i
  let (s, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut out)
  let s1 ← nativeShake.fill_leaves_chunk sk_seed pk_seed adrs start s
  ok (deref_mut_back s1)

def runtimePlan
  (num_leaves : Std.Usize) (threads : Std.Usize) :
  Result (Option (Std.Usize × Std.Usize))
  := do
  if num_leaves < 16#usize
  then ok none
  else
    let i ← num_leaves / 4#usize
    let workers ← lift (core.cmp.impls.OrdUsize.min threads i)
    if workers < 2#usize
    then ok none
    else
      let i1 ← workers * 4#usize
      let i2 ← num_leaves / i1
      let chunk ← lift (core.cmp.impls.OrdUsize.max i2 4#usize)
      let i3 ← num_leaves + chunk
      let i4 ← i3 - 1#usize
      let num_chunks ← i4 / chunk
      ok (some (chunk, num_chunks))

end slhdsa.cache.builder.workers.fill
