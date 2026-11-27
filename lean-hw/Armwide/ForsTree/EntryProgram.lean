import Armwide.ForsTree.Top
import Armwide.KeyDispatch
import Armplatform.Internal
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.ArmForsTree.Entry
open Armwide.Public.Dispatcher (Cpu)
open Armwide.Keygen (Features)
noncomputable section
variable [cpu : Cpu] [features : Features]

abbrev sha256.arm_wide.available [c : Cpu] := @Armwide.Public.Dispatcher.sha256.arm_wide.available c
abbrev fors.arm.subtree [f : Features] {N : Usize} := @ArmForsTree.fors.arm.subtree f.sha512 N
abbrev fors.fors_batch_loop0 {N : Usize} := @slhdsa.fors.fors_batch_loop0 N
abbrev fors.fors_batch_loop1 := slhdsa.fors.fors_batch_loop1
abbrev fors.fors_batch_loop2 {N : Usize} := @slhdsa.fors.fors_batch_loop2 N
abbrev fors.fors_batch_loop3 {N : Usize} := @PlatformFors.armTreeLoop N
abbrev fors.fors_batch_loop4 {N : Usize} := @slhdsa.fors.fors_batch_loop0 N
abbrev fors.fors_batch_loop5 := slhdsa.fors.fors_batch_loop1
abbrev fors.fors_batch_loop6 {N : Usize} := @slhdsa.fors.fors_batch_loop2 N
abbrev fors.fors_batch_loop7 {N : Usize} := @PlatformFors.armTreeLoop N

def fors.fors_batch
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (i : Std.U32) (z : Std.U32)
  (seed : hash.Seed N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
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
    then fors.arm.subtree sk_seed i z seed adrs
    else
      let n ← 1#usize <<< z
      let a ← address.Adrs.with_type adrs address.FORS_PRF
      let prf_adrs ← address.Adrs.with_keypair a adrs.keypair
      let a1 := Array.repeat 64#usize 0#u8
      let blocks := Array.repeat 128#usize a1
      let start := Array.repeat 128#usize 0#u32
      let «end» := Array.repeat 128#usize 0#u32
      let (blocks1, start1, end1) ←
        fors.fors_batch_loop0 sk_seed i z n prf_adrs blocks start «end»
          0#usize
      let (s, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
          blocks1 { start := 0#usize, «end» := n }
      let s1 ← lift (Array.to_slice start1)
      let s2 ← lift (Array.to_slice end1)
      let s3 ← hash.chain_blocks N seed.state s s1 s2
      let blocks2 := index_mut_back s3
      let blocks3 ← fors.fors_batch_loop1 adrs.typ n blocks2 0#usize
      let (s4, index_mut_back1) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
          blocks3 { start := 0#usize, «end» := n }
      let s5 ← lift (Array.to_slice start1)
      let s6 ← lift (Array.to_slice end1)
      let s7 ← hash.chain_blocks N seed.state s4 s5 s6
      let a2 := Array.repeat N 0#u8
      let vals := Array.repeat 128#usize a2
      let blocks4 := index_mut_back1 s7
      let vals1 ← fors.fors_batch_loop2 n blocks4 vals 0#usize
      let cnt ← n / 2#usize
      let vals2 ←
        fors.fors_batch_loop3 i z seed.pk_seed seed.state seed.state512
          adrs.layer adrs.tree adrs.typ adrs.keypair adrs.word2 adrs.word3
          blocks4 start1 end1 vals1 1#u32 cnt
      Array.index_usize vals2 0#usize
  else
    let n ← 1#usize <<< z
    let a ← address.Adrs.with_type adrs address.FORS_PRF
    let prf_adrs ← address.Adrs.with_keypair a adrs.keypair
    let a1 := Array.repeat 64#usize 0#u8
    let blocks := Array.repeat 128#usize a1
    let start := Array.repeat 128#usize 0#u32
    let «end» := Array.repeat 128#usize 0#u32
    let (blocks1, start1, end1) ←
      fors.fors_batch_loop4 sk_seed i z n prf_adrs blocks start «end» 0#usize
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
        blocks1 { start := 0#usize, «end» := n }
    let s1 ← lift (Array.to_slice start1)
    let s2 ← lift (Array.to_slice end1)
    let s3 ← hash.chain_blocks N seed.state s s1 s2
    let blocks2 := index_mut_back s3
    let blocks3 ← fors.fors_batch_loop5 adrs.typ n blocks2 0#usize
    let (s4, index_mut_back1) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
        blocks3 { start := 0#usize, «end» := n }
    let s5 ← lift (Array.to_slice start1)
    let s6 ← lift (Array.to_slice end1)
    let s7 ← hash.chain_blocks N seed.state s4 s5 s6
    let a2 := Array.repeat N 0#u8
    let vals := Array.repeat 128#usize a2
    let blocks4 := index_mut_back1 s7
    let vals1 ← fors.fors_batch_loop6 n blocks4 vals 0#usize
    let cnt ← n / 2#usize
    let vals2 ←
      fors.fors_batch_loop7 i z seed.pk_seed seed.state seed.state512
        adrs.layer adrs.tree adrs.typ adrs.keypair adrs.word2 adrs.word3
        blocks4 start1 end1 vals1 1#u32 cnt
    Array.index_usize vals2 0#usize

def fors.fors_node
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (i : Std.U32) (z : Std.U32)
  (seed : hash.Seed N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  if z <= fors.BATCH_HEIGHT
  then fors.fors_batch sk_seed i z seed adrs
  else
    let i1 ← 2#u32 * i
    let i2 ← z - 1#u32
    let lnode ← fors.fors_node sk_seed i1 i2 seed adrs
    let i3 ← i1 + 1#u32
    let rnode ← fors.fors_node sk_seed i3 i2 seed adrs
    let a ← address.Adrs.with_word2 adrs z
    let a1 ← address.Adrs.with_word3 a i
    xmss.hash2 seed a1 lnode rnode
partial_fixpoint

@[rust_loop_body]
def fors.fors_sign_loop0_loop0.body
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (seed : hash.Seed N)
  (adrs : address.Adrs) (a : Std.U32) (i : Std.U32) (idx : Std.U32)
  (sig : alloc.vec.Vec Std.U8) (j : Std.U32) :
  Result (ControlFlow ((alloc.vec.Vec Std.U8) × Std.U32) (alloc.vec.Vec
    Std.U8))
  := do
  if j < a
  then
    let i1 ← idx >>> j
    let s ← lift (i1 ^^^ 1#u32)
    let i2 ← a - j
    let i3 ← i <<< i2
    let i4 ← i3 + s
    let node ← fors.fors_node sk_seed i4 j seed adrs
    let s1 ← lift (Array.to_slice node)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s1
    let j1 ← j + 1#u32
    ok (cont (sig1, j1))
  else ok (done sig)


@[rust_loop]
def fors.fors_sign_loop0_loop0
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (seed : hash.Seed N)
  (adrs : address.Adrs) (a : Std.U32) (sig : alloc.vec.Vec Std.U8)
  (i : Std.U32) (idx : Std.U32) (j : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (sig1, j1) => fors.fors_sign_loop0_loop0.body sk_seed seed adrs a i
      idx sig1 j1)
    (sig, j)


@[rust_loop_body]
def fors.fors_sign_loop0.body
  {N : Std.Usize} (i : Std.U32) (sk_seed : Array Std.U8 N) (seed : hash.Seed N)
  (adrs : address.Adrs) (a : Std.U32) (indices : alloc.vec.Vec Std.U32)
  (sig : alloc.vec.Vec Std.U8) (i1 : Std.U32) :
  Result (ControlFlow ((alloc.vec.Vec Std.U8) × Std.U32) (alloc.vec.Vec
    Std.U8))
  := do
  if i1 < i
  then
    let i2 ← lift (UScalar.cast .Usize i1)
    let idx ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32)
        indices i2
    let i3 ← i1 <<< a
    let i4 ← i3 + idx
    let sk ← fors.fors_sk_gen sk_seed seed adrs i4
    let s ← lift (Array.to_slice sk)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
    let sig2 ←
      fors.fors_sign_loop0_loop0 sk_seed seed adrs a sig1 i1 idx 0#u32
    let i5 ← i1 + 1#u32
    ok (cont (sig2, i5))
  else ok (done sig)


@[rust_loop]
def fors.fors_sign_loop0
  {N : Std.Usize} (i : Std.U32) (sk_seed : Array Std.U8 N) (seed : hash.Seed N)
  (adrs : address.Adrs) (a : Std.U32) (indices : alloc.vec.Vec Std.U32)
  (sig : alloc.vec.Vec Std.U8) (i1 : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (sig1, i2) => fors.fors_sign_loop0.body i sk_seed seed adrs a indices
      sig1 i2)
    (sig, i1)


def fors.fors_sign
  {N : Std.Usize} (p : params.Params) (md : Slice Std.U8)
  (sk_seed : Array Std.U8 N) (seed : hash.Seed N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let i ← lift (UScalar.cast .Usize p.k)
  let indices ← util.base_2b md p.a i
  fors.fors_sign_loop0 p.k sk_seed seed adrs p.a indices (alloc.vec.Vec.new
    Std.U8) 0#u32


end
end slhdsa.ArmForsTree.Entry
