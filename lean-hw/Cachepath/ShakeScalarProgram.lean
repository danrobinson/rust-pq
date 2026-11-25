import Cacheops.Funs

/-! Scalar WOTS and FORS callers from the production cache. The extractor checks
the complete definitions on every target. Runtime dispatch remains a parameter. -/
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.CacheScalar

class Acceleration where
  available (N : Std.Usize) : Result Bool
  wots_sign {N : Usize} : Array U8 N → Array U8 N → address.Adrs → Slice U32 →
    Result (alloc.vec.Vec U8)
  wots_pk_from_sig {N : Usize} : Slice U8 → Array U8 N → address.Adrs →
    Slice U32 → Result (Array U8 N)
  fors_sign {N : Usize} : params.Params → Slice U32 → Array U8 N → Array U8 N →
    address.Adrs → Result (alloc.vec.Vec U8)
  fors_pk_from_sig {N : Usize} : params.Params → Slice U32 → Slice U8 → Array U8 N →
    address.Adrs → Result (Array U8 N)

set_option linter.concreteInstances false
variable [Acceleration]

abbrev cache.shake_ops.simd.available := @Acceleration.available _
abbrev cache.shake_ops.simd.wots_sign := @Acceleration.wots_sign _
abbrev cache.shake_ops.simd.wots_pk_from_sig := @Acceleration.wots_pk_from_sig _
abbrev cache.shake_ops.simd.fors_sign := @Acceleration.fors_sign _
abbrev cache.shake_ops.simd.fors_pk_from_sig := @Acceleration.fors_pk_from_sig _

abbrev cache.shake_ops.start := @shake.hash.start
abbrev cache.shake_ops.digest := shake.hash.digest
abbrev cache.shake_ops.thash := @shake.hash.thash
abbrev cache.shake_ops.wots_secret := @shake.wots.secret
abbrev cache.shake_ops.wots_chain := @shake.wots.chain
abbrev cache.shake_ops.fors_sk_gen := @shake.fors.fors_sk_gen
abbrev cache.shake_ops.fors_node_portable := @shake.fors.fors_node
abbrev cache.shake_ops.climb {N : Usize} (node : Array U8 N) (idx : U32) (auth : Slice U8)
    (first : Usize) (height : U32) (seed : Array U8 N) (a : address.Adrs) :=
  CacheopsRust.cache.shake_ops.climb node idx auth first height seed
    ⟨a.layer, a.tree, a.typ, a.keypair, a.word2, a.word3⟩

@[rust_loop_body]
def cache.shake_ops.wots_pk_gen_portable_loop.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (iter : core.ops.range.Range Std.Usize) (pk : shake256.Sponge) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × shake256.Sponge)
    shake256.Sponge)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done pk)
  | some i6 =>
    let a ←
      cache.shake_ops.wots_secret sk seed
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } i6
    let i7 ← lift (UScalar.cast .U32 i6)
    let a1 ←
      address.Adrs.with_word2
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } i7
    let i8 ← params.W - 1#u32
    let «end» ← cache.shake_ops.wots_chain a seed a1 0#u32 i8
    let s ← lift (Array.to_slice «end»)
    let pk1 ← shake256.Sponge.absorb pk s
    ok (cont (iter1, pk1))

@[rust_loop]
def cache.shake_ops.wots_pk_gen_portable_loop
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (i : Std.U32) (i1 : Std.U64) (i2 : Std.U32)
  (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (pk : shake256.Sponge) :
  Result shake256.Sponge
  := do
  loop
    (fun (iter1, pk1) => cache.shake_ops.wots_pk_gen_portable_loop.body sk seed
      i i1 i2 i3 i4 i5 iter1 pk1)
    (iter, pk)

def cache.shake_ops.wots_pk_gen_portable
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let a ← address.Adrs.with_type adrs address.WOTS_PK
  let a1 ← address.Adrs.with_keypair a adrs.keypair
  let pk ← cache.shake_ops.start seed a1
  let i ← 2#usize * N
  let i1 ← i + params.LEN2
  let pk1 ←
    cache.shake_ops.wots_pk_gen_portable_loop
      { start := 0#usize, «end» := i1 } sk seed adrs.layer adrs.tree
      adrs.typ adrs.keypair adrs.word2 adrs.word3 pk
  cache.shake_ops.digest N pk1

@[rust_loop_body]
def cache.shake_ops.wots_sign_loop.body
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (adrs : address.Adrs)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U32)) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U32)) × (alloc.vec.Vec Std.U8)) (alloc.vec.Vec
    Std.U8))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter
  match o with
  | none => ok (done sig)
  | some p =>
    let (i, d) := p
    let a ← cache.shake_ops.wots_secret sk seed adrs i
    let i1 ← lift (UScalar.cast .U32 i)
    let a1 ← address.Adrs.with_word2 adrs i1
    let v ← cache.shake_ops.wots_chain a seed a1 0#u32 d
    let s ← lift (Array.to_slice v)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
    ok (cont (iter1, sig1))

@[rust_loop]
def cache.shake_ops.wots_sign_loop
  {N : Std.Usize}
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U32)) (sk : Array Std.U8 N) (seed : Array Std.U8 N) (adrs : address.Adrs)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => cache.shake_ops.wots_sign_loop.body sk seed adrs
      iter1 sig1)
    (iter, sig)

def cache.shake_ops.wots_sign
  {N : Std.Usize} (msg : Array Std.U8 N) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let digits ← wots.wots_digits msg
  let b ← cache.shake_ops.simd.available N
  if b
  then
    let s := alloc.vec.Vec.deref digits
    cache.shake_ops.simd.wots_sign sk seed adrs s
  else
    let i := alloc.vec.Vec.len digits
    let i1 ← i * N
    let sig := alloc.vec.Vec.with_capacity Std.U8 i1
    let s := alloc.vec.Vec.deref digits
    let i2 ← core.slice.Slice.iter s
    let iter ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U32) i2
    cache.shake_ops.wots_sign_loop iter sk seed adrs sig

@[rust_loop_body]
def cache.shake_ops.wots_pk_from_sig_loop.body
  {N : Std.Usize} (sig : Slice Std.U8) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U32)) (pk : shake256.Sponge) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U32)) × shake256.Sponge) shake256.Sponge)
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter
  match o with
  | none => ok (done pk)
  | some p =>
    let (i6, d) := p
    let a ← util.block N sig i6
    let i7 ← lift (UScalar.cast .U32 i6)
    let a1 ←
      address.Adrs.with_word2
        {
          layer := i,
          tree := i1,
          typ := i2,
          keypair := i3,
          word2 := i4,
          word3 := i5
        } i7
    let i8 ← params.W - 1#u32
    let «end» ← cache.shake_ops.wots_chain a seed a1 d i8
    let s ← lift (Array.to_slice «end»)
    let pk1 ← shake256.Sponge.absorb pk s
    ok (cont (iter1, pk1))

@[rust_loop]
def cache.shake_ops.wots_pk_from_sig_loop
  {N : Std.Usize}
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U32)) (sig : Slice Std.U8) (seed : Array Std.U8 N) (i : Std.U32)
  (i1 : Std.U64) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (pk : shake256.Sponge) :
  Result shake256.Sponge
  := do
  loop
    (fun (iter1, pk1) => cache.shake_ops.wots_pk_from_sig_loop.body sig seed i
      i1 i2 i3 i4 i5 iter1 pk1)
    (iter, pk)

def cache.shake_ops.wots_pk_from_sig
  {N : Std.Usize} (sig : Slice Std.U8) (msg : Array Std.U8 N)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let digits ← wots.wots_digits msg
  let b ← cache.shake_ops.simd.available N
  if b
  then
    let s := alloc.vec.Vec.deref digits
    cache.shake_ops.simd.wots_pk_from_sig sig seed adrs s
  else
    let a ← address.Adrs.with_type adrs address.WOTS_PK
    let a1 ← address.Adrs.with_keypair a adrs.keypair
    let pk ← cache.shake_ops.start seed a1
    let s := alloc.vec.Vec.deref digits
    let i ← core.slice.Slice.iter s
    let iter ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U32) i
    let pk1 ←
      cache.shake_ops.wots_pk_from_sig_loop iter sig seed adrs.layer
        adrs.tree adrs.typ adrs.keypair adrs.word2 adrs.word3 pk
    cache.shake_ops.digest N pk1

@[rust_loop_body]
def cache.shake_ops.fors_sign_loop0_loop0.body
  {N : Std.Usize} (i : Std.U32) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (adrs : address.Adrs) (idx : Std.U32) (tree : Std.U32)
  (iter : core.ops.range.Range Std.U32) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let i1 ← idx >>> j
    let s ← lift (i1 ^^^ 1#u32)
    let i2 ← i - j
    let i3 ← tree <<< i2
    let i4 ← i3 + s
    let node ← cache.shake_ops.fors_node_portable sk i4 j seed adrs
    let s1 ← lift (Array.to_slice node)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s1
    ok (cont (iter1, sig1))

@[rust_loop]
def cache.shake_ops.fors_sign_loop0_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (i : Std.U32)
  (sk : Array Std.U8 N) (seed : Array Std.U8 N) (adrs : address.Adrs)
  (sig : alloc.vec.Vec Std.U8) (idx : Std.U32) (tree : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => cache.shake_ops.fors_sign_loop0_loop0.body i sk seed
      adrs idx tree iter1 sig1)
    (iter, sig)

@[rust_loop_body]
def cache.shake_ops.fors_sign_loop0.body
  {N : Std.Usize} (i : Std.U32) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (adrs : address.Adrs)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U32)) (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U32)) × (alloc.vec.Vec Std.U8)) (alloc.vec.Vec
    Std.U8))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter
  match o with
  | none => ok (done sig)
  | some p =>
    let (i1, idx) := p
    let tree ← lift (UScalar.cast .U32 i1)
    let i2 ← tree <<< i
    let i3 ← i2 + idx
    let a ← cache.shake_ops.fors_sk_gen sk seed adrs i3
    let s ← lift (Array.to_slice a)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
    let sig2 ←
      cache.shake_ops.fors_sign_loop0_loop0 { start := 0#u32, «end» := i } i
        sk seed adrs sig1 idx tree
    ok (cont (iter1, sig2))

@[rust_loop]
def cache.shake_ops.fors_sign_loop0
  {N : Std.Usize}
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U32)) (i : Std.U32) (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (adrs : address.Adrs) (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => cache.shake_ops.fors_sign_loop0.body i sk seed adrs
      iter1 sig1)
    (iter, sig)

def cache.shake_ops.fors_sign
  {N : Std.Usize} (p : params.Params) (md : Slice Std.U8) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let i ← lift (UScalar.cast .Usize p.k)
  let indices ← util.base_2b md p.a i
  let b ← cache.shake_ops.simd.available N
  if b
  then
    let s := alloc.vec.Vec.deref indices
    cache.shake_ops.simd.fors_sign p s sk seed adrs
  else
    let i1 ← params.Params.fors_sig_bytes p
    let sig := alloc.vec.Vec.with_capacity Std.U8 i1
    let s := alloc.vec.Vec.deref indices
    let i2 ← core.slice.Slice.iter s
    let iter ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U32) i2
    cache.shake_ops.fors_sign_loop0 iter p.a sk seed adrs sig

@[rust_loop_body]
def cache.shake_ops.fors_pk_from_sig_loop.body
  {N : Std.Usize} (i : Std.U32) (sig : Slice Std.U8) (seed : Array Std.U8 N)
  (i1 : Std.U32) (i2 : Std.U64) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (i6 : Std.U32)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U32)) (roots : shake256.Sponge) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U32)) × shake256.Sponge) shake256.Sponge)
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter
  match o with
  | none => ok (done roots)
  | some p =>
    let (i7, sel) := p
    let i8 ← lift (UScalar.cast .Usize i)
    let i9 ← 1#usize + i8
    let offset ← i7 * i9
    let i10 ← lift (UScalar.cast .U32 i7)
    let i11 ← i10 <<< i
    let idx ← i11 + sel
    let a ←
      address.Adrs.with_word2
        {
          layer := i1,
          tree := i2,
          typ := i3,
          keypair := i4,
          word2 := i5,
          word3 := i6
        } 0#u32
    let a1 ← address.Adrs.with_word3 a idx
    let a2 ← util.block N sig offset
    let value ← cache.shake_ops.thash seed a1 a2
    let i12 ← offset + 1#usize
    let root ←
      cache.shake_ops.climb value idx sig i12 i seed
        {
          layer := i1,
          tree := i2,
          typ := i3,
          keypair := i4,
          word2 := i5,
          word3 := i6
        }
    let s ← lift (Array.to_slice root)
    let roots1 ← shake256.Sponge.absorb roots s
    ok (cont (iter1, roots1))

@[rust_loop]
def cache.shake_ops.fors_pk_from_sig_loop
  {N : Std.Usize}
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U32)) (i : Std.U32) (sig : Slice Std.U8) (seed : Array Std.U8 N)
  (i1 : Std.U32) (i2 : Std.U64) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32)
  (i6 : Std.U32) (roots : shake256.Sponge) :
  Result shake256.Sponge
  := do
  loop
    (fun (iter1, roots1) => cache.shake_ops.fors_pk_from_sig_loop.body i sig
      seed i1 i2 i3 i4 i5 i6 iter1 roots1)
    (iter, roots)

def cache.shake_ops.fors_pk_from_sig
  {N : Std.Usize} (p : params.Params) (sig : Slice Std.U8) (md : Slice Std.U8)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let i ← lift (UScalar.cast .Usize p.k)
  let indices ← util.base_2b md p.a i
  let b ← cache.shake_ops.simd.available N
  if b
  then
    let s := alloc.vec.Vec.deref indices
    cache.shake_ops.simd.fors_pk_from_sig p s sig seed adrs
  else
    let a ← address.Adrs.with_type adrs address.FORS_ROOTS
    let a1 ← address.Adrs.with_keypair a adrs.keypair
    let roots ← cache.shake_ops.start seed a1
    let s := alloc.vec.Vec.deref indices
    let i1 ← core.slice.Slice.iter s
    let iter ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U32) i1
    let roots1 ←
      cache.shake_ops.fors_pk_from_sig_loop iter p.a sig seed adrs.layer
        adrs.tree adrs.typ adrs.keypair adrs.word2 adrs.word3 roots
    cache.shake_ops.digest N roots1

end slhdsa.CacheScalar
