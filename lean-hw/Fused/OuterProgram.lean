import Fused.Program
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Fused.Outer
set_option linter.concreteInstances false
class Branches where
  available : Usize → Result Bool
  fused {N : Usize} : params.Params → Array U8 N → Array U8 N → U32 → Array U8 N → address.Adrs → Result (alloc.vec.Vec U8)
  subtree : Fused.Subtree
  keygen {N : Usize} : Array U8 N → Array U8 N → address.Adrs → Result (Array U8 N)
  sign {N : Usize} : Array U8 N → Array U8 N → address.Adrs → Slice U32 → Result (alloc.vec.Vec U8)
variable [b : Branches]
abbrev shake.batch.available := b.available
abbrev shake.batch.xmss_sign_batch := @b.fused
abbrev shake.batch.xmss_subtree := @b.subtree
abbrev shake.batch.keygen := @b.keygen
abbrev shake.batch.sign := @b.sign

def shake.wots.wots_pk_gen
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let b ← shake.batch.available N
  if b
  then shake.batch.keygen sk seed adrs
  else
    let a ← address.Adrs.with_type adrs address.WOTS_PK
    let a1 ← address.Adrs.with_keypair a adrs.keypair
    let pk ← shake.hash.start seed a1
    let pk1 ←
      shake.wots.wots_pk_gen_loop sk seed adrs.layer adrs.tree adrs.typ
        adrs.keypair adrs.word2 adrs.word3 pk 0#usize
    shake.hash.digest N pk1

def shake.xmss.xmss_node
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (i : Std.U32) (z : Std.U32)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  if z >= 1#u32
  then
    let b ← shake.batch.available N
    if b
    then shake.batch.xmss_subtree sk_seed seed i z adrs
    else
      if z = 0#u32
      then
        let a ← address.Adrs.with_type adrs address.WOTS_HASH
        let a1 ← address.Adrs.with_keypair a i
        shake.wots.wots_pk_gen sk_seed seed a1
      else
        let i1 ← 2#u32 * i
        let i2 ← z - 1#u32
        let lnode ← shake.xmss.xmss_node sk_seed i1 i2 seed adrs
        let i3 ← i1 + 1#u32
        let rnode ← shake.xmss.xmss_node sk_seed i3 i2 seed adrs
        let a ← address.Adrs.with_type adrs address.TREE
        let a1 ← address.Adrs.with_word2 a z
        let a2 ← address.Adrs.with_word3 a1 i
        shake.xmss.hash2 seed a2 lnode rnode
  else
    if z = 0#u32
    then
      let a ← address.Adrs.with_type adrs address.WOTS_HASH
      let a1 ← address.Adrs.with_keypair a i
      shake.wots.wots_pk_gen sk_seed seed a1
    else
      let i1 ← 2#u32 * i
      let i2 ← z - 1#u32
      let lnode ← shake.xmss.xmss_node sk_seed i1 i2 seed adrs
      let i3 ← i1 + 1#u32
      let rnode ← shake.xmss.xmss_node sk_seed i3 i2 seed adrs
      let a ← address.Adrs.with_type adrs address.TREE
      let a1 ← address.Adrs.with_word2 a z
      let a2 ← address.Adrs.with_word3 a1 i
      shake.xmss.hash2 seed a2 lnode rnode
partial_fixpoint

def shake.wots.wots_sign
  {N : Std.Usize} (msg : Array Std.U8 N) (sk : Array Std.U8 N)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let digits ← wots.wots_digits msg
  let b ← shake.batch.available N
  if b
  then let s := alloc.vec.Vec.deref digits
       shake.batch.sign sk seed adrs s
  else
    shake.wots.wots_sign_loop sk seed adrs digits (alloc.vec.Vec.new Std.U8)
      0#usize

@[rust_loop_body]
def shake.xmss.xmss_sign_loop0.body
  {N : Std.Usize} (i : Std.U32) (sk_seed : Array Std.U8 N) (idx : Std.U32)
  (seed : Array Std.U8 N) (adrs : address.Adrs) (sig : alloc.vec.Vec Std.U8)
  (j : Std.U32) :
  Result (ControlFlow ((alloc.vec.Vec Std.U8) × Std.U32) (alloc.vec.Vec
    Std.U8))
  := do
  if j < i
  then
    let i1 ← idx >>> j
    let k ← lift (i1 ^^^ 1#u32)
    let node ← shake.xmss.xmss_node sk_seed k j seed adrs
    let s ← lift (Array.to_slice node)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
    let j1 ← j + 1#u32
    ok (cont (sig1, j1))
  else ok (done sig)

@[rust_loop]
def shake.xmss.xmss_sign_loop0
  {N : Std.Usize} (i : Std.U32) (sk_seed : Array Std.U8 N) (idx : Std.U32)
  (seed : Array Std.U8 N) (adrs : address.Adrs) (sig : alloc.vec.Vec Std.U8)
  (j : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (sig1, j1) => shake.xmss.xmss_sign_loop0.body i sk_seed idx seed adrs
      sig1 j1)
    (sig, j)

@[rust_loop_body]
def shake.xmss.xmss_sign_loop1.body
  {N : Std.Usize} (i : Std.U32) (sk_seed : Array Std.U8 N) (idx : Std.U32)
  (seed : Array Std.U8 N) (adrs : address.Adrs) (sig : alloc.vec.Vec Std.U8)
  (j : Std.U32) :
  Result (ControlFlow ((alloc.vec.Vec Std.U8) × Std.U32) (alloc.vec.Vec
    Std.U8))
  := do
  if j < i
  then
    let i1 ← idx >>> j
    let k ← lift (i1 ^^^ 1#u32)
    let node ← shake.xmss.xmss_node sk_seed k j seed adrs
    let s ← lift (Array.to_slice node)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
    let j1 ← j + 1#u32
    ok (cont (sig1, j1))
  else ok (done sig)

@[rust_loop]
def shake.xmss.xmss_sign_loop1
  {N : Std.Usize} (i : Std.U32) (sk_seed : Array Std.U8 N) (idx : Std.U32)
  (seed : Array Std.U8 N) (adrs : address.Adrs) (sig : alloc.vec.Vec Std.U8)
  (j : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (sig1, j1) => shake.xmss.xmss_sign_loop1.body i sk_seed idx seed adrs
      sig1 j1)
    (sig, j)

def shake.xmss.xmss_sign
  {N : Std.Usize} (p : params.Params) (m : Array Std.U8 N)
  (sk_seed : Array Std.U8 N) (idx : Std.U32) (seed : Array Std.U8 N)
  (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  if p.hp >= 3#u32
  then
    let b ← shake.batch.available N
    if b
    then shake.batch.xmss_sign_batch p m sk_seed idx seed adrs
    else
      let a ← address.Adrs.with_type adrs address.WOTS_HASH
      let a1 ← address.Adrs.with_keypair a idx
      let sig ← shake.wots.wots_sign m sk_seed seed a1
      shake.xmss.xmss_sign_loop0 p.hp sk_seed idx seed adrs sig 0#u32
  else
    let a ← address.Adrs.with_type adrs address.WOTS_HASH
    let a1 ← address.Adrs.with_keypair a idx
    let sig ← shake.wots.wots_sign m sk_seed seed a1
    shake.xmss.xmss_sign_loop1 p.hp sk_seed idx seed adrs sig 0#u32

end slhdsa.Fused.Outer
