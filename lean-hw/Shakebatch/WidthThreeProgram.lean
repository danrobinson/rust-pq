import Shakebatch.LinuxWots
import Slhdsa.Proofs.ShakeXmss
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.WidthThree
set_option linter.concreteInstances false

/-- Runtime WOTS primitives shared by the extracted width-three XMSS callers. -/
class Wots where
  keygen {N : Usize} : Array U8 N → Array U8 N → address.Adrs → Result (Array U8 N)
  sign {N : Usize} : Array U8 N → Array U8 N → address.Adrs → Slice U32 → Result (alloc.vec.Vec U8)

variable [w : Wots]
abbrev shake.batch.keygen := @Wots.keygen w
abbrev shake.batch.sign := @Wots.sign w
abbrev shake.batch.available := ShakeBatch.Linux.available

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

def shake.xmss.hash2
  {N : Std.Usize} (seed : Array Std.U8 N) (adrs : address.Adrs)
  (left : Array Std.U8 N) (right : Array Std.U8 N) :
  Result (Array Std.U8 N)
  := do
  shake.hash.thash_pair seed adrs left right

/-- [slhdsa::shake::batch::xmss_subtree_fallback]:
    Source: 'src/shake/batch.rs', lines 630:0-648:1 -/
def shake.batch.xmss_subtree_fallback
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (tree_index : Std.U32) (height : Std.U32) (addr : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  if height = 0#u32
  then
    let a ← address.Adrs.with_type addr address.WOTS_HASH
    let a1 ← address.Adrs.with_keypair a tree_index
    shake.batch.keygen sk seed a1
  else
    let i ← 2#u32 * tree_index
    let i1 ← height - 1#u32
    let left ← shake.batch.xmss_subtree_fallback sk seed i i1 addr
    let i2 ← i + 1#u32
    let right ← shake.batch.xmss_subtree_fallback sk seed i2 i1 addr
    let a ← address.Adrs.with_type addr address.TREE
    let a1 ← address.Adrs.with_word2 a height
    let a2 ← address.Adrs.with_word3 a1 tree_index
    shake.hash.thash_pair seed a2 left right
partial_fixpoint

/-- [slhdsa::shake::batch::xmss_subtree]:
    Source: 'src/shake/batch.rs', lines 618:0-628:1 -/
def shake.batch.xmss_subtree
  {N : Std.Usize} (sk : Array Std.U8 N) (seed : Array Std.U8 N)
  (tree_index : Std.U32) (height : Std.U32) (addr : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  shake.batch.xmss_subtree_fallback sk seed tree_index height addr

/-- [slhdsa::shake::xmss::xmss_node]:
    Source: 'src/shake/../xmss.rs', lines 16:0-47:1
    Visibility: public -/
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

/-- [slhdsa::shake::batch::xmss_sign_batch]: loop body 0:
    Source: 'src/shake/batch.rs', lines 664:8-668:9 -/
@[rust_loop_body]
def shake.batch.xmss_sign_batch_loop.body
  {N : Std.Usize} (sk : Array Std.U8 N) (idx : Std.U32) (seed : Array Std.U8 N)
  (addr : address.Adrs) (iter : core.ops.range.Range Std.U32)
  (sig : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (alloc.vec.Vec
    Std.U8)) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let i ← idx >>> j
    let k ← lift (i ^^^ 1#u32)
    let node ← shake.batch.xmss_subtree_fallback sk seed k j addr
    let s ← lift (Array.to_slice node)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
    ok (cont (iter1, sig1))

/-- [slhdsa::shake::batch::xmss_sign_batch]: loop 0:
    Source: 'src/shake/batch.rs', lines 664:8-668:9 -/
@[rust_loop]
def shake.batch.xmss_sign_batch_loop
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (idx : Std.U32) (seed : Array Std.U8 N) (addr : address.Adrs)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => shake.batch.xmss_sign_batch_loop.body sk idx seed
      addr iter1 sig1)
    (iter, sig)

/-- [slhdsa::shake::batch::xmss_sign_batch]:
    Source: 'src/shake/batch.rs', lines 653:0-670:1 -/
def shake.batch.xmss_sign_batch
  {N : Std.Usize} (p : params.Params) (m : Array Std.U8 N)
  (sk : Array Std.U8 N) (idx : Std.U32) (seed : Array Std.U8 N)
  (addr : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let digits ← wots.wots_digits m
  let a ← address.Adrs.with_type addr address.WOTS_HASH
  let a1 ← address.Adrs.with_keypair a idx
  let s := alloc.vec.Vec.deref digits
  let sig ← shake.batch.sign sk seed a1 s
  shake.batch.xmss_sign_batch_loop { start := 0#u32, «end» := p.hp } sk idx
    seed addr sig

/-- [slhdsa::shake::xmss::xmss_sign]: loop body 0:
    Source: 'src/shake/../xmss.rs', lines 72:4-77:5
    Visibility: public -/
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

/-- [slhdsa::shake::xmss::xmss_sign]: loop 0:
    Source: 'src/shake/../xmss.rs', lines 72:4-77:5
    Visibility: public -/
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

/-- [slhdsa::shake::xmss::xmss_sign]: loop body 1:
    Source: 'src/shake/../xmss.rs', lines 72:4-77:5
    Visibility: public -/
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

/-- [slhdsa::shake::xmss::xmss_sign]: loop 1:
    Source: 'src/shake/../xmss.rs', lines 72:4-77:5
    Visibility: public -/
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

/-- [slhdsa::shake::xmss::xmss_sign]:
    Source: 'src/shake/../xmss.rs', lines 50:0-79:1
    Visibility: public -/
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

end slhdsa.WidthThree
