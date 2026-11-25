import Cachepath.ShakeNode

/-! The complete serial signer specialized to scalar dispatch. Its orchestration
definitions are compared with one extraction starting at the production signer. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace CacheopsRust.Closed

/-- Scalar dispatch with arbitrary unreachable accelerator branches. -/
def scalarBackend : slhdsa.CacheScalar.Acceleration where
  available := fun _ => ok false
  wots_sign := fun _ _ _ _ => fail .panic
  wots_pk_from_sig := fun _ _ _ _ => fail .panic
  fors_sign := fun _ _ _ _ _ => fail .panic
  fors_pk_from_sig := fun _ _ _ _ _ => fail .panic

local instance : slhdsa.CacheScalar.Acceleration := scalarBackend

abbrev cache.shake_ops.wots_sign {N : Usize} (m sk seed : Array U8 N) (a : address.Adrs) :=
  slhdsa.CacheScalar.cache.shake_ops.wots_sign m sk seed (toSlhAdrs a)
abbrev cache.shake_ops.wots_pk_from_sig {N : Usize} (sig : Slice U8) (m seed : Array U8 N)
    (a : address.Adrs) :=
  slhdsa.CacheScalar.cache.shake_ops.wots_pk_from_sig sig m seed (toSlhAdrs a)
abbrev cache.shake_ops.fors_sign {N : Usize} (p : params.Params) (md : Slice U8)
    (sk seed : Array U8 N) (a : address.Adrs) :=
  slhdsa.CacheScalar.cache.shake_ops.fors_sign (toSlhParams p) md sk seed (toSlhAdrs a)
abbrev cache.shake_ops.fors_pk_from_sig {N : Usize} (p : params.Params) (sig md : Slice U8)
    (seed : Array U8 N) (a : address.Adrs) :=
  slhdsa.CacheScalar.cache.shake_ops.fors_pk_from_sig (toSlhParams p) sig md seed (toSlhAdrs a)
abbrev cache.shake_ops.xmss_node {N : Usize} (sk : Array U8 N) (i z : U32) (seed : Array U8 N)
    (a : address.Adrs) :=
  ShakeNode.node (fun _ => ok false) (fun _ _ _ _ _ => fail .panic)
    (fun sk seed adrs => slhdsa.CacheScalar.cache.shake_ops.wots_pk_gen_portable sk seed (toSlhAdrs adrs))
    sk i z seed a

@[rust_loop_body]
def cache.shake_ops.xmss_sign_loop.body
  {N : Std.Usize} (sk : Array Std.U8 N) (idx : Std.U32) (seed : Array Std.U8 N)
  (adrs : address.Adrs) (iter : core.ops.range.Range Std.U32)
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
    let node ← cache.shake_ops.xmss_node sk k j seed adrs
    let s ← lift (Array.to_slice node)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
    ok (cont (iter1, sig1))

@[rust_loop]
def cache.shake_ops.xmss_sign_loop
  {N : Std.Usize} (iter : core.ops.range.Range Std.U32) (sk : Array Std.U8 N)
  (idx : Std.U32) (seed : Array Std.U8 N) (adrs : address.Adrs)
  (sig : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, sig1) => cache.shake_ops.xmss_sign_loop.body sk idx seed adrs
      iter1 sig1)
    (iter, sig)

def cache.shake_ops.xmss_sign
  {N : Std.Usize} (p : params.Params) (m : Array Std.U8 N)
  (sk : Array Std.U8 N) (idx : Std.U32) (seed : Array Std.U8 N)
  (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let a ← address.Adrs.with_type adrs address.WOTS_HASH
  let a1 ← address.Adrs.with_keypair a idx
  let sig ← cache.shake_ops.wots_sign m sk seed a1
  cache.shake_ops.xmss_sign_loop { start := 0#u32, «end» := p.hp } sk idx
    seed adrs sig

def cache.shake_ops.xmss_pk_from_sig
  {N : Std.Usize} (p : params.Params) (idx : Std.U32) (sig : Slice Std.U8)
  (m : Array Std.U8 N) (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let a ← address.Adrs.with_type adrs address.WOTS_HASH
  let a1 ← address.Adrs.with_keypair a idx
  let node ← cache.shake_ops.wots_pk_from_sig sig m seed a1
  let i ← 2#usize * N
  let i1 ← i + params.LEN2
  let a2 ← address.Adrs.with_type adrs address.TREE
  cache.shake_ops.climb node idx sig i1 p.hp seed a2

@[rust_loop_body]
def cache.shake_ops.sign_from_digest_loop.body
  {N : Std.Usize} (a : address.Adrs) (i : Std.Usize) (i1 : Std.U32)
  (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32) (i5 : Std.U32) (i6 : Std.Usize)
  (sk_seed : Array Std.U8 N) (pk_seed : Array Std.U8 N)
  (top_tree : Slice (Array Std.U8 N)) (iter : core.ops.range.Range Std.U32)
  (layer_d2_hit : Option (Slice (Array Std.U8 N))) (root : Array Std.U8 N)
  (sig : alloc.vec.Vec Std.U8) (tree : Std.U64) (leaf : Std.U32) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (Option (Slice (Array
    Std.U8 N))) × (Array Std.U8 N) × (alloc.vec.Vec Std.U8) × Std.U64 ×
    Std.U32) (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done sig)
  | some j =>
    let a1 ← address.Adrs.with_layer a j
    let adrs ← address.Adrs.with_tree a1 tree
    let i7 ← i2 - 1#u32
    let (layer_d2_hit1, root1, sig1, iter2) ←
      if j = i7
      then
        do
        let a2 ← address.Adrs.with_type adrs address.WOTS_HASH
        let a3 ← address.Adrs.with_keypair a2 leaf
        let wots ← cache.shake_ops.wots_sign root sk_seed pk_seed a3
        let s := alloc.vec.Vec.deref wots
        let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
        let sig3 ← cache.append_auth_path top_tree i3 leaf sig2
        ok (layer_d2_hit, root, sig3, iter1)
      else
        do
        let i8 ← j + 2#u32
        if i8 = i2
        then
          let (a2, v) ←
            match layer_d2_hit with
            | none =>
              do
              let s ←
                cache.shake_ops.xmss_sign
                  {
                    n := i,
                    h := i1,
                    d := i2,
                    hp := i3,
                    a := i4,
                    k := i5,
                    m := i6
                  } root sk_seed leaf pk_seed adrs
              let s1 := alloc.vec.Vec.deref s
              let root2 ←
                cache.shake_ops.xmss_pk_from_sig
                  {
                    n := i,
                    h := i1,
                    d := i2,
                    hp := i3,
                    a := i4,
                    k := i5,
                    m := i6
                  } leaf s1 root pk_seed adrs
              let s2 := alloc.vec.Vec.deref s
              let sig2 ←
                alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s2
              ok (root2, sig2)
            | some d2_tree =>
              do
              let a3 ← address.Adrs.with_type adrs address.WOTS_HASH
              let a4 ← address.Adrs.with_keypair a3 leaf
              let wots ← cache.shake_ops.wots_sign root sk_seed pk_seed a4
              let s := alloc.vec.Vec.deref wots
              let sig2 ←
                alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
              let sig3 ← cache.append_auth_path d2_tree i3 leaf sig2
              let root2 ← cache.tree_root d2_tree
              ok (root2, sig3)
          ok (layer_d2_hit, a2, v, iter1)
        else
          let s ←
            cache.shake_ops.xmss_sign
              { n := i, h := i1, d := i2, hp := i3, a := i4, k := i5, m := i6 }
              root sk_seed leaf pk_seed adrs
          let s1 := alloc.vec.Vec.deref s
          let root2 ←
            cache.shake_ops.xmss_pk_from_sig
              { n := i, h := i1, d := i2, hp := i3, a := i4, k := i5, m := i6 }
              leaf s1 root pk_seed adrs
          let s2 := alloc.vec.Vec.deref s
          let sig2 ←
            alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s2
          ok (layer_d2_hit, root2, sig2, iter1)
    let i8 ← 1#u64 <<< i3
    let i9 ← i8 - 1#u64
    let i10 ← lift (tree &&& i9)
    let leaf1 ← lift (UScalar.cast .U32 i10)
    let tree1 ← tree >>> i3
    ok (cont (iter2, layer_d2_hit1, root1, sig1, tree1, leaf1))

@[rust_loop]
def cache.shake_ops.sign_from_digest_loop
  {N : Std.Usize} (a : address.Adrs) (iter : core.ops.range.Range Std.U32)
  (i : Std.Usize) (i1 : Std.U32) (i2 : Std.U32) (i3 : Std.U32) (i4 : Std.U32)
  (i5 : Std.U32) (i6 : Std.Usize) (sk_seed : Array Std.U8 N)
  (pk_seed : Array Std.U8 N) (top_tree : Slice (Array Std.U8 N))
  (layer_d2_hit : Option (Slice (Array Std.U8 N))) (root : Array Std.U8 N)
  (sig : alloc.vec.Vec Std.U8) (tree : Std.U64) (leaf : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, layer_d2_hit1, root1, sig1, tree1, leaf1) =>
      cache.shake_ops.sign_from_digest_loop.body a i i1 i2 i3 i4 i5 i6 sk_seed
      pk_seed top_tree iter1 layer_d2_hit1 root1 sig1 tree1 leaf1)
    (iter, layer_d2_hit, root, sig, tree, leaf)

def cache.shake_ops.sign_from_digest
  {N : Std.Usize} (p : params.Params) (sk_seed : Array Std.U8 N)
  (pk_seed : Array Std.U8 N) (r : Array Std.U8 N) (digest : Slice Std.U8)
  (top_tree : Slice (Array Std.U8 N))
  (layer_d2_hit : Option (Slice (Array Std.U8 N))) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let idx_tree ← cache.digest_tree p digest
  let idx_leaf ← cache.digest_leaf p digest
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_tree a idx_tree
  let a2 ← address.Adrs.with_type a1 address.FORS_TREE
  let fors_adrs ← address.Adrs.with_keypair a2 idx_leaf
  let i ← params.Params.md_bytes p
  let md ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) digest { start := 0#usize, «end» := i }
  let sig_fors ← cache.shake_ops.fors_sign p md sk_seed pk_seed fors_adrs
  let s := alloc.vec.Vec.deref sig_fors
  let root ← cache.shake_ops.fors_pk_from_sig p s md pk_seed fors_adrs
  let i1 ← params.Params.sig_bytes p
  let sig := alloc.vec.Vec.with_capacity Std.U8 i1
  let s1 ← lift (Array.to_slice r)
  let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s1
  let s2 := alloc.vec.Vec.deref sig_fors
  let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig1 s2
  cache.shake_ops.sign_from_digest_loop a { start := 0#u32, «end» := p.d }
    p.n p.h p.d p.hp p.a p.k p.m sk_seed pk_seed top_tree layer_d2_hit root
    sig2 idx_tree idx_leaf

end CacheopsRust.Closed
