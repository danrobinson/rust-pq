import Cachepath.ShakeClosed
import Segmentedapi.Top
import Shakeopt.Segmented

/-! Source-matched public cache functions. Acceleration is specialized only in
the SHAKE signer. SHA-2 uses the shared segmented hash and signature modules. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace CacheopsRust.Public
variable [backend : Closed.Backend]

abbrev hash.prf_msg {N : Usize} := @slhdsa.hash.prf_msg N
abbrev hash.h_msg {N : Usize} (p : params.Params) := @slhdsa.hash.h_msg N (toSlhParams p)
abbrev slh.message.randomizer {N : Usize} := @SegmentedApiRust.slh.message.randomizer N
abbrev slh.message.digest {N : Usize} (p : params.Params) :=
  @SegmentedApiRust.slh.message.digest N (toSlhParams p)
abbrev cache.shake_ops.sign_from_digest {N : Usize} := @Closed.cache.shake_ops.sign_from_digest backend N

def cache.with_pure_context
  (m : Slice Std.U8) (ctx : Slice Std.U8) : Result (alloc.vec.Vec Std.U8) := do
  let i := Slice.len ctx
  let i1 ← 2#usize + i
  let i2 := Slice.len m
  let i3 ← i1 + i2
  let mp := alloc.vec.Vec.with_capacity Std.U8 i3
  let mp1 ← alloc.vec.Vec.push mp 0#u8
  let i4 := Slice.len ctx
  let i5 ← lift (UScalar.cast .U8 i4)
  let mp2 ← alloc.vec.Vec.push mp1 i5
  let mp3 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 mp2 ctx
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 mp3 m

def cache.sha2_ops.pure_digest
  {N : Std.Usize} (p : params.Params) (sk_prf : Array Std.U8 N)
  (pk_seed : Array Std.U8 N) (pk_root : Array Std.U8 N)
  (addrnd : Array Std.U8 N) (ctx : Slice Std.U8) (m : Slice Std.U8) :
  Result ((Array Std.U8 N) × (alloc.vec.Vec Std.U8))
  := do
  let i := Slice.len m
  if i < 1024#usize
  then
    let mp ← cache.with_pure_context m ctx
    let s := alloc.vec.Vec.deref mp
    let r ← hash.prf_msg sk_prf addrnd s
    let s1 := alloc.vec.Vec.deref mp
    let digest ← hash.h_msg p r pk_seed pk_root s1
    ok (r, digest)
  else
    let r ← slh.message.randomizer sk_prf addrnd ctx m
    let digest ← slh.message.digest p r pk_seed pk_root ctx m
    ok (r, digest)

def cache.shake_ops.pure_digest
  {N : Std.Usize} (p : params.Params) (sk_prf : Array Std.U8 N)
  (pk_seed : Array Std.U8 N) (pk_root : Array Std.U8 N)
  (addrnd : Array Std.U8 N) (ctx : Slice Std.U8) (m : Slice Std.U8) :
  Result ((Array Std.U8 N) × (alloc.vec.Vec Std.U8))
  := do
  let i := Slice.len ctx
  let i1 ← lift (UScalar.cast .U8 i)
  let prf ← shake256.Sponge.new
  let s ← lift (Array.to_slice sk_prf)
  let prf1 ← shake256.Sponge.absorb prf s
  let s1 ← lift (Array.to_slice addrnd)
  let prf2 ← shake256.Sponge.absorb prf1 s1
  let s2 ← lift (Array.to_slice (Array.make 2#usize [ 0#u8, i1 ]))
  let prf3 ← shake256.Sponge.absorb prf2 s2
  let prf4 ← shake256.Sponge.absorb prf3 ctx
  let prf5 ← shake256.Sponge.absorb prf4 m
  let r ← cache.shake_ops.digest N prf5
  let s3 ← lift (Array.to_slice r)
  let h ← shake256.Sponge.absorb prf s3
  let s4 ← lift (Array.to_slice pk_seed)
  let h1 ← shake256.Sponge.absorb h s4
  let s5 ← lift (Array.to_slice pk_root)
  let h2 ← shake256.Sponge.absorb h1 s5
  let s6 ← lift (Array.to_slice (Array.make 2#usize [ 0#u8, i1 ]))
  let h3 ← shake256.Sponge.absorb h2 s6
  let h4 ← shake256.Sponge.absorb h3 ctx
  let h5 ← shake256.Sponge.absorb h4 m
  let d ← alloc.vec.from_elem core.clone.CloneU8 0#u8 p.m
  let (s7, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut d)
  let s8 ← shake256.Sponge.finish h5 s7
  let d1 := deref_mut_back s8
  ok (r, d1)

def cache.TopTreeCache.assert_compatible
  {N : Std.Usize} (self : cache.TopTreeCache N) (p : params.Params)
  (sk : Slice Std.U8) :
  Result Unit
  := do
  if N = p.n
  then
    if self.hp = p.hp
    then
      if self.d = p.d
      then let b ← cache.TopTreeCache.matches_key self sk
           massert b
      else
        let _ ←
          core.fmt.Arguments.from_str (toStr
            "TopTreeCache: parameter set d mismatch")
        fail panic
    else
      let _ ←
        core.fmt.Arguments.from_str (toStr
          "TopTreeCache: parameter set h\' mismatch")
      fail panic
  else
    let _ ←
      core.fmt.Arguments.from_str (toStr "TopTreeCache: N must match p.n")
    fail panic

def cache.TopTreeCache.lookup_digest_layer
  {N : Std.Usize} (self : cache.TopTreeCache N) (p : params.Params)
  (digest : Slice Std.U8) :
  Result (Option (Slice (Array Std.U8 N)))
  := do
  let b ← alloc.vec.Vec.is_empty self.layer_d2
  if b
  then ok none
  else
    let i ← cache.TopTreeCache.layer_d2_tree_index N p digest
    cache.TopTreeCache.lookup_d2 self i

def cache.TopTreeCache.sign
  {N : Std.Usize} (self : cache.TopTreeCache N) (p : params.Params)
  (m : Slice Std.U8) (ctx : Slice Std.U8) (sk : Slice Std.U8)
  (addrnd : Array Std.U8 N) :
  Result (Option (alloc.vec.Vec Std.U8))
  := do
  let i := Slice.len ctx
  if i > 255#usize
  then ok none
  else
    cache.TopTreeCache.assert_compatible self p sk
    let sk_seed ← util.block N sk 0#usize
    let sk_prf ← util.block N sk 1#usize
    let pk_seed ← util.block N sk 2#usize
    let pk_root ← util.block N sk 3#usize
    let (hf, (r, digest)) ←
      match self.family with
      | cache.HashFamily.Sha2 =>
        do
        let p1 ←
          cache.sha2_ops.pure_digest p sk_prf pk_seed pk_root addrnd ctx m
        ok (cache.HashFamily.Sha2, p1)
      | cache.HashFamily.Shake =>
        do
        let p1 ←
          cache.shake_ops.pure_digest p sk_prf pk_seed pk_root addrnd ctx m
        ok (cache.HashFamily.Shake, p1)
    let s := alloc.vec.Vec.deref digest
    let d2_hit ←
      cache.TopTreeCache.lookup_digest_layer { self with family := hf } p s
    match hf with
    | cache.HashFamily.Sha2 =>
      let s1 := alloc.vec.Vec.deref digest
      let s2 := alloc.vec.Vec.deref self.top_tree
      let sig ←
        cache.sha2_ops.sign_from_digest p sk_seed pk_seed r s1 s2 d2_hit
      ok (some sig)
    | cache.HashFamily.Shake =>
      let s1 := alloc.vec.Vec.deref digest
      let s2 := alloc.vec.Vec.deref self.top_tree
      let sig ←
        cache.shake_ops.sign_from_digest p sk_seed pk_seed r s1 s2 d2_hit
      ok (some sig)

def cache.TopTreeCache.sign_deterministic
  {N : Std.Usize} (self : cache.TopTreeCache N) (p : params.Params)
  (m : Slice Std.U8) (ctx : Slice Std.U8) (sk : Slice Std.U8) :
  Result (Option (alloc.vec.Vec Std.U8))
  := do
  let i := Slice.len ctx
  if i > 255#usize
  then ok none
  else
    let pk_seed ← util.block N sk 2#usize
    cache.TopTreeCache.sign self p m ctx sk pk_seed

def cache.sign_cached
  {N : Std.Usize} (p : params.Params) (m : Slice Std.U8) (ctx : Slice Std.U8)
  (sk : Slice Std.U8) (addrnd : Array Std.U8 N) (cache : cache.TopTreeCache N)
  :
  Result (Option (alloc.vec.Vec Std.U8))
  := do
  CacheopsRust.Public.cache.TopTreeCache.sign cache p m ctx sk addrnd

def cache.sign_deterministic_cached
  {N : Std.Usize} (p : params.Params) (m : Slice Std.U8) (ctx : Slice Std.U8)
  (sk : Slice Std.U8) (cache : cache.TopTreeCache N) :
  Result (Option (alloc.vec.Vec Std.U8))
  := do
  CacheopsRust.Public.cache.TopTreeCache.sign_deterministic cache p m ctx sk

end CacheopsRust.Public
