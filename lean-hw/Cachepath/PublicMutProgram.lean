import Cachepath.Public
import Cachepath.Mutation
open Aeneas Aeneas.Std Result ControlFlow Error
namespace CacheopsRust.Public
variable [backend : Closed.Backend]

/-! The Rust cache policy uses a backend-specific tree constructor on a cache miss. -/
class Builders (N : Usize) where
  sha2 : CacheopsRust.cache.mutation.Builder N
  shake : CacheopsRust.cache.mutation.Builder N

abbrev cache.TopTreeCache.lookup_or_populate_d2 {N : Usize} [b : Builders N] :=
  @CacheopsRust.cache.TopTreeCache.lookup_or_populate_d2 N b.sha2 b.shake

def cache.TopTreeCache.sign_mut
  {N : Std.Usize} [Builders N] (self : cache.TopTreeCache N) (p : params.Params)
  (m : Slice Std.U8) (ctx : Slice Std.U8) (sk : Slice Std.U8)
  (addrnd : Array Std.U8 N) :
  Result ((Option (alloc.vec.Vec Std.U8)) × (CacheopsRust.cache.TopTreeCache N))
  := do
  let i := Slice.len ctx
  if i > 255#usize
  then ok (none, self)
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
    let tree_d2 ← cache.TopTreeCache.layer_d2_tree_index N p s
    let (o, self1) ←
      cache.TopTreeCache.lookup_or_populate_d2 { self with family := hf } p
        sk_seed pk_seed tree_d2
    let has_d2 := core.option.Option.is_some o
    let d2_hit ←
      if has_d2
      then cache.TopTreeCache.lookup_d2 self1 tree_d2
      else ok none
    match self1.family with
    | cache.HashFamily.Sha2 =>
      let s1 := alloc.vec.Vec.deref digest
      let s2 := alloc.vec.Vec.deref self1.top_tree
      let sig ←
        cache.sha2_ops.sign_from_digest p sk_seed pk_seed r s1 s2 d2_hit
      ok (some sig, self1)
    | cache.HashFamily.Shake =>
      let s1 := alloc.vec.Vec.deref digest
      let s2 := alloc.vec.Vec.deref self1.top_tree
      let sig ←
        cache.shake_ops.sign_from_digest p sk_seed pk_seed r s1 s2 d2_hit
      ok (some sig, self1)

def cache.TopTreeCache.sign_deterministic_mut
  {N : Std.Usize} [Builders N] (self : cache.TopTreeCache N) (p : params.Params)
  (m : Slice Std.U8) (ctx : Slice Std.U8) (sk : Slice Std.U8) :
  Result ((Option (alloc.vec.Vec Std.U8)) × (CacheopsRust.cache.TopTreeCache N))
  := do
  let i := Slice.len ctx
  if i > 255#usize
  then ok (none, self)
  else
    let pk_seed ← util.block N sk 2#usize
    cache.TopTreeCache.sign_mut self p m ctx sk pk_seed

def cache.sign_cached_mut
  {N : Std.Usize} [Builders N] (p : params.Params) (m : Slice Std.U8) (ctx : Slice Std.U8)
  (sk : Slice Std.U8) (addrnd : Array Std.U8 N) (cache : cache.TopTreeCache N)
  :
  Result ((Option (alloc.vec.Vec Std.U8)) × (CacheopsRust.cache.TopTreeCache N))
  := do
  CacheopsRust.Public.cache.TopTreeCache.sign_mut cache p m ctx sk addrnd

def cache.sign_deterministic_cached_mut
  {N : Std.Usize} [Builders N] (p : params.Params) (m : Slice Std.U8) (ctx : Slice Std.U8)
  (sk : Slice Std.U8) (cache : cache.TopTreeCache N) :
  Result ((Option (alloc.vec.Vec Std.U8)) × (CacheopsRust.cache.TopTreeCache N))
  := do
  CacheopsRust.Public.cache.TopTreeCache.sign_deterministic_mut cache p m ctx sk

end CacheopsRust.Public
