import Segmentedapi.Funs
import Slhdsa.Proofs.Slh
open Aeneas Aeneas.Std Result
open slhdsa
namespace slhdsa.SegmentedApi.Program

abbrev slh.message.randomizer := @SegmentedApiRust.slh.message.randomizer
abbrev slh.message.digest := @SegmentedApiRust.slh.message.digest

def slh.message.sign
  {N : Std.Usize} (p : params.Params) (m : Slice Std.U8) (ctx : Slice Std.U8)
  (sk : Slice Std.U8) (addrnd : Array Std.U8 N) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let sk_seed ← util.block N sk 0#usize
  let sk_prf ← util.block N sk 1#usize
  let pk_seed ← util.block N sk 2#usize
  let pk_root ← util.block N sk 3#usize
  let r ← slh.message.randomizer sk_prf addrnd ctx m
  let digest ← slh.message.digest p r pk_seed pk_root ctx m
  let s := alloc.vec.Vec.deref digest
  let idx_tree ← slh.digest_tree p s
  let s1 := alloc.vec.Vec.deref digest
  let idx_leaf ← slh.digest_leaf p s1
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_tree a idx_tree
  let a2 ← address.Adrs.with_type a1 address.FORS_TREE
  let adrs ← address.Adrs.with_keypair a2 idx_leaf
  let seed ← hash.seed_ctx pk_seed
  let i ← params.Params.md_bytes p
  let md ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
      digest { start := 0#usize, «end» := i }
  let sig_fors ← fors.fors_sign p md sk_seed seed adrs
  let s2 := alloc.vec.Vec.deref sig_fors
  let pk_fors ← fors.fors_pk_from_sig p s2 md seed adrs
  let sig_ht ← ht.ht_sign p pk_fors sk_seed seed idx_tree idx_leaf
  let s3 ← lift (Array.to_slice r)
  let sig ←
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.new
      Std.U8) s3
  let s4 := alloc.vec.Vec.deref sig_fors
  let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s4
  let s5 := alloc.vec.Vec.deref sig_ht
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig1 s5

/-- [slhdsa::slh::message::verify]:
    Source: 'src/slh/message.rs', lines 145:0-162:1 -/
def slh.message.verify
  (N : Std.Usize) (p : params.Params) (m : Slice Std.U8) (ctx : Slice Std.U8)
  (sig : Slice Std.U8) (pk : Slice Std.U8) :
  Result Bool
  := do
  let sig_bytes ← params.Params.sig_bytes p
  let i := Slice.len sig
  if i != sig_bytes
  then ok false
  else
    let i1 ← params.Params.fors_sig_bytes p
    let fors_end ← N + i1
    let pk_seed ← util.block N pk 0#usize
    let pk_root ← util.block N pk 1#usize
    let r ← util.block N sig 0#usize
    let digest ← slh.message.digest p r pk_seed pk_root ctx m
    let s := alloc.vec.Vec.deref digest
    let idx_tree ← slh.digest_tree p s
    let s1 := alloc.vec.Vec.deref digest
    let idx_leaf ← slh.digest_leaf p s1
    let a ← address.Adrs.new
    let a1 ← address.Adrs.with_tree a idx_tree
    let a2 ← address.Adrs.with_type a1 address.FORS_TREE
    let adrs ← address.Adrs.with_keypair a2 idx_leaf
    let seed ← hash.seed_ctx pk_seed
    let s2 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := N, «end» := fors_end }
    let i2 ← params.Params.md_bytes p
    let s3 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
        digest { start := 0#usize, «end» := i2 }
    let pk_fors ← fors.fors_pk_from_sig p s2 s3 seed adrs
    let s4 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) sig { start := fors_end, «end» := sig_bytes }
    ht.ht_verify p pk_fors s4 seed idx_tree idx_leaf pk_root

/-- [slhdsa::slh::slh_sign]:
    Source: 'src/slh.rs', lines 123:0-135:1
    Visibility: public -/
def slh.slh_sign
  {N : Std.Usize} (p : params.Params) (m : Slice Std.U8) (ctx : Slice Std.U8)
  (sk : Slice Std.U8) (addrnd : Array Std.U8 N) :
  Result (Option (alloc.vec.Vec Std.U8))
  := do
  let i := Slice.len ctx
  if i > 255#usize
  then ok none
  else
    let i1 := Slice.len m
    if i1 >= 1024#usize
    then let v ← slh.message.sign p m ctx sk addrnd
         ok (some v)
    else
      let mp ← slh.with_context m ctx
      let s := alloc.vec.Vec.deref mp
      let v ← slh.slh_sign_internal p s sk addrnd
      ok (some v)

/-- [slhdsa::slh::slh_verify]:
    Source: 'src/slh.rs', lines 138:0-150:1
    Visibility: public -/
def slh.slh_verify
  (N : Std.Usize) (p : params.Params) (m : Slice Std.U8) (sig : Slice Std.U8)
  (ctx : Slice Std.U8) (pk : Slice Std.U8) :
  Result Bool
  := do
  let i := Slice.len ctx
  if i > 255#usize
  then ok false
  else
    let i1 := Slice.len m
    if i1 >= 1024#usize
    then slh.message.verify N p m ctx sig pk
    else
      let mp ← slh.with_context m ctx
      let s := alloc.vec.Vec.deref mp
      slh.slh_verify_internal N p s sig pk

end slhdsa.SegmentedApi.Program

namespace slhdsa.SegmentedApi
open Program

theorem message_sign_eq {N : Usize} (p : params.Params) (m ctx mp sk : Slice U8) (rnd : Array U8 N)
    (prf : ∀ key, SegmentedApiRust.slh.message.randomizer key rnd ctx m = hash.prf_msg key rnd mp)
    (digest : ∀ (r pk root : Array U8 N),
      SegmentedApiRust.slh.message.digest p r pk root ctx m = hash.h_msg p r pk root mp) :
    Program.slh.message.sign p m ctx sk rnd = slh.slh_sign_internal p mp sk rnd := by
  simp only [Program.slh.message.sign,slh.slh_sign_internal,Program.slh.message.randomizer,
    Program.slh.message.digest,prf,digest]

theorem message_verify_eq {N : Usize} (p : params.Params) (m ctx mp sig pk : Slice U8)
    (digest : ∀ (r ps root : Array U8 N),
      SegmentedApiRust.slh.message.digest p r ps root ctx m = hash.h_msg p r ps root mp) :
    Program.slh.message.verify N p m ctx sig pk = slh.slh_verify_internal N p mp sig pk := by
  simp only [Program.slh.message.verify,slh.slh_verify_internal,Program.slh.message.digest,digest]

end slhdsa.SegmentedApi
