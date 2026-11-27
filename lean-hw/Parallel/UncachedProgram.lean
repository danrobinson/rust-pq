import Armwide.Signature
import Slhdsa.Proofs.ShakeSlh
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelCaller
noncomputable section

class Worker (S : Usize → Type) where
  run {N : Usize} (p : params.Params) (md : Slice U8) (sk : Array U8 N) (seed : S N)
    (a : address.Adrs) (r : Array U8 N) (tree : U64) (leaf : U32) : Result (Option (alloc.vec.Vec U8))

abbrev ShakeSeed (N : Usize) := Array U8 N

namespace Sh
class Fallback where
  forsSign {N : Usize} : params.Params → Slice U8 → Array U8 N → Array U8 N → address.Adrs → Result (alloc.vec.Vec U8)
  forsRecover {N : Usize} : params.Params → Slice U8 → Slice U8 → Array U8 N → address.Adrs → Result (Array U8 N)
  htSign {N : Usize} : params.Params → Array U8 N → Array U8 N → Array U8 N → U64 → U32 → Result (alloc.vec.Vec U8)

def scalar : Fallback := ⟨@slhdsa.shake.fors.fors_sign,@slhdsa.shake.fors.fors_pk_from_sig,@slhdsa.shake.ht.ht_sign⟩

variable [fallback : Fallback] [worker : Worker ShakeSeed]
abbrev shake.fors.fors_sign {N : Usize} := @fallback.forsSign N
abbrev shake.fors.fors_pk_from_sig {N : Usize} := @fallback.forsRecover N
abbrev shake.ht.ht_sign {N : Usize} := @fallback.htSign N
abbrev shake.slh.parallel.sign {N : Usize} := @worker.run N

/-- The sign_digest! continuation is shared by contiguous and segmented message hashing. -/
def signWith {N : Std.Usize}
  (prf : Array U8 N → Array U8 N → Slice U8 → Result (Array U8 N))
  (hash : params.Params → Array U8 N → Array U8 N → Array U8 N → Slice U8 → Result (alloc.vec.Vec U8))
  (p : params.Params) (m : Slice Std.U8) (sk : Slice Std.U8)
  (addrnd : Array Std.U8 N) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let sk_seed ← util.block N sk 0#usize
  let sk_prf ← util.block N sk 1#usize
  let pk_seed ← util.block N sk 2#usize
  let pk_root ← util.block N sk 3#usize
  let r ← prf sk_prf addrnd m
  let digest ← hash p r pk_seed pk_root m
  let s := alloc.vec.Vec.deref digest
  let idx_tree ← shake.slh.digest_tree p s
  let s1 := alloc.vec.Vec.deref digest
  let idx_leaf ← shake.slh.digest_leaf p s1
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_tree a idx_tree
  let a2 ← address.Adrs.with_type a1 address.FORS_TREE
  let adrs ← address.Adrs.with_keypair a2 idx_leaf
  let seed ← shake.hash.seed_ctx pk_seed
  let i ← params.Params.md_bytes p
  let md ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
      digest { start := 0#usize, «end» := i }
  let o ← shake.slh.parallel.sign p md sk_seed seed adrs r idx_tree idx_leaf
  match o with
  | none =>
    let sig_fors ← shake.fors.fors_sign p md sk_seed seed adrs
    let s2 := alloc.vec.Vec.deref sig_fors
    let pk_fors ← shake.fors.fors_pk_from_sig p s2 md seed adrs
    let sig_ht ← shake.ht.ht_sign p pk_fors sk_seed seed idx_tree idx_leaf
    let s3 ← lift (Array.to_slice r)
    let sig ←
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.new
        Std.U8) s3
    let s4 := alloc.vec.Vec.deref sig_fors
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s4
    let s5 := alloc.vec.Vec.deref sig_ht
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig1 s5
  | some sig => ok sig
def shake.slh.slh_sign_internal {N : Usize} :=
  @signWith fallback worker N shake.hash.prf_msg shake.hash.h_msg

end Sh

namespace S2
variable [worker : Worker hash.Seed] [cpu : Armwide.Public.Dispatcher.Cpu] [features : Armwide.Keygen.Features]
abbrev slh.parallel.sign {N : Usize} := @worker.run N
abbrev hash.prf_msg {N : Usize} := @NativeArmSignature.hash.prf_msg N
abbrev hash.h_msg {N : Usize} := @NativeArmSignature.hash.h_msg N
abbrev fors.fors_sign {N : Usize} := @NativeArmSignature.fors.fors_sign cpu features N
abbrev fors.fors_pk_from_sig {N : Usize} := @NativeArmSignature.fors.fors_pk_from_sig cpu features N
abbrev ht.ht_sign {N : Usize} := @NativeArmSignature.ht.ht_sign cpu features N

def slh.slh_sign_internal
  {N : Std.Usize} (p : params.Params) (m : Slice Std.U8) (sk : Slice Std.U8)
  (addrnd : Array Std.U8 N) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let sk_seed ← util.block N sk 0#usize
  let sk_prf ← util.block N sk 1#usize
  let pk_seed ← util.block N sk 2#usize
  let pk_root ← util.block N sk 3#usize
  let r ← hash.prf_msg sk_prf addrnd m
  let digest ← hash.h_msg p r pk_seed pk_root m
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
  let o ← slh.parallel.sign p md sk_seed seed adrs r idx_tree idx_leaf
  match o with
  | none =>
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
  | some sig => ok sig
end S2
end
end slhdsa.ParallelCaller
