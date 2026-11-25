import Armwide.RecoveryPublic
import Armwide.DispatchProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.Recovery.Dispatcher
open slhdsa.Armwide.Public.Dispatcher (Cpu)
abbrev sha256.arm_wide.available [Cpu] := Public.Dispatcher.sha256.arm_wide.available
abbrev wots.wots_pk_from_sig_loop0 := @slhdsa.wots.wots_pk_from_sig_loop
abbrev wots.wots_pk_from_sig_loop1 := @slhdsa.wots.wots_pk_from_sig_loop
section
variable [Cpu] [Keygen.Features]
def wots.wots_pk_from_sig
  {N : Std.Usize} (sig : Slice Std.U8) (m : Array Std.U8 N)
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
    then wots.arm.recover sig m seed adrs
    else
      let i ← 2#usize * N
      let len ← i + params.LEN2
      let msg ← wots.wots_digits m
      let a := Array.repeat 64#usize 0#u8
      let blocks := Array.repeat 67#usize a
      let blocks1 ← wots.wots_pk_from_sig_loop0 N sig adrs len blocks 0#usize
      let (s, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
          blocks1 { start := 0#usize, «end» := len }
      let s1 := alloc.vec.Vec.deref msg
      let _ ← params.W - 1#u32
      let i1 ← lift (Std.U32.wrapping_sub params.W 1#u32)
      let a1 := Array.repeat 67#usize i1
      let s2 ← lift (Array.to_slice a1)
      let s3 ← hash.chain_blocks N seed.state s s1 s2
      let a2 ← address.Adrs.with_type adrs address.WOTS_PK
      let pk_adrs ← address.Adrs.with_keypair a2 adrs.keypair
      let blocks2 := index_mut_back s3
      let s4 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
          blocks2 { start := 0#usize, «end» := len }
      hash.thash_values seed pk_adrs s4
  else
    let i ← 2#usize * N
    let len ← i + params.LEN2
    let msg ← wots.wots_digits m
    let a := Array.repeat 64#usize 0#u8
    let blocks := Array.repeat 67#usize a
    let blocks1 ← wots.wots_pk_from_sig_loop1 N sig adrs len blocks 0#usize
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
        blocks1 { start := 0#usize, «end» := len }
    let s1 := alloc.vec.Vec.deref msg
    let _ ← params.W - 1#u32
    let i1 ← lift (Std.U32.wrapping_sub params.W 1#u32)
    let a1 := Array.repeat 67#usize i1
    let s2 ← lift (Array.to_slice a1)
    let s3 ← hash.chain_blocks N seed.state s s1 s2
    let a2 ← address.Adrs.with_type adrs address.WOTS_PK
    let pk_adrs ← address.Adrs.with_keypair a2 adrs.keypair
    let blocks2 := index_mut_back s3
    let s4 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U8 64#usize)))
        blocks2 { start := 0#usize, «end» := len }
    hash.thash_values seed pk_adrs s4

end

theorem dispatch_eq_scalar [cpu : Cpu] [Keygen.Features] {N : Usize} (p : params.Params) (hp : PN p N)
    (sig : Slice U8) (m : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (fits : N.val*(2*N.val+3)≤sig.length) :
    wots.wots_pk_from_sig sig m seed a = slhdsa.wots.wots_pk_from_sig sig m seed a := by
  unfold wots.wots_pk_from_sig
  rcases hp.nok with h|h|h <;> simp only [h,bind_ok,ite_true,sha256.arm_wide.available,
    Public.Dispatcher.sha256.arm_wide.available] <;> cases cpu.wide
  all_goals first | rfl | exact recover_eq_scalar p hp sig m seed hs a fits

#print axioms dispatch_eq_scalar
end slhdsa.Armwide.Recovery.Dispatcher
